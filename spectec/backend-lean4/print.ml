open Il.Ast
open Util.Source

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

let iter_prem_rels_list = ["Forall"; "Forall₂"; "Forall₃"]
let iter_exp_lst_funcs = ["List.map"; "List.zipWith"; "list_map3"]
let iter_exp_opt_funcs = ["Option.map"; "option_zipWith"; "option_map3"]
let error at msg = Util.Error.error at "Lean4 translation" msg 

(* List of declaration ids that are hand-coded in the preamble *)
let builtins = [ "disjoint_"; "setminus1_"; "setminus_" ]

let rec list_split (f : 'a -> bool) = function 
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

type exptype =
  | LHS
  | RHS
  | REL

let var_prefix = "var_"

let remove_iter_from_type t =
  match t.it with
  | IterT (t', _) -> t'
  | _ -> t
let empty_name s = match s with
  | "" -> "NO_NAME"
  | _ -> s

let is_typ_bind b = match b.it with
  | TypB _ -> true
  | _ -> false

let string_of_list_prefix prefix delim str_func ls = 
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls)

let string_of_list_suffix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> String.concat delim (List.map str_func ls) ^ suffix

let string_of_list prefix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls) ^ suffix

let square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"
let comment_parens s = "/- " ^ s ^ " -/"

let family_type_suffix = "entry"

let env_ref = ref Il.Env.empty

(* ElseSimp removes the auxiliary relations introduced for `otherwise`, but
   deliberately leaves their hints in the script.  Keep just enough of that
   metadata to reconstruct the quantifier structure when printing rules. *)
let otherwise_rules_ref = ref StringSet.empty
let wf_relations_ref = ref StringSet.empty

let otherwise_key relation_id rule_id = relation_id ^ "\000" ^ rule_id

let improved_user_id id =
  let id' =
    String.map (function '.' | '-' -> '_' | c -> c) id
    |> Str.global_replace (Str.regexp {|\(*\)|}) "_lst"
    |> Util.Lib.String.replace "?" "_opt"
  in
  match int_of_string_opt id' with
  | Some _ -> "r_" ^ id'
  | None -> id'

let remove_prefix prefix value =
  let prefix_length = String.length prefix in
  if String.length value >= prefix_length &&
     String.sub value 0 prefix_length = prefix
  then Some (String.sub value prefix_length (String.length value - prefix_length))
  else None

let register_backend_hints defs =
  otherwise_rules_ref := StringSet.empty;
  wf_relations_ref := StringSet.empty;
  let rec register def =
    match def.it with
    | HintD {it = RelH (id, hints); _} ->
      List.iter (fun hint ->
        match hint.hintid.it, hint.hintexp.it with
        | "else-relation", El.Ast.TextE base_relation ->
          let prefix = base_relation ^ "_before_" in
          begin match remove_prefix prefix id.it with
          | Some rule_id ->
            otherwise_rules_ref := StringSet.add
              (otherwise_key (improved_user_id base_relation)
                (improved_user_id rule_id))
              !otherwise_rules_ref
          | None -> ()
          end
        | "wf-relation", _ ->
          wf_relations_ref := StringSet.add (improved_user_id id.it) !wf_relations_ref
        | _ -> ()
      ) hints
    | RecD nested -> List.iter register nested
    | _ -> ()
  in
  List.iter register defs

let is_record_typ inst = 
  match inst.it with
  | InstD (_, _, {it = StructT _; _}) -> true
  | _ -> false

let is_variant_typ inst = 
  match inst.it with
  | InstD (_, _, {it = VariantT _; _}) -> true
  | _ -> false

let is_alias_typ inst = 
  match inst.it with
  | InstD (_, _, {it = AliasT _; _}) -> true
  | _ -> false

let is_alias_typ_def def = 
  match def.it with
  | TypD(_ , _, [{it = InstD (_, _, {it = AliasT _; _}); _}]) -> true
  | _ -> false

let rec is_composable_type seen env typ =
  match typ.it with
  | IterT _ -> true
  | VarT (id, _) when StringSet.mem id.it seen -> false
  | VarT (id, _) ->
    let seen' = StringSet.add id.it seen in
    begin match Il.Env.find_opt_typ env id with
    | Some (_, [{it = InstD (_, _, {it = AliasT inner; _}); _}]) ->
      is_composable_type seen' env inner
    | Some (_, [{it = InstD (_, _, {it = StructT fields; _}); _}]) ->
      List.for_all (fun (_, (_, field_typ, _), _) ->
        is_composable_type seen' env field_typ) fields
    | _ -> false
    end
  | _ -> false

let is_inductive d = 
  match d.it with
  | RelD _ -> true
  | TypD(_, _, [inst]) when is_variant_typ inst || is_alias_typ inst -> true
  | _ -> false
    
let comment_desc_def d = 
  match d.it with
  | TypD (_, _, [inst]) when is_alias_typ inst -> "Type Alias Definition"
  | TypD (_, _, [inst]) when is_variant_typ inst -> "Inductive Type Definition"
  | TypD (_, _, [inst]) when is_record_typ inst -> "Record Creation Definition"
  | TypD _ -> "Type Family Definition"
  | RecD [_] -> "Recursive Definition"
  | RecD _ -> "Recursive Definitions"
  | DecD (_, _, _, []) -> "Axiom Definition"
  | DecD _ -> "Auxiliary Definition"
  | RelD _ -> "Inductive Relations Definition"
  | HintD _ -> "Hint Definition"
  | GramD _ -> "Grammar Production Definition"

let render_unop unop = 
  match unop with
  | `NotOp   -> "!"
  | `PlusOp  -> ""
  | `MinusOp -> "0 - "
let render_binop binop = 
  match binop with
  | `AndOp   -> " && " 
  | `OrOp    -> " || "
  | `ImplOp  -> " -> "
  | `EquivOp -> " <-> "
  | `AddOp   -> " + " 
  | `SubOp   -> " - " 
  | `MulOp   -> " * " 
  | `DivOp   -> " / "
  | `ModOp   -> " % "
  | `PowOp   -> " ^ " 

let render_cmpop cmpop =
  match cmpop with
  | `EqOp -> " == "
  | `NeOp -> " != "
  | `LtOp -> " < "
  | `GtOp -> " > "
  | `LeOp -> " <= "
  | `GeOp -> " >= "

let is_atomid a =
  match a.it with
  | Xl.Atom.Atom _ -> true
  | _ -> false 

let render_atom a =
  match a.it with
  | Xl.Atom.Atom a -> a
  | _ -> ""

  let render_id a = match a with
  | "rec" -> "rec_"
  | "bool" -> "nat_of_bool"
  | "mut" | "local" | "export" | "import" | "catch" | "syntax" | "at"
    -> "«" ^ a ^ "»"
  | _ -> a

let render_mixop (m : mixop) = 
  (match m with
    | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
    | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.filter is_atomid atoms |> List.map render_atom)) mixop
    )
  )

let get_bind_id b = 
  match b.it with
  | ExpB (id, _) | TypB id | DefB (id, _, _) | GramB (id, _, _) -> id.it

let get_param_id b = 
  match b.it with
  | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _) -> id.it

let render_numtyp nt = 
  match nt with
  | `NatT -> "Nat"
  | `IntT -> "Int"
  | `RatT -> "Rat"
  | `RealT -> error no_region "Mathematical real numbers are not yet supported by the Lean4 backend"

let render_num num =
  match num with
  | `Nat n | `Int n -> Z.to_string n
  | `Rat q -> parens (parens (Q.to_string q) ^ " : Rat")
  | `Real _ -> error no_region "Mathematical real literals are not yet supported by the Lean4 backend"

let render_conversion r_func e nt1 nt2 =
  let rendered = r_func e in
  match nt1, nt2 with
  | nt1, nt2 when nt1 = nt2 -> rendered
  | `NatT, `IntT -> parens ("Int.ofNat " ^ rendered)
  | `IntT, `NatT -> parens ("Int.toNat " ^ rendered)
  | (`NatT | `IntT), `RatT -> parens (rendered ^ " : Rat")
  | `RatT, `IntT -> parens ("Rat.floor " ^ rendered)
  | `RatT, `NatT -> parens ("Int.toNat (Rat.floor " ^ rendered ^ ")")
  | (`RealT, _) | (_, `RealT) ->
    error e.at "Conversions involving mathematical real numbers are not yet supported by the Lean4 backend"
  | _ ->
    error e.at ("Unsupported numeric conversion from " ^ Xl.Num.string_of_typ nt1 ^
      " to " ^ Xl.Num.string_of_typ nt2)

let transform_case_tup e = 
  match e.it with
  | TupE exps -> exps
  | _ -> [e]

let transform_case_typ t =
  match t.it with
  | TupT typs -> List.map snd typs
  | _ -> [t]

let transform_case_args t =
  match t.it with
  | TupT typs -> typs
  | _ -> [(VarE ("_" $ t.at) $$ t.at % t, t)]

let get_type_args t = 
  match t.it with
  | VarT (_, args) -> args
  | _ -> error t.at ("Following type should be a variable type: " ^ Il.Print.string_of_typ t)

let rec render_param_type exp_type param = 
  match param.it with
  | ExpP (_, typ) -> render_type exp_type typ
  | TypP _ -> "Type"
  | DefP (_, params, typ) -> 
    string_of_list_suffix " -> " " -> " (render_param_type exp_type) params ^ render_type exp_type typ
  | GramP _ -> comment_parens ("Unsupported param: " ^ Il.Print.string_of_param param)

and render_type exp_type typ = 
  let rt_func = render_type exp_type in
  match typ.it with
  | VarT (id, []) -> render_id id.it
  | VarT (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type) args))
  | BoolT -> "Bool"
  | NumT nt -> render_numtyp nt
  | TextT -> "String"
  | TupT [] -> "Unit"
  | TupT typs -> String.concat " × " (List.map (fun (_, t) -> rt_func t) typs)
  | IterT (t, Opt) -> parens ("Option " ^ rt_func t)
  | IterT (t, _) -> parens ("List " ^ rt_func t)

and render_exp exp_type exp =
  let r_func = render_exp exp_type in
  match exp.it with 
  | VarE id -> render_id id.it
  | BoolE b -> string_of_bool b
  | NumE num -> render_num num
  | TextE s -> "\"" ^ String.escaped s ^ "\""
  | UnE (unop, _, e1) -> parens (render_unop unop ^ r_func e1)
  | BinE (binop, _, e1, e2) -> parens (r_func e1 ^ render_binop binop ^ r_func e2)
  | CmpE (cmpop, _, e1, e2) -> parens (r_func e1 ^ render_cmpop cmpop ^ r_func e2)
  | TupE [] -> "()"
  | TupE exps -> parens (String.concat ", " (List.map r_func exps))
  | ProjE (e, i) -> 
    let typs = transform_case_typ e.note in 
    let rec make_proj_chain idx len e = 
      match idx, len with
      | 0, 0 -> r_func e
      | i, n when i <= n -> parens ("snd " ^ r_func e)
      | _ -> parens ("fst " ^ (make_proj_chain idx (len - 1) e))
    in
    begin match typs with
    | [_] -> r_func e
    | _ -> make_proj_chain i (List.length typs - 1) e 
    end
  | CaseE (m, e) when exp_type = LHS -> 
    let exps = transform_case_tup e in
    begin match exps with
    | [] -> "." ^ render_mixop m
    | _ -> parens ("." ^ render_mixop m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | CaseE (m, e) -> 
    let exps = transform_case_tup e in
    begin match exps with
    | [] -> "." ^ render_mixop m
    | _ -> parens ("." ^ render_mixop m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | UncaseE _ -> error exp.at "Encountered uncase. Run uncase-removal pass"
  | OptE (Some e) -> parens ("some " ^ r_func e)
  | OptE None -> "none"
  | TheE e -> parens ("Option.get! " ^ r_func e)
  | StrE fields -> "{ " ^ (String.concat ", " (List.map (fun (a, e) -> render_atom a ^ " := " ^ r_func e) fields)) ^ " }"
  | DotE (e, a) -> parens (r_func e ^ "." ^ render_atom a)
  | CompE (e1, e2) -> parens (r_func e1 ^ " ++ " ^ r_func e2)
  | ListE [] -> "[]"
  | ListE exps -> square_parens (String.concat ", " (List.map r_func exps)) 
  | LiftE e -> parens ("Option.toList " ^ r_func e)
  (* | MemE (e1, e2) -> parens (r_func e1 ^ " ∈ " ^ r_func e2) *)
  | MemE (e1, e2) -> parens ("List.contains" ^ " " ^ r_func e2 ^ " " ^ r_func e1)
  | LenE e1 -> parens ("List.length " ^ r_func e1)
  | CatE ({it = ListE [e1]; _}, e2) when exp_type = LHS -> parens (r_func e1 ^ " :: " ^ r_func e2) 
  | CatE (e1, e2) -> parens (r_func e1 ^ " ++ " ^ r_func e2)
  | IdxE (e1, e2) -> parens (r_func e1 ^ "[" ^ r_func e2 ^ "]!")
  | SliceE (e1, e2, e3) -> parens ("List.extract " ^ r_func e1 ^ " " ^ r_func e2 ^ " " ^ r_func e3)
  | UpdE (e1, p, e2) -> render_path_start p e1 false e2
  | ExtE (e1, p, e2) -> render_path_start p e1 true e2
  | CallE (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type) args))
  (* Iter handling *)
  | IterE (e, (ListN (n, _), [])) -> parens ("List.replicate " ^ (r_func n) ^ " " ^ (r_func e)) 
  | IterE (e, (_, [])) -> r_func e
  | IterE (e, _) when exp_type = LHS -> r_func e
  | IterE (e, (iter, iter_binds)) ->
    let binds = List.map (fun (id, e) -> parens (id.it ^ " : " ^ render_type exp_type (remove_iter_from_type e.note))) iter_binds in
    let iter_exps = List.map snd iter_binds in 
    let n = List.length iter_binds - 1 in
    let lst = if iter = Opt then iter_exp_opt_funcs else iter_exp_lst_funcs in
    let pred_name = match (List.nth_opt lst n) with 
    | Some s -> s
    | None -> error exp.at "Iteration exceeded the supported amount for rocq translation"
    in 
    parens (pred_name ^ " " ^ render_lambda binds (r_func e) ^ " " ^ 
    String.concat " " (List.map (render_exp exp_type) iter_exps))
  | CvtE (e1, nt1, nt2) -> render_conversion r_func e1 nt1 nt2
  | SubE _ -> error exp.at "Encountered subtype expression. Please run sub pass"
  | IfE (cond, then_exp, else_exp) -> 
    parens ("if " ^ r_func cond ^ " then " ^ r_func then_exp ^ " else " ^ r_func else_exp)

and render_arg exp_type a = 
  match a.it with 
  | ExpA e -> render_exp exp_type e
  | TypA t -> render_type exp_type t
  | DefA id -> render_id id.it 
  | _ -> comment_parens ("Unsupported arg: " ^ Il.Print.string_of_arg a)

and render_bind exp_type b =
  match b.it with
  | ExpB (id, typ) -> parens (render_id id.it ^ " : " ^ render_type exp_type typ)
  | TypB id -> parens (render_id id.it ^ " : Type 0")
  | DefB (id, params, typ) -> 
    parens (render_id id.it ^ " : " ^ 
    string_of_list_suffix " -> " " -> " (render_param_type exp_type) params ^
    render_type exp_type typ)
  | GramB _ -> comment_parens ("Unsupported bind: " ^ Il.Print.string_of_bind b)

and render_param exp_type param = 
  let get_id p =
    match p.it with
    | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _) -> id.it
  in
  parens (get_id param ^ " : " ^ render_param_type exp_type param)


(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
  | RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and render_lambda binds text =
  parens ("fun " ^ String.concat " " binds ^ " => " ^ text)

and render_path_start (p : path) start_exp is_extend end_exp = 
  let paths = List.rev (p :: transform_list_path p) in
  (render_path paths (start_exp.note) p.at 0 (Some start_exp) is_extend end_exp)

and render_path (paths : path list) typ at n name is_extend end_exp = 
  let render_record_update t1 t2 t3 =
    parens ("{ " ^ t1 ^ " with " ^ t2 ^ " := " ^ t3 ^ " }")
  in
  let r_func_e = render_exp RHS in
  let is_dot p = (match p.it with
    | DotP _ -> true
    | _ -> false 
  ) in
  let list_name num = (match name with
    | Some exp -> exp
    | None -> VarE ((var_prefix ^ string_of_int num) $ no_region) $$ no_region % typ
  ) in
  let new_name_typ = remove_iter_from_type (list_name n).note in
  let new_name = var_prefix ^ string_of_int (n + 1) in 
  match paths with
  (* End logic for extend *)
  | [{it = IdxP (_, e); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " ++ " ^ r_func_e end_exp) in
    let bind = render_bind RHS (ExpB (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("List.modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ render_lambda [bind] extend_term)
  | [{it = DotP (_, a); _}] when is_extend -> 
    let projection_term = parens (r_func_e (list_name n) ^ "." ^ render_atom a) in
    let extend_term = parens (projection_term ^ " ++ " ^ r_func_e end_exp) in
    render_record_update (r_func_e (list_name n)) (render_atom a) extend_term
  | [{it = SliceP (_, e1, e2); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " ++ " ^ r_func_e end_exp) in
    let bind = render_bind RHS (ExpB (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ render_lambda [bind] extend_term)
  (* End logic for update *)
  | [{it = IdxP (_, e); _}] -> 
    let bind = render_bind RHS (ExpB ("_" $ no_region, new_name_typ) $ no_region) in
    parens ("List.modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [bind] (r_func_e end_exp))
  | [{it = DotP (_, a); _}] -> 
    render_record_update (r_func_e (list_name n)) (render_atom a) (r_func_e end_exp)
  | [{it = SliceP (_, e1, e2); _}] -> 
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ r_func_e end_exp)
  (* Middle logic *)
  | {it = IdxP (_, e); note; _} :: ps -> 
    let path_term = render_path ps note at (n + 1) None is_extend end_exp in
    let new_name = var_prefix ^ string_of_int (n + 1) in 
    let bind = render_bind RHS (ExpB (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("List.modify " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [bind] path_term)
  | ({it = DotP _; note; _} as p) :: ps -> 
    let (dot_paths, ps') = list_split is_dot (p :: ps) in
    let (end_atom, dot_paths') = match List.rev dot_paths with
      | {it = DotP (_, a'); _} :: ds -> (a', ds)
      | _ -> assert false (* Impossible since it has p *)
    in
    let projection_term = List.fold_right (fun p acc -> 
      match p.it with
      | DotP (_, a') -> 
        DotE (acc, a') $$ no_region % p.note
      | _ -> error at "Should be a record access" (* Should not happen *)
    )  dot_paths' (list_name n) in
    let update_fields = String.concat "." (List.map (fun p ->
      match p.it with
      | DotP (_, a) -> render_atom a
      | _ -> error at "Should be a record access" 
    ) dot_paths) in
    let new_term = parens (r_func_e projection_term ^ "." ^ render_atom end_atom) in
    let new_exp = DotE (projection_term, end_atom) $$ no_region % note in 
    if ps' = [] 
      then (
        let final_term = if is_extend then parens (new_term ^ " ++ " ^ r_func_e end_exp) else r_func_e end_exp in
        render_record_update (r_func_e (list_name n)) update_fields final_term
      )
      else (
        let path_term = render_path ps' note at n (Some new_exp) is_extend end_exp in
        render_record_update (r_func_e (list_name n)) update_fields path_term
      )
  | ({it = SliceP (_, _e1, _e2); _} as p) :: _ps ->
    (* TODO - this is not entirely correct. Still unsure how to implement this as a term *)
    (* let new_typ = transform_type' NORMAL note in
    let path_term = render_path ps new_typ at (n + 1) None is_extend end_exp $@ transform_type' NORMAL note in
    let new_name = var_prefix ^ string_of_int (n + 1) in
    let lambda_typ = T_arrowtype [new_name_typ; new_typ] in
    T_app (T_exp_basic T_sliceupdate $@ anytype',
      [list_name n; transform_exp NORMAL e1; transform_exp NORMAL e2; T_lambda ([(new_name, new_name_typ)], path_term) $@ lambda_typ]) *)
    comment_parens (Il.Print.string_of_path p)
  (* Catch all error if we encounter empty list or RootP *)
  | _ -> error at "Paths should not be empty"

and render_binders (binds : bind list) = 
  string_of_list_prefix " " " " (render_bind RHS) binds

let render_binders_ids (binds : bind list) = 
  string_of_list_prefix " " " " get_bind_id binds

let render_match_binders params =
  String.concat ", " (List.map get_param_id params)

let render_params params = 
  string_of_list_prefix " " " " (render_param RHS) params

let render_match_args args =
  string_of_list_prefix " " ", " (render_arg LHS) args


let string_of_eqtype_proof recursive (cant_do_equality: bool) id (binds : bind list) =
  let binders = render_binders binds in 
  let binder_ids = render_binders_ids binds in
  (* Decidable equality proof *)
  (* e.g.
    Definition functype_eq_dec : forall (tf1 tf2 : functype),
      {tf1 = tf2} + {tf1 <> tf2}.
    Proof. decidable_equality. Defined.
    Definition functype_eqb v1 v2 : bool := functype_eq_dec v1 v2.
    Definition eqfunctypeP : Equality.axiom functype_eqb :=
      eq_dec_Equality_axiom functype functype_eq_dec.

    HB.instance Definition _ := hasDecEq.Build (functype) (eqfunctypeP).
    *)
  (if cant_do_equality then comment_parens "FIXME - No clear way to do decidable equality" ^ "\n" else "") ^
  (match recursive with
  | true -> 
    
    "Fixpoint " ^ id ^ "_eq_dec" ^ binders ^ " (v1 v2 : " ^ id ^ binder_ids ^ ") {struct v1} :\n" ^
    "  {v1 = v2} + {v1 <> v2}.\n" ^
    let proof = if cant_do_equality then "Admitted" else "decide equality; do ? decidable_equality_step. Defined" in
    "Proof. " ^ proof ^ "\n\n"
  | false -> 
    "Definition " ^ id ^ "_eq_dec : forall" ^ binders ^ " (v1 v2 : " ^ id ^ binder_ids ^ "),\n" ^
    "  {v1 = v2} + {v1 <> v2}.\n" ^
    
    let proof = if cant_do_equality then "Admitted" else "do ? decidable_equality_step. Defined" in
    "Proof. " ^ proof ^ "\n\n") ^ 

  "Definition " ^ id ^ "_eqb" ^ binders ^ " (v1 v2 : " ^ id ^ binder_ids ^ ") : bool :=\n" ^
  "  is_left" ^ parens (id ^ "_eq_dec" ^ binder_ids ^ " v1 v2") ^ ".\n" ^  
  "Definition eq" ^ id ^ "P" ^ binders ^ " : Equality.axiom " ^ parens (id ^ "_eqb" ^ binder_ids) ^ " :=\n" ^
  "  eq_dec_Equality_axiom " ^ parens (id ^ binder_ids) ^ " " ^ parens (id ^ "_eq_dec" ^ binder_ids) ^ "\n\n" ^
  "HB.instance Definition _" ^ binders ^ " := hasDecEq.Build " ^ parens (id ^ binder_ids) ^ " " ^ parens ("eq" ^ id ^ "P" ^ binder_ids) ^ ".\n" ^
  "Hint Resolve " ^ id ^ "_eq_dec : eq_dec_db" 

let string_of_relation_args typ = 
  string_of_list "" " -> " " -> " (render_type REL) (transform_case_typ typ)
  
let rec render_prem prem =
  let r_func = render_prem in 
  match prem.it with
  | IfPr exp -> render_exp REL exp
  | RulePr (id, _m, exp) -> parens (id.it ^ string_of_list_prefix " " " " (render_exp REL) (transform_case_tup exp))
  | NegPr p -> parens ("¬" ^ r_func p)
  | ElsePr -> error prem.at "Encountered an otherwise premise. Run the else-removal pass"
  | IterPr (p, (_, [])) -> r_func p
  | IterPr (p, (iter, ps)) -> 
    let option_conversion s = if iter = Opt then parens ("Option.toList " ^ s) else s in
    let binds = List.map (fun (id, e) -> parens (id.it ^ " : " ^ render_type REL (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in 
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt iter_prem_rels_list n) with 
    | Some s -> s
    | None -> error prem.at "Iteration exceeded the supported amount for rocq translation"
    in 
    pred_name ^ " " ^ render_lambda binds (r_func p) ^ " " ^ 
    String.concat " " (List.map (render_exp REL) iter_exps |> List.map option_conversion)
  | LetPr _ -> error prem.at "Encountered a let premise. Run the let-introduction pass"
 
let render_typealias id binds typ = 
  "abbrev " ^ render_id id ^ render_binders binds ^ " : Type := " ^ render_type RHS typ

let render_record id binds fields = 
  let constructor_name = "MK" ^ id in
  let inhabitance_binders = render_binders binds in 
  let binders = render_binders_ids binds in 

  (* Standard Record definition *)
  "structure " ^ id ^ inhabitance_binders ^ " where " ^ constructor_name ^ " ::\n  " ^ 
  String.concat "\n  " (List.map (fun (a, (_, typ, _), _) -> 
    render_atom a ^ " : " ^ render_type RHS typ) fields) ^ "\n" ^

  "deriving Inhabited, BEq\n\n" ^

  (* SpecTec only defines record composition when every field is composable. *)
  if List.for_all (fun (_, (_, typ, _), _) ->
      is_composable_type StringSet.empty !env_ref typ) fields then
    "def _append_" ^ id ^ inhabitance_binders ^ " (arg1 arg2 : " ^
    parens (id ^ binders) ^ ") : " ^ render_id id ^ " where" ^
    "\n  " ^ String.concat "\n  " (List.map (fun (a, _, _) ->
      let field = render_atom a in
      field ^ " := arg1." ^ field ^ " ++ arg2." ^ field
    ) fields) ^ "\n" ^
    "instance : Append " ^ render_id id ^
    " where\n  append arg1 arg2 := _append_" ^ id ^ " arg1 arg2\n\n"
  else ""

let rec has_typ id t =
  match t.it with
  | VarT (id', _) -> id'.it = id
  | IterT (t', _) ->  has_typ id t'
  | TupT pairs -> List.exists (fun (_, t') -> has_typ id t') pairs
  | _ -> false

let cant_do_equality binds cases = 
  (List.exists is_typ_bind binds) ||
  (List.exists (fun (_, (binds', _, _), _) -> List.exists is_typ_bind binds') cases)
  
let render_case_typs t = 
  let typs = transform_case_args t in
  string_of_list_prefix " " " " (fun (e, t) -> 
    parens (render_exp RHS e ^ " : " ^ render_type RHS t)) typs

let render_variant_typ id binds cases = 
  "inductive " ^ render_id id ^ render_binders binds ^ " : Type where\n  " ^
  String.concat "\n  " (List.map (fun (m, (_, t, _), _) ->
    "| " ^ render_mixop m ^ render_case_typs t ^ " : " ^ render_id id ^ render_binders_ids binds   
  )  cases) ^ 
  "\nderiving Inhabited, BEq\n"

let clauses_have_same_args c1 c2 =
  match (c1.it, c2.it) with
  | (DefD (binds1, args1, _, _), DefD (binds2, args2, _, _)) ->
    Il.Eq.eq_list Il.Eq.eq_bind binds1 binds2 &&
    Il.Eq.eq_list Il.Eq.eq_arg args1 args2

let group_clauses_by_same_args clauses =
  let group_helper acc clause =
    match acc with
    | [] -> [[clause]]
    | group :: rest ->
      let representative = List.hd group in
      if clauses_have_same_args representative clause then
        (group @ [clause]) :: rest
      else
        [clause] :: group :: rest
  in
  List.fold_left group_helper [] clauses |> List.rev

let render_function_def id params r_typ clauses = 
  let groups = group_clauses_by_same_args clauses in
  "def " ^ render_id id ^ " : ∀ " ^ render_params params ^ " , " ^ render_type RHS r_typ ^ "\n" ^
  String.concat "\n" (List.map (fun group -> match (List.hd group).it with
    | DefD (_, args, _, _) -> 
    "  |" ^ render_match_args args ^ " =>\n    " ^
    String.concat "\n    " (List.map (fun clause ->
      let DefD (_, _, exp, prems) = clause.it in
      match prems with
      | [] -> render_exp RHS exp
      | [{it = ElsePr; _}] -> "  " ^ render_exp RHS exp
      | _ ->
        "if " ^ String.concat " && " (List.map (fun prem -> render_prem prem) prems) ^ " then\n      " ^
        render_exp RHS exp ^ "\n    else"
    ) group)
  ) groups) ^
  "\n"

let pos_le left right =
  left.line < right.line ||
  left.line = right.line && left.column <= right.column

let region_contains outer inner =
  outer <> no_region && inner <> no_region &&
  outer.left.file = inner.left.file && inner.left.file = inner.right.file &&
  pos_le outer.left inner.left && pos_le inner.right outer.right

let rec is_wf_prem prem =
  match prem.it with
  | RulePr (id, _, _) -> StringSet.mem id.it !wf_relations_ref
  | IterPr (inner, _) -> is_wf_prem inner
  | IfPr _ | LetPr _ | ElsePr | NegPr _ -> false

let bind_is_free free bind =
  match bind.it with
  | ExpB (id, _) -> Il.Free.Set.mem id.it free.Il.Free.varid
  | TypB id -> Il.Free.Set.mem id.it free.Il.Free.typid
  | DefB (id, _, _) -> Il.Free.Set.mem id.it free.Il.Free.defid
  | GramB (id, _, _) -> Il.Free.Set.mem id.it free.Il.Free.gramid

let relation_lhs exp =
  match transform_case_tup exp with
  | [lhs; _] -> lhs
  | _ -> error exp.at "Expected a binary relation while reconstructing `otherwise`"

let retained_otherwise_prems rule prems =
  List.filter (fun prem ->
    region_contains rule.at prem.at || is_wf_prem prem
  ) prems

let fresh_otherwise_subject previous =
  let used =
    List.fold_left (fun names (binds, _, _) ->
      List.fold_left (fun names bind -> StringSet.add (get_bind_id bind) names)
        names binds
    ) StringSet.empty previous
  in
  let rec choose index =
    let suffix = if index = 0 then "" else "_" ^ string_of_int index in
    let candidate = "spectec_otherwise_subject" ^ suffix in
    if StringSet.mem candidate used then choose (index + 1) else candidate
  in
  choose 0

(* A rule marked `otherwise` means that none of the preceding rules can apply
   to the same LHS.  ElseSimp flattens the existential binders of those rules
   into universal constructor binders, which is not equivalent.  Rebuild the
   original quantifier structure directly as a proposition:

     not (exists previous-rule binders, previous LHS = current LHS and prems)

   Including syntactically disjoint preceding rules is harmless: their LHS
   equality is uninhabited, and avoids duplicating the middle-end's purely
   optimizing apartness analysis in the backend. *)
let render_otherwise_proposition lhs previous =
  let subject = fresh_otherwise_subject previous in
  let alternatives = List.map (fun (binds, previous_lhs, prems) ->
    let body =
      String.concat " ∧ "
        ((render_exp REL previous_lhs ^ " = " ^ subject) :: prems)
      |> parens
    in
    match binds with
    | [] -> body
    | _ ->
      parens ("∃ " ^ String.concat " " (List.map (render_bind REL) binds) ^
        ", " ^ body)
  ) previous in
  if alternatives = [] then
    error lhs.at "An `otherwise` rule has no preceding rules"
  else
    parens ("(fun (" ^ subject ^ " : " ^ render_type REL lhs.note ^ ") => ¬ " ^
      parens (String.concat " ∨ " alternatives) ^ ") " ^ render_exp REL lhs)

let render_relation id typ rules =
  let has_otherwise = List.exists (fun rule ->
    match rule.it with
    | RuleD (rule_id, _, _, _, _) ->
      StringSet.mem (otherwise_key id rule_id.it) !otherwise_rules_ref
  ) rules in
  if not has_otherwise then
    "inductive " ^ id ^ " : " ^ string_of_relation_args typ ^ "Prop where\n  " ^
    String.concat "\n  " (List.map (fun rule ->
      match rule.it with
      | RuleD (rule_id, binds, _, exp, prems) ->
        let string_prems =
          string_of_list "\n    " " ->\n    " " ->\n    " render_prem prems
        in
        let forall_quantifiers =
          string_of_list "forall " ", " " " (render_bind REL) binds
        in
        "| " ^ render_id rule_id.it ^ " : " ^ forall_quantifiers ^
        string_prems ^ id ^ " " ^
        String.concat " " (List.map (render_exp REL) (transform_case_tup exp))
    ) rules)
  else
  let _, rendered_rules =
    List.fold_left (fun (previous, rendered) rule ->
      match rule.it with
      | RuleD (rule_id, binds, _, exp, prems) ->
        let lhs = relation_lhs exp in
        let is_otherwise =
          StringSet.mem (otherwise_key id rule_id.it) !otherwise_rules_ref
        in
        let retained_prems =
          if is_otherwise then retained_otherwise_prems rule prems else prems
        in
        let semantic_prems = List.map render_prem retained_prems in
        let semantic_prems =
          if is_otherwise then
            semantic_prems @ [render_otherwise_proposition lhs previous]
          else semantic_prems
        in
        let binds =
          if is_otherwise then
            let free = Il.Free.union (Il.Free.free_exp exp)
              (Il.Free.free_list Il.Free.free_prem retained_prems) in
            List.filter (bind_is_free free) binds
          else binds
        in
        let string_prems =
          string_of_list "\n    " " ->\n    " " ->\n    " Fun.id semantic_prems
        in
        let forall_quantifiers =
          string_of_list "forall " ", " " " (render_bind REL) binds
        in
        let rendered_rule =
          "| " ^ render_id rule_id.it ^ " : " ^ forall_quantifiers ^
          string_prems ^ id ^ " " ^
          String.concat " " (List.map (render_exp REL) (transform_case_tup exp))
        in
        previous @ [(binds, lhs, semantic_prems)], rendered @ [rendered_rule]
    ) ([], []) rules
  in
  "inductive " ^ id ^ " : " ^ string_of_relation_args typ ^ "Prop where\n  " ^
  String.concat "\n  " rendered_rules

let render_axiom id params r_typ =
  let signature =
    string_of_list "forall " ", " " " (render_param RHS) params ^ render_type RHS r_typ
  in
  "def " ^ render_id id.it ^ " : " ^ signature ^ " := SpectecBuiltins." ^ render_id id.it

let render_rel_axiom id typ =
  "opaque " ^ id.it ^ " : " ^ string_of_relation_args typ ^ "Prop"

let render_global_declaration id typ exp = 
  "def " ^ id.it ^ " : " ^ render_type RHS typ ^ " := " ^ render_exp RHS exp

let get_type_alias_id def = 
  match def.it with
  | TypD (id, _, [inst]) when is_alias_typ inst -> Some id.it
  | _ -> None

let has_prems c = 
  match c.it with
  | DefD (_, _, _, prems) -> prems <> []

(* In-order traversal of args, collecting variables. Only support expressions that we expect in function patterns *)
let rec
  args_vars (args : arg list) : string list = List.concat_map arg_vars args
and
  arg_vars (arg : arg) : string list = match arg.it with
  | ExpA e -> exp_vars e
  | TypA _ -> []
  | DefA id -> [id.it]
  | _ -> [] 
and
  exp_vars (e : exp) : string list = match e.it with
  | VarE id -> [id.it]
  | CaseE (_, e1) -> exp_vars e1
  | TupE exps -> List.concat_map exp_vars exps
  | _ -> []

(* Check if the args mention a pattern variable more than once *)
let has_nonlinear_pattern c =
  match c.it with
  | DefD (binds, args, _, _) -> 
    let bound_ids = List.map get_bind_id binds in
    let rec go seen (vars : string list) =
      match vars with
      | [] -> false
      | id :: rest ->
        if List.mem id bound_ids then
          if List.mem id seen then true
          else go (id :: seen) rest
        else
          go seen rest
    in
    go [] (args_vars args)

let rec is_bool_premise prem =
  match prem.it with
  | IfPr _exp -> true
  | NegPr prem -> is_bool_premise prem
  | _ -> false

let is_else_premise prem =
  match prem.it with
  | ElsePr -> true
  | _ -> false

let is_supported_clause _id clauses = 
  match List.rev clauses with
  | [] -> true 
  | [c] -> not (has_prems c)
  | last :: others -> 
    (* Printf.eprintf "Checking supported clauses; %s\n" (String.concat "\n" (List.map (Il.Print.string_of_clause id) clauses)); *)
    (let DefD (_, _, _, prems) = last.it in match prems with | [p] -> is_else_premise p | _ -> false) &&
    List.for_all (fun c -> 
      let DefD (_, _, _, prems) = c.it in
      List.for_all is_bool_premise prems
    ) others

let is_supported_function id _params _r_typ clauses = 
  List.for_all (fun c -> not (has_nonlinear_pattern c)) clauses &&
  List.for_all (is_supported_clause id) (group_clauses_by_same_args clauses)

let is_axiom def =
  match def.it with
  | DecD (_, _, _, _clauses) -> true
  | _ -> false

let is_builtin def =
    match def.it with
    | TypD (id, _, _) -> List.mem id.it builtins
    | DecD (id, _, _, _) -> List.mem id.it builtins
    | RelD (id, _, _, _) -> List.mem id.it builtins
    | _ ->false

let rec string_of_def def = 
  comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region def.at) ^ "\n" ^
  begin
  if is_builtin def then "/- elided, builtin -/" else
  match def.it with
  | TypD (id, _, [{it = InstD (binds, _, {it = AliasT typ; _}); _}]) -> 
    render_typealias id.it binds typ
  | TypD (id, _, [{it = InstD (binds, _, {it = StructT typfields; _}); _}])-> 
    render_record id.it binds typfields
  | TypD (id, _, [{it = InstD (binds, _, {it = VariantT typcases; _}); _}]) -> 
    render_variant_typ id.it binds typcases
  | DecD (id, [], typ, [{it = DefD ([], [], exp, _); _}]) -> 
    render_global_declaration id typ exp
  | DecD (id, params, typ, []) -> 
    render_axiom id params typ
  | DecD (id, params, typ, clauses) -> 
    if is_supported_function id params typ clauses then
      render_function_def id.it params typ clauses
    else
      error def.at ("Unsupported concrete function: " ^ Il.Print.string_of_def def)
  | RelD (id, _, typ, []) -> 
    render_rel_axiom id typ
  | RelD (id, _, typ, rules) -> 
    render_relation id.it typ rules
  (* Mutual recursion *)
  | RecD defs ->
    begin match defs with
    | [] -> ""
    | [d] -> string_of_def d
    (* HACK - this is simply to deal with functions that are not supposed to be axioms.
    The functions that are supposed to be axioms should not be mutually recursive anyways.
    *)
    | (_d :: _defs') when List.exists is_axiom defs ->
      String.concat "\n\n" (List.map string_of_def defs)
    | (_d :: _defs') -> 
      "mutual\n" ^
      String.concat "\n\n" (List.map string_of_def defs) ^ "\n\n" ^ 
      "end"
    end
  | _ -> error def.at ("Unsupported def: " ^ Il.Print.string_of_def def)
  end

let exported_string = {|import Std

/- Preamble -/
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option match.ignoreUnusedAlts true

instance : Append (Option a) where
  append := fun o1 o2 => match o1 with | none => o2 | _ => o1
    
def Forall (R : α → Prop) (xs : List α) : Prop :=
  ∀ x ∈ xs, R x
def Forall₂ (R : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  ∀ x y, (x,y) ∈ List.zip xs ys → R x y
def Forall₃ (R : α → β → γ → Prop) (xs : List α) (ys : List β) (zs : List γ) : Prop :=
  ∀ x y z, (x,y,z) ∈ List.zip xs (List.zip ys zs) → R x y z

def list_slice_update (xs : List α) (start len : Nat) (replacement : List α) : List α :=
  xs.take start ++ replacement ++ xs.drop (start + len)

def list_map3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: list_map3 f xs ys zs
  | _, _, _ => []

def option_zipWith (f : α → β → γ) : Option α → Option β → Option γ
  | some x, some y => some (f x y)
  | _, _ => none

def option_map3 (f : α → β → γ → δ) : Option α → Option β → Option γ → Option δ
  | some x, some y, some z => some (f x y z)
  | _, _, _ => none

/- written manually due to `BEq` constraint -/
def disjoint_ (X : Type) [BEq X] : ∀ (var_0 : (List X)), Bool
  | [] => true
  | (w :: w'_lst) => ((!(List.contains w'_lst w)) && (disjoint_ X w'_lst))

/- written manually due to `BEq` constraint -/
def setminus_ (X : Type) [BEq X] (l1 l2 : List X) : List X :=
  l1.filter (fun x => !(List.contains l2 x))
|}


let rec is_valid_def def = 
  match def.it with
  | GramD _ | HintD _ -> false
  | RecD defs -> List.for_all is_valid_def defs
  | _ -> true

let rec is_relation_def def =
  match def.it with
  | RelD _ -> true
  | RecD defs -> List.for_all is_relation_def defs
  | _ -> false

let rec flatten_relation_defs def =
  match def.it with
  | RelD _ -> [def]
  | RecD defs -> List.concat_map flatten_relation_defs defs
  | _ -> assert false

let rec collect_prem_relations relations prem =
  match prem.it with
  | RulePr (id, _, exp) ->
    let signature =
      transform_case_tup exp
      |> List.map (fun arg -> arg.note)
      |> string_of_list "" " -> " " -> " (render_type REL)
    in
    StringMap.add id.it signature relations
  | IterPr (prem, _) | NegPr prem -> collect_prem_relations relations prem
  | IfPr _ | LetPr _ | ElsePr -> relations

let collect_rule_relations relations rule =
  match rule.it with
  | RuleD (_, _, _, _, prems) ->
    List.fold_left collect_prem_relations relations prems

let collect_clause_relations relations clause =
  match clause.it with
  | DefD (_, _, _, prems) ->
    List.fold_left collect_prem_relations relations prems

let rec collect_def_relations relations def =
  match def.it with
  | RelD (_, _, _, rules) ->
    List.fold_left collect_rule_relations relations rules
  | DecD (_, _, _, clauses) ->
    List.fold_left collect_clause_relations relations clauses
  | RecD defs -> List.fold_left collect_def_relations relations defs
  | TypD _ | GramD _ | HintD _ -> relations

let missing_relations defs relations =
  let declared =
    List.fold_left (fun ids def ->
      match def.it with
      | RelD (id, _, _, _) -> StringSet.add id.it ids
      | _ -> assert false
    ) StringSet.empty relations
  in
  List.fold_left collect_def_relations StringMap.empty defs
  |> StringMap.filter (fun id _ -> not (StringSet.mem id declared))
  |> StringMap.bindings

let render_missing_relation (id, signature) =
  comment_parens "Relation referenced without an explicit declaration" ^ "\n" ^
  "opaque " ^ render_id id ^ " : " ^ signature ^ "Prop"

(* Middle-end passes can introduce relation dependencies after the front end has
   formed recursive groups. Recompute those groups here and print relations only
   after all data types and functions, so Lean never sees a forward reference. *)
let render_relations relations =
  let relation_id def =
    match def.it with
    | RelD (id, _, _, _) -> id.it
    | _ -> assert false
  in
  let relation_array = Array.of_list relations in
  let indices =
    Array.fold_left (fun (map, i) def ->
      StringMap.add (relation_id def) i map, i + 1
    ) (StringMap.empty, 0) relation_array
    |> fst
  in
  let graph =
    Array.map (fun def ->
      Il.Free.Set.elements (Il.Free.free_def def).relid
      |> List.filter_map (fun id -> StringMap.find_opt id indices)
      |> Array.of_list
    ) relation_array
  in
  Util.Scc.sccs graph
  |> List.map (fun component ->
    let defs =
      Util.Scc.Set.elements component
      |> List.map (Array.get relation_array)
    in
    match defs with
    | [def] -> string_of_def def
    | _ ->
      "mutual\n" ^
      String.concat "\n\n" (List.map string_of_def defs) ^
      "\n\nend"
  )
  |> String.concat "\n\n"

let abstract_signature params r_typ =
  string_of_list "forall " ", " " " (render_param RHS) params ^ render_type RHS r_typ

let render_builtin_interface builtins =
  let fields =
    List.map (fun (id, params, r_typ) ->
      "  " ^ render_id id.it ^ " : " ^ abstract_signature params r_typ
    ) builtins
    |> String.concat "\n"
  in
  let accessors =
    List.map (fun (id, params, r_typ) -> render_axiom id params r_typ) builtins
    |> String.concat "\n\n"
  in
  "class SpectecBuiltins where\n" ^ fields ^ "\n\n" ^
  "variable [SpectecBuiltins]\n\n" ^ accessors

let rec extract_abstract_def def =
  match def.it with
  | DecD (id, params, r_typ, []) -> [(id, params, r_typ)], None
  | RecD defs ->
    let builtins, remaining =
      List.map extract_abstract_def defs |> List.split
    in
    let remaining = List.filter_map Fun.id remaining in
    let remainder = if remaining = [] then None else Some (RecD remaining $ def.at) in
    List.concat builtins, remainder
  | _ -> [], Some def

let extract_abstract_defs defs =
  let builtins, remaining = List.map extract_abstract_def defs |> List.split in
  List.concat builtins, List.filter_map Fun.id remaining

let rec is_type_definition def =
  match def.it with
  | TypD _ -> true
  | RecD defs -> List.for_all is_type_definition defs
  | _ -> false

let application id params =
  parens (render_id id ^ string_of_list_prefix " " " " (fun param ->
    render_id (get_param_id param)) params)

let wf_uN width value = parens ("wf_uN " ^ width ^ " " ^ value)
let wf_fN width value = parens ("wf_fN " ^ width ^ " " ^ value)
let wf_val typ value = parens ("wf_val_ " ^ typ ^ " " ^ value)

let forall_results predicate values =
  "Forall " ^ parens ("fun result => " ^ predicate "result") ^ " " ^ values

let option_results predicate values = forall_results predicate (parens ("Option.toList " ^ values))

let law_signature params assumptions result =
  let conclusion = String.concat " ->\n  " (assumptions @ [result]) in
  string_of_list "forall " ",\n  " " " (render_param RHS) params ^ conclusion

let parameter_values_of_types type_ids params =
  List.filter_map (fun param ->
    match param.it with
    | ExpP (id, {it = VarT (type_id, _); _}) when List.mem type_id.it type_ids ->
      Some (render_id id.it)
    | _ -> None
  ) params

let first = function
  | value :: _ -> Some value
  | [] -> None

let last values = first (List.rev values)

type indexed_context = {
  width : string option;
  valtype : string option;
}

let unindexed_wf_predicate id value =
  let relation_id = "wf_" ^ id.it in
  match Il.Env.find_opt_rel !env_ref (relation_id $ id.at) with
  | Some (_, typ, _) when List.length (transform_case_typ typ) = 1 ->
    Some (parens (render_id relation_id ^ " " ^ value))
  | _ -> None

(* The Undep pass deliberately erases the indices from iN, fN, and val_.  For
   Wasm 1.0 declarations, width parameters are ordered input then output (M,
   N), as are valtype parameters.  Reconstruct the preservation proposition
   from that uniform signature shape rather than from operation names.  Types
   whose generated wf relation has no index (for example byte) are recovered
   directly from the relation environment. *)
let rec indexed_predicate context typ value =
  let with_width predicate =
    match context.width with
    | Some width -> Some (predicate width value)
    | None -> None
  in
  let with_valtype =
    match context.valtype with
    | Some typ -> Some (wf_val typ value)
    | None -> None
  in
  match typ.it with
  | VarT (id, _) when List.mem id.it ["iN"; "uN"] -> with_width wf_uN
  | VarT (id, _) when id.it = "fN" -> with_width wf_fN
  | VarT (id, _) when id.it = "u32" -> Some (wf_uN "32" value)
  | VarT (id, _) when id.it = "val_" -> with_valtype
  | VarT (id, _) -> unindexed_wf_predicate id value
  | IterT (inner, Opt) ->
    begin match indexed_predicate context inner "result" with
    | Some predicate -> Some (option_results (fun _ -> predicate) value)
    | None -> None
    end
  | IterT (inner, _) ->
    begin match indexed_predicate context inner "result" with
    | Some predicate -> Some (forall_results (fun _ -> predicate) value)
    | None -> None
    end
  | _ -> None

let render_builtin_preservation id params r_typ =
  let widths = parameter_values_of_types ["M"; "N"] params in
  let valtypes = parameter_values_of_types ["valtype"] params in
  let input_context = {width = first widths; valtype = first valtypes} in
  let output_context = {width = last widths; valtype = last valtypes} in
  let assumptions =
    List.filter_map (fun param ->
      match param.it with
      | ExpP (param_id, typ) ->
        indexed_predicate input_context typ (render_id param_id.it)
      | _ -> None
    ) params
  in
  let app = application id params in
  match indexed_predicate output_context r_typ app with
  | Some result -> Some (id, law_signature params assumptions result)
  | None -> None

let rec collect_preservation_laws defs =
  List.concat_map (fun def ->
    match def.it with
    | DecD (id, params, r_typ, []) ->
      begin match render_builtin_preservation id.it params r_typ with
      | Some law -> [law]
      | None -> []
      end
    | RecD nested -> collect_preservation_laws nested
    | _ -> []
  ) defs

let render_preservation_laws defs =
  let laws = collect_preservation_laws defs in
  match laws with
  | [] -> ""
  | _ ->
    let fields =
      List.map (fun (id, signature) ->
        "  preserves_" ^ render_id id ^ " : " ^ signature
      ) laws |> String.concat "\n"
    in
    let accessors =
      List.map (fun (id, signature) ->
        comment_parens "Well-formedness guaranteed by the indexed SpecTec declaration" ^ "\n" ^
        "theorem spectec_preserves_" ^ render_id id ^ " : " ^ signature ^ " :=\n" ^
        "  SpectecBuiltinLaws.preserves_" ^ render_id id
      ) laws |> String.concat "\n\n"
    in
    "class SpectecBuiltinLaws [SpectecBuiltins] : Prop where\n" ^ fields ^ "\n\n" ^
    "variable [SpectecBuiltinLaws]\n\n" ^ accessors
  
let string_of_script (il : script) =
  register_backend_hints il;
  env_ref := Il.Env.env_of_script il;
  let valid_defs = List.filter is_valid_def il in
  let relation_groups, other_defs = List.partition is_relation_def valid_defs in
  let builtins, other_defs = extract_abstract_defs other_defs in
  let type_defs, term_defs = List.partition is_type_definition other_defs in
  let relations = List.concat_map flatten_relation_defs relation_groups in
  let missing = missing_relations valid_defs relations in
  exported_string ^ 
  "/- Generated Code -/\n\n" ^
  String.concat "\n\n" (List.map string_of_def type_defs) ^
  "\n\n" ^ render_builtin_interface builtins ^
  "\n\n" ^ String.concat "\n\n" (List.map string_of_def term_defs) ^
  "\n\n" ^ String.concat "\n\n" (List.map render_missing_relation missing) ^
  "\n\n" ^ render_relations relations ^
  "\n\n" ^ render_preservation_laws il
