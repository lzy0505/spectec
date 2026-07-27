#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repo_dir="$(cd -- "$script_dir/.." && pwd -P)"
generator="$script_dir/_build/default/src/exe-spectec/main.exe"
output="$script_dir/Wasm.lean"
snapshot_dir="$repo_dir/specification/wasm-1.0"
revision_file="$snapshot_dir/REVISION"
updater="$repo_dir/specification/update-wasm-1.0.sh"
update_snapshot=false

work_dir=""
output_tmp=""

usage() {
  cat <<EOF
Usage: $(basename "$0") [--update]

Generate Wasm.lean from the pinned specification/wasm-1.0 snapshot.
With --update, refresh and repin the snapshot before generating.
EOF
}

cleanup() {
  if [[ -n "$output_tmp" && -e "$output_tmp" ]]; then
    rm -f -- "$output_tmp"
  fi
  if [[ -n "$work_dir" && -e "$work_dir" ]]; then
    rm -rf -- "$work_dir"
  fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

require_command() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: required command not found: $1" >&2
    exit 1
  fi
}

revision_value() {
  local key="$1"
  awk -F= -v key="$key" '$1 == key {sub(/^[^=]*=/, ""); print; found = 1} END {
    if (!found) exit 1
  }' "$revision_file"
}

while (( $# > 0 )); do
  case "$1" in
    --update)
      update_snapshot=true
      shift
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

require_command awk
require_command lean
require_command mktemp

if [[ ! -x "$updater" ]]; then
  echo "error: updater is not executable: $updater" >&2
  exit 1
fi

if $update_snapshot; then
  "$updater"
fi

"$updater" --verify --destination "$snapshot_dir"
spec_commit="$(revision_value commit)"
snapshot_sha256="$(revision_value sha256)"

echo "Building the SpecTec Lean 4 generator..."
if command -v opam >/dev/null 2>&1; then
  (cd "$script_dir" && opam exec -- dune build src/exe-spectec/main.exe)
else
  require_command dune
  (cd "$script_dir" && dune build src/exe-spectec/main.exe)
fi

if [[ ! -x "$generator" ]]; then
  echo "error: generator was not built at $generator" >&2
  exit 1
fi

work_dir="$(mktemp -d "${TMPDIR:-/tmp}/spectec-wasm-1.0.XXXXXX")"
mkdir "$work_dir/_specification"
ln -s "$snapshot_dir" "$work_dir/_specification/wasm-1.0"

echo "Generating Wasm.lean from pinned WebAssembly/spec@$spec_commit..."
(
  cd "$work_dir"
  shopt -s nullglob
  sources=(_specification/wasm-1.0/*.spectec)
  if (( ${#sources[@]} == 0 )); then
    echo "error: pinned snapshot contains no Wasm 1.0 SpecTec sources" >&2
    exit 1
  fi
  "$generator" "${sources[@]}" --lean4 -o Wasm.lean
  lean -o Wasm.olean Wasm.lean
)

output_tmp="$(mktemp "$script_dir/.Wasm.lean.XXXXXX")"
cp "$work_dir/Wasm.lean" "$output_tmp"
mv -f -- "$output_tmp" "$output"
output_tmp=""

echo "Generated $output"
echo "Source commit: $spec_commit"
echo "Snapshot SHA-256: $snapshot_sha256"
