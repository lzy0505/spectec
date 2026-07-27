#!/usr/bin/env bash

set -euo pipefail

readonly default_repository="https://github.com/WebAssembly/spec.git"
readonly default_ref="main"

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repository="$default_repository"
ref="$default_ref"
destination="$script_dir/wasm-1.0"
verify_only=false
clone_dir=""
stage_dir=""
backup_dir=""
restore_backup=false

usage() {
  cat <<EOF
Usage: $(basename "$0") [--ref REF] [--repository URL] [--destination DIR]
       $(basename "$0") --verify [--destination DIR]

Replace specification/wasm-1.0 with the selected WebAssembly/spec snapshot.
The default ref is "main". REVISION records the resolved commit and a
deterministic SHA-256 of the copied files.

With --verify, check the existing snapshot against REVISION without fetching
or replacing anything.
EOF
}

die() {
  echo "error: $*" >&2
  exit 1
}

cleanup() {
  if $restore_backup && [[ ! -e "$destination" && -e "$backup_dir" ]]; then
    mv -- "$backup_dir" "$destination"
    restore_backup=false
  fi
  if [[ -n "$clone_dir" && -e "$clone_dir" ]]; then
    rm -rf -- "$clone_dir"
  fi
  if [[ -n "$stage_dir" && -e "$stage_dir" ]]; then
    rm -rf -- "$stage_dir"
  fi
  if [[ -n "$backup_dir" && -e "$backup_dir" ]]; then
    rm -rf -- "$backup_dir"
  fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

require_command() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

sha256_stream() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 | awk '{print $NF}'
  else
    die "one of sha256sum, shasum, or openssl is required"
  fi
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    die "one of sha256sum, shasum, or openssl is required"
  fi
}

snapshot_sha256() {
  local snapshot="$1"
  (
    cd "$snapshot"
    find . -type f ! -name REVISION -print |
      LC_ALL=C sort |
      while IFS= read -r file; do
        printf '%s  %s\n' "$(sha256_file "$file")" "${file#./}"
      done
  ) | sha256_stream
}

revision_value() {
  local revision_file="$1"
  local key="$2"
  awk -F= -v key="$key" '$1 == key {sub(/^[^=]*=/, ""); print; found = 1} END {
    if (!found) exit 1
  }' "$revision_file"
}

verify_snapshot() {
  local snapshot="$1"
  local revision_file="$snapshot/REVISION"
  local pinned_repository
  local pinned_commit
  local pinned_sha256
  local actual_sha256

  [[ -d "$snapshot" ]] || die "snapshot directory not found: $snapshot"
  [[ -f "$revision_file" ]] || die "revision file not found: $revision_file"

  pinned_repository="$(revision_value "$revision_file" repository)" ||
    die "REVISION does not specify repository"
  pinned_commit="$(revision_value "$revision_file" commit)" ||
    die "REVISION does not specify commit"
  pinned_sha256="$(revision_value "$revision_file" sha256)" ||
    die "REVISION does not specify sha256"

  [[ "$pinned_sha256" =~ ^[0-9a-fA-F]{64}$ ]] ||
    die "REVISION contains an invalid SHA-256: $pinned_sha256"

  actual_sha256="$(snapshot_sha256 "$snapshot")"
  [[ "$actual_sha256" == "$pinned_sha256" ]] ||
    die "snapshot SHA-256 mismatch: expected $pinned_sha256, got $actual_sha256"

  echo "Verified $snapshot"
  echo "Repository: $pinned_repository"
  echo "Upstream commit: $pinned_commit"
  echo "Snapshot SHA-256: $pinned_sha256"
}

while (( $# > 0 )); do
  case "$1" in
    --verify)
      verify_only=true
      shift
      ;;
    --ref)
      (( $# >= 2 )) || die "--ref requires an argument"
      ref="$2"
      shift 2
      ;;
    --repository)
      (( $# >= 2 )) || die "--repository requires an argument"
      repository="$2"
      shift 2
      ;;
    --destination)
      (( $# >= 2 )) || die "--destination requires an argument"
      destination="$2"
      shift 2
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      die "unknown argument: $1"
      ;;
  esac
done

require_command awk
require_command cp
require_command find
require_command git
require_command mktemp
require_command sort

destination_parent="$(cd -- "$(dirname -- "$destination")" && pwd -P)"
destination_name="$(basename -- "$destination")"
[[ "$destination_name" != "." && "$destination_name" != ".." ]] ||
  die "destination must name a directory, not $destination_name"
destination="$destination_parent/$destination_name"

[[ "$destination" != "/" ]] || die "refusing to replace the filesystem root"
[[ "$destination" != "$destination_parent" ]] ||
  die "destination must be a child of its parent directory"

if $verify_only; then
  verify_snapshot "$destination"
  exit 0
fi

clone_dir="$(mktemp -d "${TMPDIR:-/tmp}/spectec-wasm-1.0.clone.XXXXXX")"
stage_dir="$(mktemp -d "$destination_parent/.wasm-1.0.update.XXXXXX")"
backup_dir="$destination_parent/.wasm-1.0.backup.$$"
[[ ! -e "$backup_dir" ]] || die "backup path already exists: $backup_dir"

echo "Fetching $repository@$ref..."
git clone \
  --quiet \
  --depth 1 \
  --filter=blob:none \
  --sparse \
  --branch "$ref" \
  "$repository" \
  "$clone_dir/spec"
git -C "$clone_dir/spec" sparse-checkout set specification/wasm-1.0

commit="$(git -C "$clone_dir/spec" rev-parse HEAD)"
source_dir="$clone_dir/spec/specification/wasm-1.0"
[[ -d "$source_dir" ]] || die "upstream snapshot not found: specification/wasm-1.0"

cp -R "$source_dir/." "$stage_dir/"
shopt -s nullglob
spectec_files=("$stage_dir"/*.spectec)
(( ${#spectec_files[@]} > 0 )) || die "upstream snapshot contains no .spectec files"
shopt -u nullglob

sha256="$(snapshot_sha256 "$stage_dir")"
cat >"$stage_dir/REVISION" <<EOF
repository=$repository
commit=$commit
sha256=$sha256
EOF

verify_snapshot "$stage_dir"

if [[ -e "$destination" ]]; then
  mv -- "$destination" "$backup_dir"
  restore_backup=true
fi

mv -- "$stage_dir" "$destination"
stage_dir=""
restore_backup=false

if [[ -e "$backup_dir" ]]; then
  rm -rf -- "$backup_dir"
  backup_dir=""
fi

echo "Updated $destination"
echo "Upstream commit: $commit"
echo "Snapshot SHA-256: $sha256"
