#!/usr/bin/env bash
# Refresh tests/ast-expected/ goldens from bc-parse-test output.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

EXPECTED_DIR="tests/ast-expected"

if command -v nproc >/dev/null 2>&1; then
  JOBS=$(nproc)
elif command -v sysctl >/dev/null 2>&1; then
  JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 1)
else
  JOBS=1
fi

print_usage() {
  echo "Usage: $0 [-j|--jobs N]"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -j|--jobs)
      JOBS="${2:-}"
      shift 2
      ;;
    -h|--help)
      print_usage
      exit 0
      ;;
    -*)
      echo "Error: Unknown option '$1'" >&2
      print_usage
      exit 1
      ;;
    *)
      echo "Error: Unexpected argument '$1'" >&2
      print_usage
      exit 1
      ;;
  esac
done

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "Error: --jobs must be a positive integer" >&2
  exit 1
fi

expected_path_for() {
  local src="$1"
  local rel="${src#tests/}"
  if [[ "$rel" == constraints/* ]]; then
    echo "$EXPECTED_DIR/constraints/${rel#constraints/}"
  else
    echo "$EXPECTED_DIR/$rel"
  fi
}

process_file() {
  local src="$1"
  local dest_base temp_out
  dest_base=$(expected_path_for "$src")
  mkdir -p "$(dirname "$dest_base")"
  temp_out=$(mktemp)
  echo "Processing: $src"
  if lake exe bc-parse-test "$src" > "$temp_out" 2>&1; then
    rm -f "${dest_base}.fail"
    mv "$temp_out" "${dest_base}.output"
    echo "  ✓ ${dest_base}.output"
  else
    rm -f "${dest_base}.output"
    mv "$temp_out" "${dest_base}.fail"
    echo "  ✗ ${dest_base}.fail"
  fi
}

shopt -s globstar nullglob
files=()
for f in tests/**/*.b tests/**/*.bc; do
  files+=("$f")
done

active_jobs=0
for src in "${files[@]}"; do
  process_file "$src" &
  active_jobs=$((active_jobs + 1))
  if (( active_jobs >= JOBS )); then
    wait -n
    active_jobs=$((active_jobs - 1))
  fi
done

while (( active_jobs > 0 )); do
  wait -n
  active_jobs=$((active_jobs - 1))
done

echo "All AST expected files updated."
