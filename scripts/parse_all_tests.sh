#!/usr/bin/env bash
# Parse all bc reference test programs with tree-sitter.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CONFIG="$ROOT/config.json"
TS="${TS:-tree-sitter}"

if [[ ! -f "$CONFIG" ]]; then
  echo "error: $CONFIG not found; run 'make parser' first" >&2
  exit 1
fi

shopt -s globstar nullglob
files=()
for f in "$ROOT"/tests/**/*.b "$ROOT"/tests/**/*.bc; do
  case "$f" in
    "$ROOT"/tests/parse-invalid/*) continue ;;
    "$ROOT"/tests/semantics/*) continue ;;
  esac
  files+=("$f")
done

if [[ ${#files[@]} -eq 0 ]]; then
  echo "error: no .b or .bc files under tests/" >&2
  exit 1
fi

passed=0
failed=0
failures=()

for f in "${files[@]}"; do
  rel="${f#"$ROOT"/}"
  stat_out="$("$TS" parse -q --stat "$f" --config-path "$CONFIG" 2>&1)" || {
    echo "FAIL $rel (tree-sitter exit $?)"
    echo "$stat_out"
    failures+=("$rel")
    failed=$((failed + 1))
    continue
  }
  if echo "$stat_out" | grep -qiE 'error|ERROR'; then
    echo "FAIL $rel"
    echo "$stat_out"
    failures+=("$rel")
    failed=$((failed + 1))
    continue
  fi
  echo "ok   $rel"
  passed=$((passed + 1))
done

echo ""
echo "parse_all_tests: $passed passed, $failed failed (${#files[@]} total)"

if [[ $failed -gt 0 ]]; then
  echo "Failures:"
  printf '  %s\n' "${failures[@]}"
  exit 1
fi
