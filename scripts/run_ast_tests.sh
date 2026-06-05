#!/usr/bin/env bash
# Run Lean AST golden tests (bc-parse-test vs tests/ast-expected/).
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

EXPECTED_DIR="tests/ast-expected"
TEMP_DIR="testResults"
LOCK_DIR="$TEMP_DIR/.print_lock"

if command -v nproc >/dev/null 2>&1; then
  JOBS=$(nproc)
elif command -v sysctl >/dev/null 2>&1; then
  JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 1)
else
  JOBS=1
fi

print_usage() {
  echo "Usage: $0 [-j|--jobs N] [test]"
  echo "  -j, --jobs N   Number of parallel executions (default: CPU count)"
  echo "  test           Optional test path or base name"
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
    --)
      shift
      break
      ;;
    -*)
      echo "Error: Unknown option '$1'" >&2
      print_usage
      exit 1
      ;;
    *)
      break
      ;;
  esac
done

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "Error: --jobs must be a positive integer" >&2
  exit 1
fi

cleanup() {
  local pids
  pids=$(jobs -pr)
  if [[ -n "$pids" ]]; then
    kill $pids 2>/dev/null || true
  fi
  rm -rf "$TEMP_DIR"
}

trap cleanup EXIT INT TERM

PASS_COUNT=0
FAIL_COUNT=0
SKIP_COUNT=0
FAILED_TESTS=()

expected_path_for() {
  local src="$1"
  local rel="${src#tests/}"
  if [[ "$rel" == constraints/* ]]; then
    echo "$EXPECTED_DIR/constraints/${rel#constraints/}"
  else
    echo "$EXPECTED_DIR/$rel"
  fi
}

discover_tests() {
  shopt -s globstar nullglob
  local -a found=()
  local f
  for f in tests/**/*.b tests/**/*.bc; do
    found+=("$f")
  done
  printf '%s\n' "${found[@]}"
}

run_single_test() {
  local src="$1"
  local base result_base expected expect_type result_file report_file status_file
  local exit_code diff_match pass

  base=$(basename "$src")
  base="${base%.b}"
  base="${base%.bc}"
  result_base="${src#tests/}"
  result_base="${result_base//\//__}"
  expected=$(expected_path_for "$src")
  result_file="$TEMP_DIR/$result_base.result"
  report_file="$TEMP_DIR/$result_base.report"
  status_file="$TEMP_DIR/$result_base.status"

  if [[ -f "${expected}.output" ]]; then
    expected="${expected}.output"
    expect_type="output"
  elif [[ -f "${expected}.fail" ]]; then
    expected="${expected}.fail"
    expect_type="fail"
  else
    echo "Skipping $base: no .output or .fail under $EXPECTED_DIR" >"$report_file"
    echo "skip" >"$status_file"
    print_report "$report_file"
    return 0
  fi

  lake exe bc-parse-test "$src" > "$result_file" 2>&1
  exit_code=$?

  if diff -q "$result_file" "$expected" >/dev/null; then
    diff_match=1
  else
    diff_match=0
  fi

  pass=0
  if [[ $expect_type == "output" && $exit_code -eq 0 && $diff_match -eq 1 ]]; then
    pass=1
  elif [[ $expect_type == "fail" && $exit_code -ne 0 && $diff_match -eq 1 ]]; then
    pass=1
  fi

  if [[ $pass -eq 1 ]]; then
    echo "Passed: $base" >"$report_file"
    echo "pass" >"$status_file"
  else
    {
      echo
      echo "Failed: $base"
      echo "**************************"
      echo "Expected ($expected):"
      cat "$expected"
      echo
      echo "--------------------------"
      echo
      echo "Actual ($result_file):"
      cat "$result_file"
      echo
      echo "Diff:"
      diff -u "$expected" "$result_file" || true
      echo "**************************"
    } >"$report_file"
    echo "fail" >"$status_file"
  fi

  print_report "$report_file"
}

print_report() {
  local report_file="$1"
  while ! mkdir "$LOCK_DIR" 2>/dev/null; do
    sleep 0.05
  done
  cat "$report_file"
  rmdir "$LOCK_DIR"
}

if [[ $# -gt 0 ]]; then
  test_arg="$1"
  if [[ "$test_arg" == /* ]]; then
    test_files=("$test_arg")
  elif [[ -f "$test_arg" ]]; then
    test_files=("$test_arg")
  elif [[ -f "tests/$test_arg" ]]; then
    test_files=("tests/$test_arg")
  elif [[ -f "tests/constraints/$test_arg" ]]; then
    test_files=("tests/constraints/$test_arg")
  elif [[ -f "tests/constraints/$test_arg.b" ]]; then
    test_files=("tests/constraints/$test_arg.b")
  else
    echo "Error: Test file '$test_arg' not found" >&2
    exit 1
  fi
else
  mapfile -t test_files < <(discover_tests)
fi

mkdir -p "$TEMP_DIR"
active_jobs=0
for src in "${test_files[@]}"; do
  run_single_test "$src" &
  ((active_jobs++))
  if (( active_jobs >= JOBS )); then
    wait -n
    ((active_jobs--))
  fi
done

while (( active_jobs > 0 )); do
  wait -n
  ((active_jobs--))
done

for status_file in "$TEMP_DIR"/*.status; do
  [[ -f "$status_file" ]] || continue
  status=$(cat "$status_file")
  base_name=$(basename "$status_file" .status)
  case "$status" in
    pass) ((PASS_COUNT++)) ;;
    fail)
      ((FAIL_COUNT++))
      FAILED_TESTS+=("$base_name")
      ;;
    skip) ((SKIP_COUNT++)) ;;
  esac
done

rm -rf "$TEMP_DIR"

echo ""
echo "==== AST Test Summary ===="
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"
echo "Skipped: $SKIP_COUNT"
if (( FAIL_COUNT > 0 )); then
  echo "Failed tests:"
  printf ' - %s\n' "${FAILED_TESTS[@]}"
  exit 1
fi
