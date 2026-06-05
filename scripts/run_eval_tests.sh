#!/usr/bin/env bash
# Compare bc-lean's definitional interpreter against GNU bc for the checked-in
# POSIX reference programs.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.." || exit 1

if ! command -v bc >/dev/null 2>&1; then
  echo "Skipping eval tests: bc command not found" >&2
  exit 0
fi

TEMP_DIR="testResults-eval"
LOCK_DIR="$TEMP_DIR/.print_lock"
PROGRESS_FILE="$TEMP_DIR/.progress"
FUEL="${BC_LEAN_FUEL:-200000}"
SEMANTICS="${BC_LEAN_SEMANTICS:-big}"
BC_LEAN_EXE="${BC_LEAN_EXE:-.lake/build/bin/bc-lean}"
BC_LEAN_ASSUME_BUILT="${BC_LEAN_ASSUME_BUILT:-0}"

if command -v nproc >/dev/null 2>&1; then
  JOBS=$(nproc)
elif command -v sysctl >/dev/null 2>&1; then
  JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 1)
else
  JOBS=1
fi

print_usage() {
  echo "Usage: $0 [-j|--jobs N] [--semantics big|small] [test ...]"
  echo "  -j, --jobs N   Number of parallel executions (default: CPU count)"
  echo "  --semantics S  Semantics to test: big or small (default: $SEMANTICS)"
  echo "  test ...       Optional test paths; defaults to checked-in eval corpora"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -j|--jobs)
      JOBS="${2:-}"
      shift 2
      ;;
    --semantics)
      SEMANTICS="${2:-}"
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

case "$SEMANTICS" in
  big|big-step)
    SEMANTICS="big"
    ;;
  small|small-step)
    SEMANTICS="small"
    ;;
  *)
    echo "Error: --semantics must be 'big' or 'small'" >&2
    exit 1
    ;;
esac

cleanup() {
  local pids=()
  mapfile -t pids < <(jobs -pr)
  if [[ ${#pids[@]} -gt 0 ]]; then
    kill "${pids[@]}" 2>/dev/null || true
  fi
  rm -rf "$TEMP_DIR"
}

trap cleanup EXIT INT TERM

ensure_runtime_artifacts() {
  if [[ "$BC_LEAN_ASSUME_BUILT" != 1 || ! -x "$BC_LEAN_EXE" ]]; then
    echo "Building bc-lean executable..."
    lake build bc-lean
  fi

  if [[ ! -f config.json ]]; then
    echo "Building tree-sitter parser/config..."
    make parser
  fi
}

needs_mathlib() {
  local stem="${1%.*}"
  if [[ -f "$1.mathlib" || -f "$stem.mathlib" ]]; then
    return 0
  fi

  case "$1" in
    tests/Test/atan.b|tests/Test/checklib.b|tests/Test/exp.b|tests/Test/jn.b|\
    tests/Test/ln.b|tests/Test/sine.b)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

print_report() {
  local report_file="$1"
  local completed first_line
  while ! mkdir "$LOCK_DIR" 2>/dev/null; do
    sleep 0.05
  done
  completed=$(cat "$PROGRESS_FILE")
  completed=$((completed + 1))
  echo "$completed" >"$PROGRESS_FILE"

  first_line=$(head -n1 "$report_file")
  printf '[%d/%d] %s\n' "$completed" "$TOTAL_TESTS" "$first_line"
  tail -n +2 "$report_file"
  rmdir "$LOCK_DIR"
}

run_single_test() {
  local src="$1"
  local result_base lean_out ref_out lean_err ref_err report status
  local lean_code ref_code math_args=()

  result_base="${src#tests/}"
  result_base="${result_base//\//__}"
  lean_out="$TEMP_DIR/$result_base.lean.out"
  ref_out="$TEMP_DIR/$result_base.ref.out"
  lean_err="$TEMP_DIR/$result_base.lean.err"
  ref_err="$TEMP_DIR/$result_base.ref.err"
  report="$TEMP_DIR/$result_base.report"
  status="$TEMP_DIR/$result_base.status"

  if needs_mathlib "$src"; then
    math_args=(-l)
  fi

  "$BC_LEAN_EXE" --fuel "$FUEL" --semantics "$SEMANTICS" "${math_args[@]}" "$src" \
    </dev/null >"$lean_out" 2>"$lean_err"
  lean_code=$?

  if needs_mathlib "$src"; then
    bc -l "$src" </dev/null >"$ref_out" 2>"$ref_err"
  else
    bc "$src" </dev/null >"$ref_out" 2>"$ref_err"
  fi
  ref_code=$?

  if [[ $lean_code -eq $ref_code ]] && diff -q "$ref_out" "$lean_out" >/dev/null; then
    echo "Passed: $src" >"$report"
    echo "pass" >"$status"
  else
    {
      echo "Failed: $src"
      echo "Lean exit: $lean_code"
      echo "bc exit:   $ref_code"
      echo "Diff:"
      diff -u "$ref_out" "$lean_out" || true
      if [[ -s "$lean_err" ]]; then
        echo
        echo "bc-lean stderr:"
        cat "$lean_err"
      fi
      if [[ -s "$ref_err" ]]; then
        echo
        echo "bc stderr:"
        cat "$ref_err"
      fi
    } >"$report"
    echo "fail" >"$status"
  fi

  print_report "$report"
}

discover_tests() {
  local roots=(tests/Test tests/Examples tests/eval tests/external)
  local existing=()
  for root in "${roots[@]}"; do
    if [[ -d "$root" ]]; then
      existing+=("$root")
    fi
  done

  if [[ ${#existing[@]} -eq 0 ]]; then
    return 0
  fi

  find "${existing[@]}" -type f \( -name '*.b' -o -name '*.bc' \) | sort
}

mkdir -p "$TEMP_DIR"

PASS_COUNT=0
FAIL_COUNT=0
SKIP_COUNT=0
FAILED_TESTS=()

if [[ $# -gt 0 ]]; then
  test_files=("$@")
else
  mapfile -t test_files < <(discover_tests)
fi

if [[ ${#test_files[@]} -eq 0 ]]; then
  echo "No eval tests discovered" >&2
  exit 1
fi

for src in "${test_files[@]}"; do
  if [[ ! -f "$src" ]]; then
    echo "Error: Test file '$src' not found" >&2
    exit 1
  fi
done

ensure_runtime_artifacts

mkdir -p "$TEMP_DIR"
echo 0 >"$PROGRESS_FILE"
TOTAL_TESTS=${#test_files[@]}

echo "Running $TOTAL_TESTS eval tests with $JOBS job(s), fuel=$FUEL, semantics=$SEMANTICS"

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

echo ""
echo "==== Eval Test Summary ($SEMANTICS) ===="
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"
echo "Skipped: $SKIP_COUNT"
if (( FAIL_COUNT > 0 )); then
  echo "Failed tests:"
  printf ' - %s\n' "${FAILED_TESTS[@]}"
  exit 1
fi
