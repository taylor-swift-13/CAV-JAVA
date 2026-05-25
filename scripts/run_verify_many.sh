#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERIFY_SCRIPT="$ROOT/scripts/run_verify.py"
EXPORT_EXAMPLES=1

usage() {
  cat <<'EOF'
usage: run_verify_many.sh [--no-export-examples] <name1> [name2 ...]

For each <name>, run:
  python3 scripts/run_verify.py input/<name>.c --function-name <name> [--export-examples]

Options:
  --no-export-examples   Do not pass --export-examples to verify.
EOF
}

NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-export-examples)
      EXPORT_EXAMPLES=0
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      while [[ $# -gt 0 ]]; do
        NAMES+=("$1")
        shift
      done
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      NAMES+=("$1")
      shift
      ;;
  esac
done

if [[ ${#NAMES[@]} -lt 1 ]]; then
  usage >&2
  exit 2
fi

cd "$ROOT"

FAILURES=()
SUCCESSES=()

for name in "${NAMES[@]}"; do
  INPUT_PATH="input/${name}.c"

  if [[ ! -f "$INPUT_PATH" ]]; then
    echo "[verify-many] missing input file name=$name path=$INPUT_PATH" >&2
    FAILURES+=("$name:missing_input")
    continue
  fi

  echo "[verify-many] start name=$name"
  VERIFY_CMD=(python3 "$VERIFY_SCRIPT" "$INPUT_PATH" --function-name "$name")
  if [[ $EXPORT_EXAMPLES -eq 1 ]]; then
    VERIFY_CMD+=(--export-examples)
  fi

  if ! "${VERIFY_CMD[@]}"; then
    echo "[verify-many] failed name=$name" >&2
    FAILURES+=("$name:verify")
    continue
  fi

  SUCCESSES+=("$name")
  echo "[verify-many] done name=$name"
done

echo "[verify-many] summary: total=${#NAMES[@]} success=${#SUCCESSES[@]} failure=${#FAILURES[@]}"

if [[ ${#SUCCESSES[@]} -gt 0 ]]; then
  echo "[verify-many] successes:"
  for success in "${SUCCESSES[@]}"; do
    echo "  $success"
  done
fi

if [[ ${#FAILURES[@]} -gt 0 ]]; then
  echo "[verify-many] failures:" >&2
  for failure in "${FAILURES[@]}"; do
    echo "  $failure" >&2
  done
  exit 1
fi
