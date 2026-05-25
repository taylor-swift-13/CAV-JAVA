#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONTRACT_SCRIPT="$ROOT/scripts/run_contract.py"
VERIFY_SCRIPT="$ROOT/scripts/run_verify.py"

EXPORT_EXAMPLES=1
JOBS=1

usage() {
  cat <<'EOF'
usage: run_pipeline_many.sh [--no-export-examples] [--jobs N|-j N] <name1> [name2 ...]

For each <name>, run:
  1. python3 scripts/run_contract.py raw/<name>.md --function-name <name>
  2. python3 scripts/run_verify.py input/<name>.c --function-name <name> [--export-examples]

Options:
  --no-export-examples   Do not pass --export-examples to verify.
  --jobs N, -j N         Run up to N names concurrently. Default: 1.
EOF
}

NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-export-examples)
      EXPORT_EXAMPLES=0
      shift
      ;;
    --jobs|-j)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      JOBS="$2"
      shift 2
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

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "--jobs must be a positive integer: $JOBS" >&2
  exit 2
fi

cd "$ROOT"

RUN_ID="$(date +%Y%m%d_%H%M%S)"
RUN_DIR="$ROOT/output/pipeline_many_${RUN_ID}"
mkdir -p "$RUN_DIR"

run_one() {
  local name="$1"
  RAW_PATH="raw/${name}.md"
  INPUT_PATH="input/${name}.c"

  if [[ ! -f "$RAW_PATH" ]]; then
    echo "[contract-verify-many] missing raw file: $RAW_PATH" >&2
    return 10
  fi

  echo "[contract-verify-many] contract start name=$name"
  if ! python3 "$CONTRACT_SCRIPT" "$RAW_PATH" --function-name "$name"; then
    echo "[contract-verify-many] contract failed name=$name" >&2
    return 20
  fi
  echo "[contract-verify-many] contract done name=$name"

  if [[ ! -f "$INPUT_PATH" ]]; then
    echo "[contract-verify-many] missing generated input after contract: $INPUT_PATH" >&2
    return 30
  fi

  VERIFY_CMD=(python3 "$VERIFY_SCRIPT" "$INPUT_PATH" --function-name "$name")
  if [[ $EXPORT_EXAMPLES -eq 1 ]]; then
    VERIFY_CMD+=(--export-examples)
  fi

  echo "[contract-verify-many] verify start name=$name"
  if ! "${VERIFY_CMD[@]}"; then
    echo "[contract-verify-many] verify failed name=$name" >&2
    return 40
  fi

  echo "[contract-verify-many] verify done name=$name"
}

status_label() {
  case "$1" in
    0) echo "success" ;;
    10) echo "missing_raw" ;;
    20) echo "contract" ;;
    30) echo "missing_input" ;;
    40) echo "verify" ;;
    *) echo "unknown_$1" ;;
  esac
}

FAILURES=()
SUCCESSES=()

if [[ "$JOBS" -eq 1 ]]; then
  for name in "${NAMES[@]}"; do
    if run_one "$name" 2>&1 | tee "$RUN_DIR/${name}.log"; then
      SUCCESSES+=("$name")
    else
      rc=${PIPESTATUS[0]}
      label="$(status_label "$rc")"
      FAILURES+=("$name:$label")
    fi
  done
else
  echo "[contract-verify-many] running with jobs=$JOBS log_dir=$RUN_DIR"
  for name in "${NAMES[@]}"; do
    while [[ "$(jobs -rp | wc -l)" -ge "$JOBS" ]]; do
      sleep 1
    done

    log="$RUN_DIR/${name}.log"
    status_file="$RUN_DIR/${name}.status"
    (
      set +e
      run_one "$name" >"$log" 2>&1
      rc=$?
      label="$(status_label "$rc")"
      printf '%s:%s\n' "$name" "$label" >"$status_file"
      exit 0
    ) &
    echo "[contract-verify-many] launched name=$name pid=$! log=$log"
  done

  wait

  for name in "${NAMES[@]}"; do
    status_file="$RUN_DIR/${name}.status"
    log="$RUN_DIR/${name}.log"
    if [[ ! -f "$status_file" ]]; then
      FAILURES+=("$name:missing_status")
      echo "[contract-verify-many] failed name=$name reason=missing_status log=$log" >&2
      continue
    fi

    status="$(<"$status_file")"
    label="${status#*:}"
    if [[ "$label" == "success" ]]; then
      SUCCESSES+=("$name")
      echo "[contract-verify-many] done name=$name log=$log"
    else
      FAILURES+=("$name:$label")
      echo "[contract-verify-many] failed name=$name reason=$label log=$log" >&2
    fi
  done
fi

echo "[contract-verify-many] summary: total=${#NAMES[@]} success=${#SUCCESSES[@]} failure=${#FAILURES[@]}"
echo "[contract-verify-many] logs: $RUN_DIR"

if [[ ${#SUCCESSES[@]} -gt 0 ]]; then
  echo "[contract-verify-many] successes:"
  for success in "${SUCCESSES[@]}"; do
    echo "  $success"
  done
fi

if [[ ${#FAILURES[@]} -gt 0 ]]; then
  echo "[contract-verify-many] failures:" >&2
  for failure in "${FAILURES[@]}"; do
    echo "  $failure" >&2
  done
  exit 1
fi

echo "[contract-verify-many] all done"
