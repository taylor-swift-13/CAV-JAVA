#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONTRACT_SCRIPT="$ROOT/scripts/run_codex_contract.py"
VERIFY_SCRIPT="$ROOT/scripts/run_codex_verify.py"
EVAL_SCRIPT="$ROOT/scripts/run_codex_eval.py"

RUN_EVAL=0
EXPORT_EXAMPLES=1
TIMEOUT_SECONDS=3600
JOBS=1

usage() {
  cat <<'EOF'
usage: run_codex_verify_many.sh [--eval] [--no-export-examples] [--timeout-seconds N] [--jobs N|-j N] <name1> [name2 ...]

For each <name>, run:
  1. python3 scripts/run_codex_contract.py raw/<name>.md --function-name <name>
  2. optionally: python3 scripts/run_codex_eval.py input/<name>.java --class-name <PascalName> --method-name <name>
  3. python3 scripts/run_codex_verify.py input/<name>.java --class-name <PascalName> [--export-examples]

Options:
  --eval                Run eval between contract and verify.
  --no-export-examples  Do not pass --export-examples to verify.
  --timeout-seconds N   Timeout passed to each contract/verify/eval Codex run. Default: 3600.
  --jobs N, -j N        Run up to N names concurrently. Default: 1.
EOF
}

pascal_name() {
  local stem="$1"
  printf '%s' "$stem" | awk -F_ '{for (i=1; i<=NF; ++i) printf toupper(substr($i,1,1)) substr($i,2)}'
}

NAMES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --eval)
      RUN_EVAL=1
      shift
      ;;
    --no-export-examples)
      EXPORT_EXAMPLES=0
      shift
      ;;
    --timeout-seconds)
      if [[ $# -lt 2 ]]; then
        echo "missing value for $1" >&2
        usage >&2
        exit 2
      fi
      TIMEOUT_SECONDS="$2"
      shift 2
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

if ! [[ "$TIMEOUT_SECONDS" =~ ^[0-9]+$ ]] || [[ "$TIMEOUT_SECONDS" -lt 1 ]]; then
  echo "--timeout-seconds must be a positive integer: $TIMEOUT_SECONDS" >&2
  exit 2
fi

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "--jobs must be a positive integer: $JOBS" >&2
  exit 2
fi

cd "$ROOT"

RUN_ID="$(date +%Y%m%d_%H%M%S)"
TMP_ROOT="${TMPDIR:-/tmp}"
BATCH_TMP="$(mktemp -d "$TMP_ROOT/cav-java-verify-many_${RUN_ID}.XXXXXX")"
trap 'rm -rf "$BATCH_TMP"' EXIT

run_one() {
  local name="$1"
  local raw_path="raw/${name}.md"
  local input_path="input/${name}.java"
  local class_name
  class_name="$(pascal_name "$name")"

  if [[ ! -f "$raw_path" ]]; then
    echo "[contract-verify-many] missing raw file: $raw_path" >&2
    return 10
  fi

  echo "[contract-verify-many] contract start name=$name"
  if ! python3 "$CONTRACT_SCRIPT" "$raw_path" --function-name "$name" --workspace-name "$name" --timeout-seconds "$TIMEOUT_SECONDS"; then
    echo "[contract-verify-many] contract failed name=$name" >&2
    return 20
  fi
  echo "[contract-verify-many] contract done name=$name"

  if [[ ! -f "$input_path" ]]; then
    echo "[contract-verify-many] missing generated input after contract: $input_path" >&2
    return 30
  fi

  if [[ "$RUN_EVAL" -eq 1 ]]; then
    echo "[contract-verify-many] eval start name=$name class=$class_name"
    if ! python3 "$EVAL_SCRIPT" "$input_path" --class-name "$class_name" --method-name "$name" --timeout-seconds "$TIMEOUT_SECONDS"; then
      echo "[contract-verify-many] eval failed name=$name" >&2
      return 40
    fi
    echo "[contract-verify-many] eval done name=$name"
  fi

  verify_cmd=(python3 "$VERIFY_SCRIPT" "$input_path" --class-name "$class_name" --timeout-seconds "$TIMEOUT_SECONDS")
  if [[ "$EXPORT_EXAMPLES" -eq 1 ]]; then
    verify_cmd+=(--export-examples)
  fi

  echo "[contract-verify-many] verify start name=$name class=$class_name export=$EXPORT_EXAMPLES"
  if ! "${verify_cmd[@]}"; then
    echo "[contract-verify-many] verify failed name=$name" >&2
    return 50
  fi
  echo "[contract-verify-many] verify done name=$name"
}

status_label() {
  case "$1" in
    0) echo "success" ;;
    10) echo "missing_raw" ;;
    20) echo "contract" ;;
    30) echo "missing_input" ;;
    40) echo "eval" ;;
    50) echo "verify" ;;
    *) echo "unknown_$1" ;;
  esac
}

FAILURES=()
SUCCESSES=()

if [[ "$JOBS" -eq 1 ]]; then
  for name in "${NAMES[@]}"; do
    if run_one "$name"; then
      SUCCESSES+=("$name")
    else
      rc=$?
      label="$(status_label "$rc")"
      FAILURES+=("$name:$label")
    fi
  done
else
  echo "[contract-verify-many] running with jobs=$JOBS"
  for name in "${NAMES[@]}"; do
    while [[ "$(jobs -rp | wc -l)" -ge "$JOBS" ]]; do
      sleep 1
    done

    log="$BATCH_TMP/${name}.log"
    status_file="$BATCH_TMP/${name}.status"
    (
      set +e
      run_one "$name" >"$log" 2>&1
      rc=$?
      label="$(status_label "$rc")"
      printf '%s:%s\n' "$name" "$label" >"$status_file"
      exit 0
    ) &
    echo "[contract-verify-many] launched name=$name pid=$!"
  done

  wait

  for name in "${NAMES[@]}"; do
    status_file="$BATCH_TMP/${name}.status"
    log="$BATCH_TMP/${name}.log"
    if [[ -f "$log" ]]; then
      sed "s/^/[contract-verify-many][$name] /" "$log"
    fi

    if [[ ! -f "$status_file" ]]; then
      FAILURES+=("$name:missing_status")
      echo "[contract-verify-many] failed name=$name reason=missing_status" >&2
      continue
    fi

    status="$(<"$status_file")"
    label="${status#*:}"
    if [[ "$label" == "success" ]]; then
      SUCCESSES+=("$name")
      echo "[contract-verify-many] done name=$name"
    else
      FAILURES+=("$name:$label")
      echo "[contract-verify-many] failed name=$name reason=$label" >&2
    fi
  done
fi

echo "[contract-verify-many] summary: total=${#NAMES[@]} success=${#SUCCESSES[@]} failure=${#FAILURES[@]} eval=$RUN_EVAL export=$EXPORT_EXAMPLES"

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
