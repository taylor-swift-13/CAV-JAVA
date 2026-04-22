#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ $# -lt 1 ]]; then
  printf 'Usage: %s <Java file> [openjml args...]\n' "$0" >&2
  exit 2
fi

java_file="$1"
shift

if [[ "$java_file" != /* ]]; then
  java_file="$repo_root/$java_file"
fi

if [[ ! -f "$java_file" ]]; then
  printf 'Java file not found: %s\n' "$java_file" >&2
  exit 2
fi

# shellcheck source=env-openjml.sh
source "$repo_root/scripts/env-openjml.sh"

openjml -esc "$@" "$java_file"
