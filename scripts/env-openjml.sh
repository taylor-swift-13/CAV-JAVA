#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
openjml_home="${OPENJML_HOME:-$repo_root/.tools/openjml/current}"

if [[ ! -x "$openjml_home/openjml" ]]; then
  printf 'OpenJML is not installed at %s\n' "$openjml_home" >&2
  printf 'Run ./scripts/install-openjml.sh first.\n' >&2
  return 1 2>/dev/null || exit 1
fi

export OPENJML_HOME="$openjml_home"
export PATH="$OPENJML_HOME:$PATH"
