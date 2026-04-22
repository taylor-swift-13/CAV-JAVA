#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# shellcheck source=env-openjml.sh
source "$repo_root/scripts/env-openjml.sh"

openjml -version
openjml -esc "$repo_root/examples/Counter.java"
