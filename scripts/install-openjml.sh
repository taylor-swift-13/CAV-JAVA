#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
install_root="$repo_root/.tools/openjml"
api_url="https://api.github.com/repos/OpenJML/OpenJML/releases/latest"

need_command() {
  if ! command -v "$1" >/dev/null 2>&1; then
    printf 'Required command not found: %s\n' "$1" >&2
    exit 1
  fi
}

need_command curl
need_command python3
need_command unzip
need_command sha256sum

os="$(uname -s)"
case "$os" in
  Linux)
    asset_pattern='openjml-ubuntu-22.04-*.zip'
    platform_id='ubuntu-22.04'
    ;;
  Darwin)
    asset_pattern='openjml-macos-*.zip'
    platform_id='macos'
    ;;
  *)
    printf 'Unsupported OS for automatic OpenJML install: %s\n' "$os" >&2
    exit 1
    ;;
esac

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

release_json="$tmp_dir/release.json"
curl --fail --location --silent --show-error "$api_url" --output "$release_json"

release_info="$(
  ASSET_PATTERN="$asset_pattern" python3 - "$release_json" <<'PY'
import fnmatch
import json
import os
import sys

with open(sys.argv[1], "r", encoding="utf-8") as handle:
    release = json.load(handle)

pattern = os.environ["ASSET_PATTERN"]
for asset in release.get("assets", []):
    name = asset.get("name", "")
    if fnmatch.fnmatch(name, pattern):
        digest = asset.get("digest", "")
        sha256 = digest.removeprefix("sha256:") if digest.startswith("sha256:") else ""
        print(release["tag_name"])
        print(name)
        print(asset["browser_download_url"])
        print(sha256)
        break
else:
    raise SystemExit(f"No release asset matched {pattern!r}")
PY
)"

tag="$(printf '%s\n' "$release_info" | sed -n '1p')"
asset_name="$(printf '%s\n' "$release_info" | sed -n '2p')"
asset_url="$(printf '%s\n' "$release_info" | sed -n '3p')"
expected_sha256="$(printf '%s\n' "$release_info" | sed -n '4p')"
install_dir="$install_root/$tag-$platform_id"
zip_path="$tmp_dir/$asset_name"
extract_dir="$tmp_dir/extract"

if [[ -x "$install_dir/openjml" ]]; then
  ln -sfn "$install_dir" "$install_root/current"
  printf 'OpenJML %s is already installed at %s\n' "$tag" "$install_dir"
  printf 'OPENJML_HOME=%s\n' "$install_root/current"
  exit 0
fi

mkdir -p "$install_root" "$extract_dir"

printf 'Downloading %s\n' "$asset_url"
curl --fail --location --show-error "$asset_url" --output "$zip_path"

if [[ -n "$expected_sha256" ]]; then
  actual_sha256="$(sha256sum "$zip_path" | awk '{print $1}')"
  if [[ "$actual_sha256" != "$expected_sha256" ]]; then
    printf 'SHA-256 mismatch for %s\n' "$asset_name" >&2
    printf 'Expected: %s\n' "$expected_sha256" >&2
    printf 'Actual:   %s\n' "$actual_sha256" >&2
    exit 1
  fi
fi

unzip -q "$zip_path" -d "$extract_dir"

openjml_dir="$(
  find "$extract_dir" -type f -name openjml -perm -111 -print -quit | xargs -r dirname
)"

if [[ -z "$openjml_dir" ]]; then
  printf 'Could not find openjml executable in %s\n' "$asset_name" >&2
  exit 1
fi

rm -rf "$install_dir"
mv "$openjml_dir" "$install_dir"
ln -sfn "$install_dir" "$install_root/current"

printf 'Installed OpenJML %s at %s\n' "$tag" "$install_dir"
printf 'Run: source ./scripts/env-openjml.sh\n'
