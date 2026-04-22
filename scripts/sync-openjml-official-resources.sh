#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
doc_dir="${OPENJML_DOC_DIR:-$repo_root/doc}"
examples_dir="${OPENJML_EXAMPLES_DIR:-$repo_root/examples}"
openjml_home="${OPENJML_HOME:-$repo_root/.tools/openjml/current}"

need_command() {
  if ! command -v "$1" >/dev/null 2>&1; then
    printf 'Required command not found: %s\n' "$1" >&2
    exit 1
  fi
}

need_command curl
need_command find
need_command unzip
need_command wget

curl_download() {
  local url="$1"
  local output="$2"

  curl \
    --fail \
    --location \
    --show-error \
    --retry 5 \
    --retry-delay 2 \
    --retry-connrefused \
    "$url" \
    --output "$output"
}

if [[ ! -x "$openjml_home/openjml" ]]; then
  "$repo_root/scripts/install-openjml.sh"
fi

version="$("$openjml_home/openjml" -version | awk '{print $2}')"
download_dir="$doc_dir/downloads"
site_tmp_dir="$(mktemp -d)"
userguide_zip="$download_dir/userguide-examples.zip"

trap 'rm -rf "$site_tmp_dir"' EXIT

mkdir -p "$doc_dir" "$download_dir" "$examples_dir"

copy_release_folder() {
  local name="$1"
  local dst="$2"
  local src="$openjml_home/$name"

  if [[ ! -d "$src" ]]; then
    printf 'OpenJML release folder not found: %s\n' "$src" >&2
    exit 1
  fi

  rm -rf "$dst"
  cp -a "$src" "$dst"
}

copy_release_folder demos "$examples_dir/openjml-demos"
copy_release_folder tutorial "$examples_dir/openjml-tutorial"
copy_release_folder specs "$doc_dir/openjml-specs"

curl_download \
  https://www.openjml.org/documentation/OpenJMLUserGuide.pdf \
  "$doc_dir/OpenJMLUserGuide.pdf"

curl_download \
  https://www.openjml.org/documentation/JML_Reference_Manual.pdf \
  "$doc_dir/JML_Reference_Manual.pdf"

curl_download \
  https://www.openjml.org/examples/userguide-examples.zip \
  "$userguide_zip"

rm -rf "$examples_dir/openjml-userguide"
mkdir -p "$examples_dir/openjml-userguide"
unzip -q "$userguide_zip" -d "$examples_dir/openjml-userguide"

download_site_section() {
  local url="$1"
  local status

  printf 'Mirroring %s\n' "$url"
  set +e
  wget \
    --no-verbose \
    --recursive \
    --level=2 \
    --no-parent \
    --page-requisites \
    --convert-links \
    --adjust-extension \
    --domains www.openjml.org \
    --directory-prefix "$site_tmp_dir" \
    "$url"
  status="$?"
  set -e

  if [[ "$status" -ne 0 ]]; then
    printf 'Warning: wget returned %s while mirroring %s; keeping successfully downloaded files.\n' "$status" "$url" >&2
  fi
}

download_site_section https://www.openjml.org/documentation/
download_site_section https://www.openjml.org/examples/
download_site_section https://www.openjml.org/tutorial/

rm -rf "$doc_dir/openjml-documentation" "$doc_dir/openjml-tutorial" "$examples_dir/openjml-web-examples"
mkdir -p "$doc_dir/openjml-documentation" "$doc_dir/openjml-tutorial" "$examples_dir/openjml-web-examples"

if [[ -d "$site_tmp_dir/www.openjml.org/documentation" ]]; then
  cp -a "$site_tmp_dir/www.openjml.org/documentation/." "$doc_dir/openjml-documentation/"
fi

if [[ -d "$site_tmp_dir/www.openjml.org/tutorial" ]]; then
  cp -a "$site_tmp_dir/www.openjml.org/tutorial/." "$doc_dir/openjml-tutorial/"
fi

if [[ -d "$site_tmp_dir/www.openjml.org/examples" ]]; then
  cp -a "$site_tmp_dir/www.openjml.org/examples/." "$examples_dir/openjml-web-examples/"
fi

cat > "$doc_dir/README.md" <<EOF
# OpenJML Docs

Downloaded and copied by \`./scripts/sync-openjml-official-resources.sh\`.

Source release: OpenJML $version

## Contents

- \`OpenJMLUserGuide.pdf\`: OpenJML User Guide from the official documentation site.
- \`JML_Reference_Manual.pdf\`: JML Reference Manual from the official documentation site.
- \`openjml-documentation\`: mirrored official documentation pages.
- \`openjml-tutorial\`: mirrored official tutorial pages.
- \`openjml-specs\`: JML specification files bundled with the OpenJML release.
- \`downloads/userguide-examples.zip\`: official User Guide examples archive.

## Sources

- https://www.openjml.org/documentation/
- https://www.openjml.org/tutorial/
- https://github.com/OpenJML/OpenJML/releases

Check the upstream pages and files for their applicable licenses and copyright terms.
EOF

cat > "$examples_dir/README.md" <<EOF
# Examples

## Local Examples

- \`Counter.java\`: small local smoke-test example used by \`./scripts/check-openjml.sh\`.

## Official OpenJML Examples

Downloaded and copied by \`./scripts/sync-openjml-official-resources.sh\`.

Source release: OpenJML $version

- \`openjml-demos\`: examples bundled with the OpenJML release.
- \`openjml-tutorial\`: tutorial source examples bundled with the OpenJML release.
- \`openjml-userguide\`: extracted official User Guide examples.
- \`openjml-web-examples\`: mirrored official examples pages.

Sources:

- https://www.openjml.org/examples/
- https://www.openjml.org/tutorial/
- https://github.com/OpenJML/OpenJML/releases

The OpenJML examples page states that its examples may be used and revised for
non-commercial purposes with reasonable source credit under CC BY-NC 4.0.
EOF

printf 'OpenJML docs synchronized into %s\n' "$doc_dir"
printf 'OpenJML examples synchronized into %s\n' "$examples_dir"
printf 'Doc files: %s\n' "$(find "$doc_dir" -type f | wc -l | tr -d ' ')"
printf 'Example files: %s\n' "$(find "$examples_dir" -type f | wc -l | tr -d ' ')"
