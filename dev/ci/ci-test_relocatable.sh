#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

coqc="$(which coqc)"
coqlib="$(coqc -config | grep '^COQLIB=' | sed 's/^COQLIB=//')"
coqc_relative_path="$(realpath --relative-to="${CI_INSTALL_DIR}" "$coqc")"
coqlib_relative_path="$(realpath --relative-to="${CI_INSTALL_DIR}" "$coqlib")"
if [[ "$coqc_relative_path" == /* || "$coqc_relative_path" == ../* ]]; then
  >&2 printf "Error: coqc relative path should not start with '/' or '..': %s (from realpath --relative-to=%q %q)\n" "$coqc_relative_path" "$CI_INSTALL_DIR" "$coqc"
  exit 1
fi
TMP_CI_INSTALL_DIR="$(mktemp -d)"
rm -rf "${TMP_CI_INSTALL_DIR}"
mv "${CI_INSTALL_DIR}" "${TMP_CI_INSTALL_DIR}"
coqc="${TMP_CI_INSTALL_DIR}/${coqc_relative_path}"
coqlib="${TMP_CI_INSTALL_DIR}/${coqlib_relative_path}"

set -x

pushd /tmp
echo >tmp.v <<EOF
Definition foo := Set.
EOF

# check that various commands work after relocating the install directory
for args in "-nois -boot -coqlib $coqlib" "-nois -boot" ""; do
  "$coqc" $args -v || exit $?
  "$coqc" $args --version || exit $?
  "$coqc" $args -h || exit $?
  "$coqc" $args --help || exit $?
  "$coqc" $args -where || exit $?
  "$coqc" $args -config || exit $?
  "$coqc" $args tmp.v || exit $?
done

popd

mv "${TMP_CI_INSTALL_DIR}" "${CI_INSTALL_DIR}"
