#!/usr/bin/env bash

DOUT=misc/tmp_coqc_cmdline/
OUT=${DOUT}coqc_cmdline.vo


mkdir -p "${DOUT}"
rm -f "${OUT}"
$coqc misc/coqc_cmdline.v -o "${OUT}"
if [ ! -f "${OUT}" ]; then
  printf "coqc -o not working"
  exit 1
fi
rm -fr "${DOUT}"
exit 0
