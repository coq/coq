#!/usr/bin/env bash

DOUT=misc/tmp_coqc_dash_o/
OUT=${DOUT}coqc_dash_o.vo


mkdir -p "${DOUT}"
rm -f "${OUT}"
$coqc misc/coqc_dash_o.v -o "${OUT}"
if [ ! -f "${OUT}" ]; then
  printf "coqc -o not working"
  exit 1
fi
rm -fr "${DOUT}"
exit 0
