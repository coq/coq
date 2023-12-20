#!/usr/bin/env bash

IN_V=misc/coqc_cmdline.v
OUT_VO=misc/coqc_cmdline.vo
OUT_VOS=misc/coqc_cmdline.vos
OUT_VOK=misc/coqc_cmdline.vok
OUT_GLOB=misc/coqc_cmdline.glob
OUT="${OUT_VO} ${OUT_VOS} ${OUT_VOK} ${OUT_GLOB}"

rm -f ${OUT}

set -x

$coqc ${IN_V} -vos
$coqc ${IN_V} -vok
if [ ! -f ${OUT_VOK} ]; then
  echo "coqc -vok not working in -vos mode"
  rm -f ${OUT}
  exit 1
fi

rm -f ${OUT}

$coqc ${IN_V} -o ${OUT_VO}
if [ ! -f ${OUT_VOK} ]; then
  echo "vok not produced in -o mode"
  rm -f ${OUT}
  exit 1
fi

rm -f ${OUT}
exit 0
