#!/usr/bin/env bash

IN_V=coqc_cmdline.v
OUT_VO=coqc_cmdline.vo
OUT_VIO=coqc_cmdline.vio
OUT_VOS=coqc_cmdline.vos
OUT_VOK=coqc_cmdline.vok
OUT_GLOB=coqc_cmdline.glob
OUT="${OUT_VO} ${OUT_VIO} ${OUT_VOS} ${OUT_VOK} ${OUT_GLOB}"

rm -f ${OUT}

set -x

coqc ${IN_V} -vos
coqc ${IN_V} -vok
if [ ! -f ${OUT_VOK} ]; then
  echo "coqc -vok not working in -vos mode"
  rm -f ${OUT}
  exit 1
fi

rm -f ${OUT}

coqc ${IN_V} -o ${OUT_VO}
if [ ! -f ${OUT_VOK} ]; then
  echo "vok not produced in -o mode"
  rm -f ${OUT}
  exit 1
fi

rm -f ${OUT}

coqc ${IN_V} -vio
coqc -vio2vo ${OUT_VIO}
if [ ! -f ${OUT_VOK} ]; then
  echo "vok not produced in -vio2vo mode"
  rm -f ${OUT}
  exit 1
fi

rm -f ${OUT}
exit 0
