#!/usr/bin/env bash

set -ex

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc

rm -f vio_checking{,bad}.{vo,vio}

coqc_stm -vio vio_checking.v
coqc_stm -vio vio_checking_bad.v

coqc_stm -schedule-vio-checking 2 vio_checking.vio

if coqc_stm -schedule-vio-checking 2 vio_checking_bad.vio; then
    echo 'vio-checking on vio_checking_bad.vio should have failed!'
    exit 1
fi
if coqc_stm -schedule-vio-checking 2 vio_checking.vio vio_checking_bad.vio; then
    echo 'vio-checking on vio_checking vio_checking_bad.vio should have failed!'
    exit 1
fi

coqc_stm -vio2vo vio_checking.vio
coqchk -silent vio_checking.vo

if coqc_stm -vio2vo vio_checking_bad.vio; then
    echo 'vio2vo on vio_checking_bad.vio should have failed!'
    exit 1
fi
