#!/usr/bin/env bash

set -ex

rm -f vio_checking{,bad}.{vo,vio}

coqc -vio vio_checking.v
coqc -vio vio_checking_bad.v

coqc -schedule-vio-checking 2 vio_checking.vio

if coqc -schedule-vio-checking 2 vio_checking_bad.vio; then
    echo 'vio-checking on vio_checking_bad.vio should have failed!'
    exit 1
fi
if coqc -schedule-vio-checking 2 vio_checking.vio vio_checking_bad.vio; then
    echo 'vio-checking on vio_checking vio_checking_bad.vio should have failed!'
    exit 1
fi

coqc -vio2vo vio_checking.vio
coqchk -silent vio_checking.vo

if coqc -vio2vo vio_checking_bad.vio; then
    echo 'vio2vo on vio_checking_bad.vio should have failed!'
    exit 1
fi
