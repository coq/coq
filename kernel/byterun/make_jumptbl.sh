#!/usr/bin/env bash

sed -n -e '/^  /s/ \([A-Z]\)/ \&\&coq_lbl_\1/gp' -e '/^}/q' ${1} > ${2}
