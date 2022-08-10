#!/bin/sh
set -e

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

coqc_stm -R misc/quick-include/ QuickInclude -vio misc/quick-include/file1.v
coqc_stm -R misc/quick-include/ QuickInclude -vio misc/quick-include/file2.v
