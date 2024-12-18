#!/usr/bin/env bash

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

[ "$(rocq repl -print-mod-uid prerequisite/admit.vo)" = "prerequisite/.coq-native/NTestSuite_admit" ]
