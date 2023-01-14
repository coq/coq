#!/usr/bin/env bash

[ "$(coqtop -print-mod-uid ../prerequisite/admit.vo)" = "../prerequisite/.coq-native/NTestSuite_admit" ]
