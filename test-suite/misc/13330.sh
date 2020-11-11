#!/usr/bin/env bash

coqc 13330/bug_13330.v
R=$?

if [ $R == 0 ]; then
  exit 1
else
  exit 0
fi
