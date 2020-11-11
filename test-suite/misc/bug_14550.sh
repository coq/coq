#!/usr/bin/env bash

coqc bug_14550/bug_14550.v
R=$?

if [ $R == 0 ]; then
  exit 1
else
  exit 0
fi
