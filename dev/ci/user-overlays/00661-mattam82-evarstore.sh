#!/bin/sh

if [ "$CI_PULL_REQUEST" = "661" ] || [ "$CI_BRANCH" = "evarstore" ]; then
    ltac2_CI_REF=evarstore
    ltac2_CI_GITURL=https://github.com/mattam82/ltac2
fi
