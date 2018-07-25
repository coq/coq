#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7859" ] || [ "$CI_BRANCH" = "rm-univ-broken-printing" ]; then
    Equations_CI_BRANCH=fix-printers
    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations
fi
