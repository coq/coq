#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7908" ] || [ "$CI_BRANCH" = "proj-mind" ]; then
    Equations_CI_BRANCH=fix-proj-mind
    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations
fi
