#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7746" ] || [ "$CI_BRANCH" = "cleanup-unused-various" ]; then
    Equations_CI_BRANCH="adapt-unused"
    Equations_CI_GITURL="https://github.com/SkySkimmer/Coq-Equations.git"
fi
