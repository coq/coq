#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8844" ] || [ "$CI_BRANCH" = "split-tactics" ]; then
    Equations_CI_REF=split-tactics
    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations

    ltac2_CI_REF=split-tactics
    ltac2_CI_GITURL=https://github.com/SkySkimmer/ltac2

    fiat_parsers_CI_REF=split-tactics
    fiat_parsers_CI_GITURL=https://github.com/SkySkimmer/fiat
fi
