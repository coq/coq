#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7863" ] || [ "$CI_BRANCH" = "rm-sorts-contents" ]; then
    Elpi_CI_BRANCH=fix-sorts-contents
    Elpi_CI_GITURL=https://github.com/SkySkimmer/coq-elpi.git
fi
