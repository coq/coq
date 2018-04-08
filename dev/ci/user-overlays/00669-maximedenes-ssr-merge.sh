#!/bin/sh

if [ "$CI_PULL_REQUEST" = "669" ] || [ "$CI_BRANCH" = "ssr-merge" ]; then
    mathcomp_CI_BRANCH=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp.git
fi
