#!/bin/sh

if [ "$CI_PULL_REQUEST" = "669" ] || [ "$CI_BRANCH" = "ssr-merge" ]; then
    mathcomp_CI_REF=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp
fi
