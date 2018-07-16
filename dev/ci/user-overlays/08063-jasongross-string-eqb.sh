#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8063" ] || [ "$CI_BRANCH" = "string-eqb" ]; then
    quickchick_CI_BRANCH=fix-for-pr-8063
    quickchick_CI_GITURL=https://github.com/JasonGross/QuickChick
fi
