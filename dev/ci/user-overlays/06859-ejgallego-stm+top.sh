#!/bin/sh

if [ "$CI_PULL_REQUEST" = "6859" ] || [ "$CI_BRANCH" = "stm+top" ] || [ "$CI_BRANCH" = "pr-6859" ]; then
    pidetop_CI_BRANCH=stm+top
    pidetop_CI_GITURL=https://bitbucket.org/ejgallego/pidetop.git
fi
