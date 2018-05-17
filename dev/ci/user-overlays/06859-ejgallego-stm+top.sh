#!/bin/sh

if [ "$CI_PULL_REQUEST" = "6859" ] || [ "$CI_BRANCH" = "stm+top"   ] ||     \
   [ "$CI_PULL_REQUEST" = "7543" ] || [ "$CI_BRANCH" = "ide+split" ] ; then

    pidetop_CI_BRANCH=stm+top
    pidetop_CI_GITURL=https://bitbucket.org/ejgallego/pidetop.git

fi
