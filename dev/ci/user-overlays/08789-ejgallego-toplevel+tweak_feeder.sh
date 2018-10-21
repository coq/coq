#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8789" ] || [ "$CI_BRANCH" = "toplevel+tweak_feeder" ]; then

    pidetop_CI_REF=toplevel+tweak_feeder
    pidetop_CI_GITURL=https://bitbucket.org/ejgallego/pidetop

fi
