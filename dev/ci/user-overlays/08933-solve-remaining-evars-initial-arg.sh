#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8933" ] || [ "$CI_BRANCH" = "solve-remaining-evars-initial-arg" ]; then
    plugin_tutorial_CI_REF=solve-remaining-evars-initial-arg
    plugin_tutorial_CI_GITURL=https://github.com/SkySkimmer/plugin_tutorials
fi
