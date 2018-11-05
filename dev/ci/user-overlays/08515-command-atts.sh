#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8515" ] || [ "$CI_BRANCH" = "command-atts" ]; then
    ltac2_CI_REF=command-atts
    ltac2_CI_GITURL=https://github.com/SkySkimmer/ltac2

    Equations_CI_REF=command-atts
    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations

    plugin_tutorial_CI_REF=command-atts
    plugin_tutorial_CI_GITURL=https://github.com/SkySkimmer/plugin_tutorials
fi
