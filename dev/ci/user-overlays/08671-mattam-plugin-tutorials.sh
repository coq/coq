#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8671" ] || [ "$CI_BRANCH" = "evar_info-flags" ]; then
    plugin_tutorial_CI_REF=pr8671-fix
    plugin_tutorial_CI_GITURL=https://github.com/mattam82/plugin_tutorials

fi
