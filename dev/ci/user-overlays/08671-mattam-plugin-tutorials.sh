#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8741" ] || [ "$CI_BRANCH" = "typeclasses-functional-evar_map" ]; then
    plugin_tutorial_CI_REF=pr8671-fix
    plugin_tutorial_CI_GITURL=https://github.com/mattam82/plugin_tutorials

fi
