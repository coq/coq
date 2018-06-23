_OVERLAY_BRANCH=camlp5-parser

if [ "$CI_PULL_REQUEST" = "7902" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    ltac2_CI_BRANCH="$_OVERLAY_BRANCH"
    ltac2_CI_GITURL=https://github.com/ppedrot/ltac2

fi
