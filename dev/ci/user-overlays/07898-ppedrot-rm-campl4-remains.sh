_OVERLAY_BRANCH=rm-campl4-remains

if [ "$CI_PULL_REQUEST" = "7898" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    pidetop_CI_BRANCH="$_OVERLAY_BRANCH"
    pidetop_CI_GITURL=https://github.com/ppedrot/pidetop

fi
