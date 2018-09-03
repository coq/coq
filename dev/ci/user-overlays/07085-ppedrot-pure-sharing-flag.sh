_OVERLAY_BRANCH=pure-sharing-flag

if [ "$CI_PULL_REQUEST" = "7085" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    mtac2_CI_BRANCH="$_OVERLAY_BRANCH"
    mtac2_CI_GITURL=https://github.com/ppedrot/Mtac2

fi
