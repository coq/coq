_OVERLAY_BRANCH=rm-implicit-tactic

if [ "$CI_PULL_REQUEST" = "8779" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    ltac2_CI_REF="$_OVERLAY_BRANCH"
    ltac2_CI_GITURL=https://github.com/ppedrot/ltac2

fi
