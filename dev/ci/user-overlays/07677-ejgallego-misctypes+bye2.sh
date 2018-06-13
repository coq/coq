_OVERLAY_BRANCH=misctypes+bye2

if [ "$CI_PULL_REQUEST" = "7677" ] || [ "$CI_BRANCH" = "_OVERLAY_BRANCH" ]; then

    Equations_CI_BRANCH="$_OVERLAY_BRANCH"
    Equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

fi
