if [ "$CI_PULL_REQUEST" = "7558" ] || [ "$CI_BRANCH" = "vernac+move_parser" ]; then

    _OVERLAY_BRANCH=vernac+move_parser

    Equations_CI_BRANCH="$_OVERLAY_BRANCH"
    Equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

    ltac2_CI_BRANCH="$_OVERLAY_BRANCH"
    ltac2_CI_GITURL=https://github.com/ejgallego/ltac2

    mtac2_CI_BRANCH="$_OVERLAY_BRANCH"
    mtac2_CI_GITURL=https://github.com/ejgallego/Mtac2

fi
