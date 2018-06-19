_OVERLAY_BRANCH=rm-reference

if [ "$CI_PULL_REQUEST" = "7797" ] || [ "$CI_BRANCH" = "_OVERLAY_BRANCH" ]; then

    Equations_CI_BRANCH="$_OVERLAY_BRANCH"
    Equations_CI_GITURL=https://github.com/maximedenes/Coq-Equations.git

    ltac2_CI_BRANCH="fix-7797"
    ltac2_CI_GITURL=https://github.com/ppedrot/Ltac2.git

    quickchick_CI_BRANCH="$_OVERLAY_BRANCH"
    quickchick_CI_GITURL=https://github.com/maximedenes/QuickChick.git

    coq_dpdgraph_CI_BRANCH="$_OVERLAY_BRANCH"
    coq_dpdgraph_CI_GITURL=https://github.com/maximedenes/coq-dpdgraph.git

    Elpi_CI_BRANCH="$_OVERLAY_BRANCH"
    Elpi_CI_GITURL=https://github.com/maximedenes/coq-elpi.git

fi
