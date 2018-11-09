_OVERLAY_BRANCH=name-abstract-univ-context

if [ "$CI_PULL_REQUEST" = "8601" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    Elpi_CI_REF="$_OVERLAY_BRANCH"
    Elpi_CI_GITURL=https://github.com/ppedrot/coq-elpi

    Equations_CI_REF="$_OVERLAY_BRANCH"
    Equations_CI_GITURL=https://github.com/ppedrot/Coq-Equations

fi
