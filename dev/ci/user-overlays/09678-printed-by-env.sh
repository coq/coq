
if [ "$CI_PULL_REQUEST" = "9678" ] || [ "$CI_BRANCH" = "printed-by-env" ]; then
    elpi_CI_REF=printed-by-env
    elpi_CI_GITURL=https://github.com/maximedenes/coq-elpi

    equations_CI_REF=printed-by-env
    equations_CI_GITURL=https://github.com/maximedenes/Coq-Equations

    ltac2_CI_REF=printed-by-env
    ltac2_CI_GITURL=https://github.com/maximedenes/ltac2

    quickchick_CI_REF=printed-by-env
    quickchick_CI_GITURL=https://github.com/maximedenes/QuickChick
fi
