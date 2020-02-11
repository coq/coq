if [ "$CI_PULL_REQUEST" = "11235" ] || [ "$CI_BRANCH" = "non-maximal-implicit" ]; then

    quickchick_CI_REF=non_maximal_implicit
    quickchick_CI_GITURL=https://github.com/SimonBoulier/QuickChick

    elpi_CI_REF=non_maximal_implicit
    elpi_CI_GITURL=https://github.com/SimonBoulier/coq-elpi

fi
