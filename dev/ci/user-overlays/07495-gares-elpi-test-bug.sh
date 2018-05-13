if [ "$CI_PULL_REQUEST" = "7495" ] || [ "$CI_BRANCH" = "fix-restrict" ]; then

    # this branch contains a commit not present on coq-master that triggers
    # the universe restriction bug #7472
    Elpi_CI_BRANCH=overlay-7495
    Elpi_CI_GITURL=https://github.com/LPCIC/coq-elpi.git

fi
