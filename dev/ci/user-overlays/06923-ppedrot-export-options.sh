if [ "$CI_PULL_REQUEST" = "6923" ] || [ "$CI_BRANCH" = "export-options" ]; then
    ltac2_CI_BRANCH=export-options
    ltac2_CI_GITURL=https://github.com/ppedrot/ltac2

    Equations_CI_BRANCH=export-options
    Equations_CI_GITURL=https://github.com/ppedrot/Coq-Equations
fi
