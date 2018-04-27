if [ "$CI_PULL_REQUEST" = "7080" ] || [ "$CI_BRANCH" = "master+swapping-modules-constr-context" ]; then
    Equations_CI_BRANCH=master+adapting-coq-pr7080
    Equations_CI_GITURL=https://github.com/herbelin/Coq-Equations.git

    Elpi_CI_BRANCH=coq-master+adapting-coq-pr7080
    Elpi_CI_GITURL=https://github.com/herbelin/coq-elpi.git
fi
