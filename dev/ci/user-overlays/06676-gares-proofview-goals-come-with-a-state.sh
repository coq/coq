if [ "$CI_PULL_REQUEST" = "6676" ] || [ "$CI_BRANCH" = "proofview/goal-w-state" ]; then
    ltac2_CI_BRANCH=fix-for/6676
    ltac2_CI_GITURL=https://github.com/gares/ltac2.git
    Equations_CI_BRANCH=fix-for/6676
    Equations_CI_GITURL=https://github.com/gares/Coq-Equations.git
fi
