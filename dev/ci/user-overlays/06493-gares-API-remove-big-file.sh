if [ "$CI_PULL_REQUEST" = "6493" ] || [ "$CI_BRANCH" = "API/remove-big-file" ]; then
    Equations_CI_BRANCH=API-removal
    Equations_CI_GITURL=https://github.com/gares/Coq-Equations.git
    coq_dpdgraph_CI_BRANCH=API-removal
    coq_dpdgraph_CI_GITURL=https://github.com/gares/coq-dpdgraph.git
    ltac2_CI_BRANCH=API-removal
    ltac2_CI_GITURL=https://github.com/gares/ltac2.git
fi
