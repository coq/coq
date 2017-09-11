if [ "$TRAVIS_PULL_REQUEST" = "01044" ] || [ "$TRAVIS_BRANCH" = "make/dpdgraph" ]; then
    coq_dpdgraph_CI_BRANCH=patch-1
    coq_dpdgraph_CI_GITURL=https://github.com/gares/coq-dpdgraph.git
fi
