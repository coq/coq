if [ "$CI_PULL_REQUEST" = "8855" ] || [ "$CI_BRANCH" = "master+more-search-options" ]; then

    coqhammer_CI_REF=master+adapt-pr8855-search-api
    coqhammer_CI_GITURL=https://github.com/herbelin/coqhammer

    coq_dpdgraph_CI_REF=coq-master+adapt-pr8855-search-api
    coq_dpdgraph_CI_GITURL=https://github.com/herbelin/coq-dpdgraph

fi
