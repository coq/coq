if [ "$CI_PULL_REQUEST" = "10201" ] || [ "$CI_BRANCH" = "opaque-future-cleanup" ]; then

    coq_dpdgraph_CI_REF=opaque-future-cleanup
    coq_dpdgraph_CI_GITURL=https://github.com/ppedrot/coq-dpdgraph

    coqhammer_CI_REF=opaque-future-cleanup
    coqhammer_CI_GITURL=https://github.com/ppedrot/coqhammer

    elpi_CI_REF=opaque-future-cleanup
    elpi_CI_GITURL=https://github.com/ppedrot/coq-elpi

    paramcoq_CI_REF=opaque-future-cleanup
    paramcoq_CI_GITURL=https://github.com/ppedrot/paramcoq

fi
