if [ "$CI_PULL_REQUEST" = "10362" ] || [ "$CI_BRANCH" = "delay-poly-opaque" ]; then

    paramcoq_CI_REF=delay-poly-opaque
    paramcoq_CI_GITURL=https://github.com/ppedrot/paramcoq

    elpi_CI_REF=delay-poly-opaque
    elpi_CI_GITURL=https://github.com/ppedrot/coq-elpi

    coqhammer_CI_REF=delay-poly-opaque
    coqhammer_CI_GITURL=https://github.com/ppedrot/coqhammer

    coq_dpdgraph_CI_REF=delay-poly-opaque
    coq_dpdgraph_CI_GITURL=https://github.com/ppedrot/coq-dpdgraph

fi
