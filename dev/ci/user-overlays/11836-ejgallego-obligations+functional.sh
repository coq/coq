if [ "$CI_PULL_REQUEST" = "11836" ] || [ "$CI_BRANCH" = "obligations+functional" ]; then

    mtac2_CI_REF=obligations+functional
    mtac2_CI_GITURL=https://github.com/ejgallego/Mtac2

    paramcoq_CI_REF=obligations+functional
    paramcoq_CI_GITURL=https://github.com/ejgallego/paramcoq

    equations_CI_REF=obligations+functional
    equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

    metacoq_CI_REF=obligations+functional
    metacoq_CI_GITURL=https://github.com/ejgallego/metacoq

    rewriter_CI_REF=obligations+functional
    rewriter_CI_GITURL=https://github.com/ejgallego/rewriter

fi
