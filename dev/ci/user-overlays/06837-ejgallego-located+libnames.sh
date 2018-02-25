if [ "$CI_PULL_REQUEST" = "6837" ] || [ "$CI_BRANCH" = "located+libnames" ]; then

    ltac2_CI_BRANCH=located+libnames
    ltac2_CI_GITURL=https://github.com/ejgallego/ltac2

    Equations_CI_BRANCH=located+libnames
    Equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

    Elpi_CI_BRANCH=located+libnames
    Elpi_CI_GITURL=https://github.com/ejgallego/coq-elpi.git

    coq_dpdgraph_CI_BRANCH=located+libnames
    coq_dpdgraph_CI_GITURL=https://github.com/ejgallego/coq-dpdgraph.git

fi
