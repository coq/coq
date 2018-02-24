if [ "$CI_PULL_REQUEST" = "6745" ] || [ "$CI_BRANCH" = "located+vernac" ]; then
    ltac2_CI_BRANCH=located+vernac
    ltac2_CI_GITURL=https://github.com/ejgallego/ltac2

    Equations_CI_BRANCH=located+vernac
    Equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

    fiat_parsers_CI_BRANCH=located+vernac
    fiat_parsers_CI_GITURL=https://github.com/ejgallego/fiat

    Elpi_CI_BRANCH=located+vernac
    Elpi_CI_GITURL=https://github.com/ejgallego/coq-elpi.git
fi
