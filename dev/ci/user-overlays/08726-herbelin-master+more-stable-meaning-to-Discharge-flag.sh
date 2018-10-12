if [ "$CI_PULL_REQUEST" = "8726" ] || [ "$CI_BRANCH" = "master+more-stable-meaning-to-Discharge-flag" ]; then

    fiat_parsers_CI_BRANCH=master+change-for-coq-pr8726
    fiat_parsers_CI_REF=master+change-for-coq-pr8726
    fiat_parsers_CI_GITURL=https://github.com/herbelin/fiat

    elpi_CI_BRANCH=coq-master+fix-global-pr8726
    elpi_CI_REF=coq-master+fix-global-pr8726
    elpi_CI_GITURL=https://github.com/herbelin/coq-elpi

    equations_CI_BRANCH=master+fix-global-pr8726
    equations_CI_REF=master+fix-global-pr8726
    equations_CI_GITURL=https://github.com/herbelin/Coq-Equations

    mtac2_CI_BRANCH=master+fix-global-pr8726
    mtac2_CI_REF=master+fix-global-pr8726
    mtac2_CI_GITURL=https://github.com/herbelin/Mtac2

    paramcoq_CI_BRANCH=master+fix-global-pr8726
    paramcoq_CI_REF=master+fix-global-pr8726
    paramcoq_CI_GITURL=https://github.com/herbelin/paramcoq

fi
