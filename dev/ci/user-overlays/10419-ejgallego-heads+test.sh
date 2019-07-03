if [ "$CI_PULL_REQUEST" = "10419" ] || [ "$CI_BRANCH" = "heads+test" ]; then

    elpi_CI_REF=heads+test
    elpi_CI_GITURL=https://github.com/ejgallego/coq-elpi

    equations_CI_REF=heads+test
    equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

    mtac2_CI_REF=heads+test
    mtac2_CI_GITURL=https://github.com/ejgallego/Mtac2

    paramcoq_CI_REF=heads+test
    paramcoq_CI_GITURL=https://github.com/ejgallego/paramcoq

    quickchick_CI_REF=heads+test
    quickchick_CI_GITURL=https://github.com/ejgallego/QuickChick

fi
