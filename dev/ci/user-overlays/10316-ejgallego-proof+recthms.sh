if [ "$CI_PULL_REQUEST" = "10316" ] || [ "$CI_BRANCH" = "proof+recthms" ]; then

    elpi_CI_REF=proof+recthms
    elpi_CI_GITURL=https://github.com/ejgallego/coq-elpi

    equations_CI_REF=proof+recthms
    equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

    mtac2_CI_REF=proof+recthms
    mtac2_CI_GITURL=https://github.com/ejgallego/Mtac2

    paramcoq_CI_REF=proof+recthms
    paramcoq_CI_GITURL=https://github.com/ejgallego/paramcoq

    quickchick_CI_REF=proof+recthms
    quickchick_CI_GITURL=https://github.com/ejgallego/QuickChick

fi
