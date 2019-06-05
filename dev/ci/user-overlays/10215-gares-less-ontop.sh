if [ "$CI_PULL_REQUEST" = "10215" ] || [ "$CI_BRANCH" = "custom-typing" ]; then

    equations_CI_REF=pass-less-ontop
    equations_CI_GITURL=https://github.com/gares/Coq-Equations

    mtac2_CI_REF=pass-less-ontop
    mtac2_CI_GITURL=https://github.com/SkySkimmer/Mtac2

    paramcoq_CI_REF=pass-less-ontop
    paramcoq_CI_GITURL=https://github.com/gares/paramcoq

    quickchick_CI_REF=pass-less-ontop
    quickchick_CI_GITURL=https://github.com/gares/QuickChick

fi
