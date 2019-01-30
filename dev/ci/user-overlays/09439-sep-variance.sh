
if [ "$CI_PULL_REQUEST" = "9439" ] || [ "$CI_BRANCH" = "sep-variance" ]; then
    elpi_CI_REF=sep-variance
    elpi_CI_GITURL=https://github.com/SkySkimmer/coq-elpi

    equations_CI_REF=sep-variance
    equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations

    mtac2_CI_REF=sep-variance
    mtac2_CI_GITURL=https://github.com/SkySkimmer/mtac2

    paramcoq_CI_REF=sep-variance
    paramcoq_CI_GITURL=https://github.com/SkySkimmer/paramcoq
fi
