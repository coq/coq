if [ "$CI_PULL_REQUEST" = "7136" ] || [ "$CI_BRANCH" = "evar-map-econstr" ]; then
    Equations_CI_BRANCH=8.9+alpha
    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations.git

    Elpi_CI_BRANCH=coq-7136
    Elpi_CI_GITURL=https://github.com/SkySkimmer/coq-elpi.git
fi
