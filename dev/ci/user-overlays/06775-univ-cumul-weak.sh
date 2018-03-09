if [ "$CI_PULL_REQUEST" = "6775" ] || [ "$CI_BRANCH" = "univ-cumul" ]; then
    Elpi_CI_BRANCH=coq-master
    Elpi_CI_GITURL=https://github.com/SkySkimmer/coq-elpi.git
fi
