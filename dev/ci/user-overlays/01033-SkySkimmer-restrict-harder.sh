if [ "$TRAVIS_PULL_REQUEST" = "1033" ] || [ "$TRAVIS_BRANCH" = "restrict-harder" ]; then
    formal_topology_CI_BRANCH=ci
    formal_topology_CI_GITURL=https://github.com/SkySkimmer/topology.git

    HoTT_CI_BRANCH=coq-pr-1033
    HoTT_CI_GITURL=https://github.com/SkySkimmer/HoTT.git

    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations.git
fi
