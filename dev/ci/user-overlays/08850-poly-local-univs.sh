#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8850" ] || [ "$CI_BRANCH" = "poly-local-univs" ]; then
    formal_topology_CI_REF=poly-local-univs
    formal_topology_CI_GITURL=https://github.com/SkySkimmer/topology

    paramcoq_CI_REF=poly-local-univs
    paramcoq_CI_GITURL=https://github.com/SkySkimmer/paramcoq
fi
