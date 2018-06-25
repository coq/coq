#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7906" ] || [ "$CI_BRANCH" = "univs-of-constr-noseff" ]; then
    Equations_CI_BRANCH=fix-univs-of-constr
    Equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations.git

    Elpi_CI_BRANCH=fix-universes-of-constr
    Elpi_CI_GITURL=https://github.com/SkySkimmer/coq-elpi.git
fi
