if [ "$CI_PULL_REQUEST" = "8718" ] || [ "$CI_BRANCH" = "master+reorganization-hook" ]; then

    mtac2_CI_BRANCH=master-sync+adapt-coq8718-declaration-hooks
    mtac2_CI_REF=master-sync+adapt-coq8718-declaration-hooks
    mtac2_CI_GITURL=https://github.com/herbelin/Mtac2

    Equations_CI_BRANCH=master+adapt-coq8718-declaration-hooks
    Equations_CI_REF=master+adapt-coq8718-declaration-hooks
    Equations_CI_GITURL=https://github.com/herbelin/Coq-Equations

    Elpi_CI_BRANCH=coq-master+adapt-coq8718-declaration-hooks
    Elpi_CI_REF=coq-master+adapt-coq8718-declaration-hooks
    Elpi_CI_GITURL=https://github.com/herbelin/coq-elpi

fi
