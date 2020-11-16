if [ "$CI_PULL_REQUEST" = "13386" ] || [ "$CI_BRANCH" = "master+fix9971-primproj-canonical-structure-on-evar-type" ]; then

    unicoq_CI_REF=master+adapting-coq-pr13386
    unicoq_CI_GITURL=https://github.com/herbelin/unicoq

    elpi_CI_REF=coq-master+adapting-coq-pr13386
    elpi_CI_GITURL=https://github.com/herbelin/coq-elpi

fi
