if [ "$CI_PULL_REQUEST" = "13143" ] || [ "$CI_BRANCH" = "master+drop-misleading-arg-hbox" ]; then

    aac_tactics_CI_REF=master+adapt-coq-pr13143-hbox-no-argument
    aac_tactics_CI_GITURL=https://github.com/herbelin/aac-tactics

    equations_CI_REF=master+adapt-coq-pr13143-hbox-no-argument
    equations_CI_GITURL=https://github.com/herbelin/Coq-Equations

fi
