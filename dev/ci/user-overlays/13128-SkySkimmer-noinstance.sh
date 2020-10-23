if [ "$CI_PULL_REQUEST" = "13128" ] || [ "$CI_BRANCH" = "noinstance" ]; then

    overlay elpi https://github.com/SkySkimmer/coq-elpi noinstance

fi
