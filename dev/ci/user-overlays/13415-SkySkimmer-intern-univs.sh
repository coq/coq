if [ "$CI_PULL_REQUEST" = "13415" ] || [ "$CI_BRANCH" = "intern-univs" ]; then

    overlay equations https://github.com/SkySkimmer/Coq-Equations intern-univs

    overlay paramcoq https://github.com/SkySkimmer/paramcoq intern-univs

    overlay elpi https://github.com/SkySkimmer/coq-elpi intern-univs
fi
