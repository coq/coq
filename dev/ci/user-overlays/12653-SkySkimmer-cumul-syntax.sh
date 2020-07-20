if [ "$CI_PULL_REQUEST" = "12653" ] || [ "$CI_BRANCH" = "cumul-syntax" ]; then

    overlay elpi https://github.com/SkySkimmer/coq-elpi cumul-syntax

    overlay equations https://github.com/SkySkimmer/Coq-Equations cumul-syntax

    overlay mtac2 https://github.com/SkySkimmer/Mtac2 cumul-syntax

    overlay paramcoq https://github.com/SkySkimmer/paramcoq cumul-syntax

    overlay rewriter https://github.com/SkySkimmer/rewriter cumul-syntax

    overlay metacoq https://github.com/SkySkimmer/metacoq cumul-syntax

fi
