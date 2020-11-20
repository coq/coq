if [ "$CI_PULL_REQUEST" = "11390" ] || [ "$CI_BRANCH" = "master+fix-9412-context-implicits" ]; then

    fiat_crypto_legacy_CI_REF=master+adapt-coq-pr9412-ignored-implicit-context
    fiat_crypto_legacy_CI_GITURL=https://github.com/herbelin/fiat-crypto

    fiat_parsers_CI_REF=master+change-coq-pr9412-ignored-implicit-context
    fiat_parsers_CI_GITURL=https://github.com/herbelin/fiat

fi
