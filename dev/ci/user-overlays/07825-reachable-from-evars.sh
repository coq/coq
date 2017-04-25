if [ "$CI_PULL_REQUEST" = "7825" ] || [ "$CI_BRANCH" = "reachable-from-evars" ]; then

    fiat_crypto_legacy_CI_REF=fix-simple-refine
    fiat_crypto_legacy_CI_GITURL=https://github.com/maximedenes/fiat-crypto

    compcert_CI_REF=fix-refine-order
    compcert_CI_GITURL=https://github.com/maximedenes/CompCert

fi
