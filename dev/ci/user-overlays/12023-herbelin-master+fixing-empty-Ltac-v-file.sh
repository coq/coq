if [ "$CI_PULL_REQUEST" = "12023" ] || [ "$CI_BRANCH" = "master+fixing-empty-Ltac-v-file" ]; then

    fiat_crypto_CI_REF=master+pr12023-atomic-tactic-now-qualified-in-ltac-file
    fiat_crypto_CI_GITURL=https://github.com/herbelin/fiat-crypto

    mtac2_CI_REF=master+pr12023-atomic-tactic-now-qualified-in-ltac-file
    mtac2_CI_GITURL=https://github.com/herbelin/Mtac2

    metacoq_CI_REF=master+pr12023-atomic-tactic-now-qualified-in-ltac-file
    metacoq_CI_GITURL=https://github.com/herbelin/template-coq

    unimath_CI_REF=master+pr12023-atomic-tactic-now-qualified-in-ltac-file
    unimath_CI_GITURL=https://github.com/herbelin/UniMath

fi
