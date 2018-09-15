if [ "$CI_PULL_REQUEST" = "7257" ] || [ "$CI_BRANCH" = "master+fix-yet-another-unif-dep-in-alphabet" ]; then
    cross_crypto_CI_REF=master+fix-coq7257-ascii-sensitive-unification
    cross_crypto_CI_GITURL=https://github.com/herbelin/cross-crypto
fi
