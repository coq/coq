#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7254" ] || [ "$CI_BRANCH" = "inductive-params" ]; then
    # Should be backwards compatible
    cross_crypto_CI_BRANCH=uniform-hole-parameter
    cross_crypto_CI_GITURL=https://github.com/jashug/cross-crypto

    # Should be backwards compatible
    Equations_CI_BRANCH=uniform-parameter-formula
    Equations_CI_GITURL=https://github.com/jashug/Coq-Equations

    # Should be backwards compatible
    formal_topology_CI_BRANCH=patch_uniform_parameters
    formal_topology_CI_GITURL=https://github.com/jashug/topology

    # Should be backwards compatible
    CompCert_CI_BRANCH=patch_uniform_parameters
    CompCert_CI_GITURL=https://github.com/jashug/CompCert

    # Same as CompCert
    VST_CI_BRANCH=patch_uniform_parameters
    VST_CI_GITURL=https://github.com/jashug/VST

    # Should be backwards compatible
    fiat_crypto_CI_BRANCH=patch_uniform_parameters_2
    fiat_crypto_CI_GITURL=https://github.com/jashug/fiat-crypto

    # Should be backwards compatible
    fiat_parsers_CI_BRANCH=patch_uniform_parameters
    fiat_parsers_CI_GITURL=https://github.com/jashug/fiat
fi
