_OVERLAY_BRANCH=omega-lia

if [ "$CI_PULL_REQUEST" = "7878" ] || [ "$CI_BRANCH" = "_OVERLAY_BRANCH" ]; then

    CompCert_CI_BRANCH="$_OVERLAY_BRANCH"
    CompCert_CI_GITURL=https://github.com/maximedenes/CompCert.git

    bignums_CI_BRANCH="$_OVERLAY_BRANCH"
    bignums_CI_GITURL=https://github.com/maximedenes/bignums.git

    bedrock2_CI_BRANCH="$_OVERLAY_BRANCH"
    bedrock2_CI_GITURL=https://github.com/maximedenes/bedrock2.git

    CoLoR_CI_BRANCH="$_OVERLAY_BRANCH"
    CoLoR_CI_GITURL=https://github.com/maximedenes/color.git

    Flocq_CI_BRANCH="$_OVERLAY_BRANCH"
    Flocq_CI_GITURL=https://gitlab.inria.fr/mdenes/flocq.git

fi
