_OVERLAY_BRANCH=clean-transp-state

if [ "$CI_PULL_REQUEST" = "7925" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    unicoq_CI_REF="$_OVERLAY_BRANCH"
    unicoq_CI_GITURL=https://github.com/ppedrot/unicoq

    equations_CI_REF="$_OVERLAY_BRANCH"
    equations_CI_GITURL=https://github.com/ppedrot/Coq-Equations

    mtac2_CI_REF="$_OVERLAY_BRANCH"
    mtac2_CI_GITURL=https://github.com/ppedrot/Mtac2

fi
