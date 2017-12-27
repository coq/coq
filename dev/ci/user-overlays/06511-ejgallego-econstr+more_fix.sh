 if [ "$CI_PULL_REQUEST" = "6511" ] || [ "$CI_BRANCH" = "econstr+more_fix" ]; then
    ltac2_CI_BRANCH=econstr+more_fix
    ltac2_CI_GITURL=https://github.com/ejgallego/ltac2

    Equations_CI_BRANCH=econstr+more_fix
    Equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations
fi
