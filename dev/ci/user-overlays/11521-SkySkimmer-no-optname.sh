if [ "$CI_PULL_REQUEST" = "11521" ] || [ "$CI_BRANCH" = "no-optname" ]; then

    coqhammer_CI_REF=no-optname
    coqhammer_CI_GITURL=https://github.com/SkySkimmer/coqhammer

    equations_CI_REF=no-optname
    equations_CI_GITURL=https://github.com/SkySkimmer/Coq-Equations

    unicoq_CI_REF=no-optname
    unicoq_CI_GITURL=https://github.com/SkySkimmer/unicoq

    paramcoq_CI_REF=no-optname
    paramcoq_CI_GITURL=https://github.com/SkySkimmer/paramcoq

fi
