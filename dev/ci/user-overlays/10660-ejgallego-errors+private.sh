if [ "$CI_PULL_REQUEST" = "10660" ] || [ "$CI_BRANCH" = "errors+private" ]; then

    coqhammer_CI_REF=errors+private
    coqhammer_CI_GITURL=https://github.com/ejgallego/coqhammer

fi
