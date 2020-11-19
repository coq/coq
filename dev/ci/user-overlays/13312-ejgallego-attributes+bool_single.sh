if [ "$CI_PULL_REQUEST" = "13312" ] || [ "$CI_BRANCH" = "attributes+bool_single" ]; then

    overlay unicoq https://github.com/ejgallego/unicoq attributes+bool_single
    overlay elpi https://github.com/ejgallego/coq-elpi attributes+bool_single

fi
