if [ "$CI_PULL_REQUEST" = "11992" ] || [ "$CI_BRANCH" = "no-reexports" ] || [ "$CI_BRANCH" = "no-reexports.r" ]; then

    compcert_CI_REF=no-reexports
    compcert_CI_GITURL=https://github.com/llelf/CompCert

    color_CI_REF=no-reexports
    color_CI_GITURL=https://github.com/llelf/color

    math_classes_CI_REF=no-reexports
    math_classes_CI_GITURL=https://github.com/llelf/math-classes

    equations_CI_REF=no-reexports
    equations_CI_GITURL=https://github.com/llelf/Coq-Equations

    ext_lib_CI_REF=no-reexports
    ext_lib_CI_GITURL=https://github.com/llelf/coq-ext-lib

    fiat_parsers_CI_REF=no-reexports
    fiat_parsers_CI_GITURL=https://github.com/llelf/fiat

fi
