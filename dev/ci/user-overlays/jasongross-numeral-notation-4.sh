if [ "$CI_PULL_REQUEST" = "8064" ] || [ "$CI_BRANCH" = "numeral-notation-4" ]; then
    HoTT_CI_REF=fix-for-numeral-notations
    HoTT_CI_GITURL=https://github.com/JasonGross/HoTT
    HoTT_CI_ARCHIVEURL=${HoTT_CI_GITURL}/archive
fi
