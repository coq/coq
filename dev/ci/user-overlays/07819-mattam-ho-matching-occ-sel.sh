_OVERLAY_BRANCH=ho-matching-occ-sel

if [ "$CI_PULL_REQUEST" = "7819" ] || [ "$CI_BRANCH" = "$_OVERLAY_BRANCH" ]; then

    unicoq_CI_REF="PR7819-overlay"

    mtac2_CI_REF="PR7819-overlay"
    mtac2_CI_GITURL=https://github.com/mattam82/Mtac2

    Equations_CI_REF="PR7819-overlay"

fi
