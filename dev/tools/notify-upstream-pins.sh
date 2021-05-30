
#!/usr/bin/env bash

# Script to notify upstreams that we need a tag to put in a platform/installer

VERSION="8.13"
DATEBETA="December 7, 2020"
DATEFINAL="January 7, 2020"
CC="CC: https://github.com/coq/coq/issues/12334"
#CC="\n@coqbot column:...."
REASON="bundled in the Windows installer"
#REASON="bundled in the Coq platform"

git show master:dev/ci/ci-basic-overlay.sh > /tmp/master-ci-basic-overlay.sh
git show v${VERSION}:dev/ci/ci-basic-overlay.sh > /tmp/branch-ci-basic-overlay.sh

# reads a variable value from a ci-basic-overlay.sh file
function read_from() {
  ( . $1; varname="$2"; echo ${!varname} )
}

# https://gist.github.com/cdown/1163649
function urlencode() {
    # urlencode <string>

    old_lc_collate=$LC_COLLATE
    LC_COLLATE=C

    local length="${#1}"
    for (( i = 0; i < length; i++ )); do
        local c="${1:$i:1}"
        case $c in
            [a-zA-Z0-9.~_-]) printf '%s' "$c" ;;
            *) printf '%%%02X' "'$c" ;;
        esac
    done

    LC_COLLATE=$old_lc_collate
}

function template {
  TITLE="Please create a tag for the upcoming release of Coq $VERSION"
  BODY="The Coq team is planning to release Coq $VERSION-beta1 on $DATEBETA,
and Coq $VERSION.0 on $DATEFINAL.

Your project is currently scheduled for being $REASON.

We are currently testing commit $3
on branch $1/tree/$2
but we would like to ship a released version instead (a tag in git's slang).

Could you please tag that commit, or communicate us any other tag
that works with the Coq branch v$VERSION at the *latest* 15 days before the
date of the final release?

Thanks!
$CC
"
  UUTITLE=$(urlencode "$TITLE")
  UUBODY=$(urlencode "$BODY")

  case $1 in
  ( http*github.com* )
    echo "$1/issues/new?title=$UUTITLE&body=$UUBODY"
  ;;
  ( http*gitlab* )
    echo "$1/-/issues/new"
    echo
    echo -e "$TITLE"
    echo
    echo -e "$BODY"
  ;;
  ( * )
    echo "$1"
    echo
    echo -e "$TITLE"
    echo
    echo -e "$BODY"

  ;;
  esac
}

# TODO: filter w.r.t. what is in the platform
PROJECTS=`read_from /tmp/branch-ci-basic-overlay.sh "projects[@]"`

for addon in $PROJECTS; do
    URL=`read_from /tmp/master-ci-basic-overlay.sh "${addon}_CI_GITURL"`
    REF=`read_from /tmp/master-ci-basic-overlay.sh "${addon}_CI_REF"`
    PIN=`read_from /tmp/branch-ci-basic-overlay.sh "${addon}_CI_REF"`
    if [ "${#PIN}" = "40" ]; then
      echo -e "Addon $addon is pinned to a hash, to open an issue open the following url:\n"
      template $URL $REF $PIN
    elif [ "${#PIN}" = "0" ]; then
      echo "Addon $addon has no pin!"
      exit 1
    else
      echo "Addon $addon is already pinned to version $PIN"
    fi
    echo -e "\n----------------------------------------------"
done
