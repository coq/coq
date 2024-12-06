#!/usr/bin/env bash
# For compat with OSX which has a non-gnu sed which doesn't support -z
SED=`(which gsed || which sed) 2> /dev/null`

if [ $# != 1 ]; then
  echo "usage: $0 rev0..rev1"
  exit 1
fi

git shortlog -s -n --no-merges --group=author --group=trailer:Co-authored-by $1 | cut -f2 | sort -k 2 | grep -v -e "coqbot" -e "^$" > contributors.tmp

cat contributors.tmp | wc -l | xargs echo "Contributors:"
cat contributors.tmp | $SED -z "s/\n/, /g"
echo
rm contributors.tmp

git shortlog -s -n --merges --group=author --group=trailer:Co-authored-by $1 | cut -f2 | sort -k 2 | grep -v -e "coqbot" -e "^$" > assignees.tmp

cat assignees.tmp | wc -l | xargs echo "Assignees:"
cat assignees.tmp | $SED -z "s/\n/, /g"
echo
rm assignees.tmp

git shortlog -s -n --merges --group=trailer:reviewed-by --group=trailer:ack-by $1 | cut -f2 | sort -k 2 | grep -v -e "coqbot" -e "^$" > reviewers.tmp

cat reviewers.tmp | wc -l | xargs echo "Reviewers:"
cat reviewers.tmp | $SED -z "s/\n/, /g"
echo
rm reviewers.tmp
