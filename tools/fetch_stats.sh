#!/usr/bin/env bash
# fetch and stats files from CI

RED="\033[31m"
RESET="\033[0m"
error() {
  echo -e "${RED}error:${RESET} $1 ${RESET}"
}

if [ $# != 1 ]; then
  error "usage: $0 pipeline-number"
  exit 1
fi

if [[ "$1" =~ ^[1-9][0-9]*$ ]]; then
  PIPELINE=$1
else
  error "$1 is not a number"
  exit 1
fi

echo Removing existing "*.stats" files...
rm *.stats
echo Downloading "*.stats" files...
TMPFILE=$(mktemp /tmp/fetch_stats.XXXXXX)
curl -s "https://gitlab.com/coq/coq/pipelines/$PIPELINE.json" >$TMPFILE

mapfile -t JNAMES < <( jq -r '.details.artifacts[].name' <$TMPFILE )
mapfile -t APATHS < <( jq -r '.details.artifacts[].path' <$TMPFILE )
rm "$TMPFILE"

for ((n = 0; n < ${#JNAMES[@]}; n++)); do
  JNAME=${JNAMES[$n]}
  # skip variants such as build:base+32bit
  if [[ ! $JNAME =~ "+" ]]; then
    APATH=${APATHS[$n]}
    URL=https://gitlab.com${APATH/download/raw}/$JNAME.stats
    if curl -s --fail -O $URL; then
      echo $URL
    fi
  fi
done
echo Now run \"bin/print_stats.sh *.stats\"
