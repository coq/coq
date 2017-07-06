#!/usr/bin/env bash

set +x
if [ -n "${MEGANAME}" ];
then
    echo "[Login]" > ~/.megarc
    echo "Username = $MEGANAME" >> ~/.megarc
    echo "Password = $MEGAPASS" >> ~/.megarc
else
    exit 0
fi

set -ex

source dev/ci/travis-exports.sh

setup-mega

megals /Root/ | grep Coq-travis > megafiles

# grab the build numbers of uploaded files, uniquify, remove newest 2
cat megafiles | sed -r 's:/Root/Coq-travis-.*-([0-9]+).zip:\1:g' | sort -ru | awk 'NR>2' > megajobs

for i in $(cat megajobs);
do
    for f in $(cat megafiles | grep $i);
    do
        megarm "$f"
    done
done
