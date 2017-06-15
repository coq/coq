#!/usr/bin/env bash

# setup travis only things

set +x
if [ -n "${MEGANAME}" ];
then
    echo "[Login]" > ~/.megarc
    echo "Username = $MEGANAME" >> ~/.megarc
    echo "Password = $MEGAPASS" >> ~/.megarc
fi

set -ex

opam init -j ${NJOBS} --compiler=${COMPILER} -n -y
