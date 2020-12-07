#!/bin/bash

set -e -x

cd $(dirname $0)/../..

eval $(opam env)
dune build coq.install coqide-server.install
