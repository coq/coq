#!/bin/bash

set -e -x

cd $(dirname $0)/../..

dune build coq.install coqide-server.install
