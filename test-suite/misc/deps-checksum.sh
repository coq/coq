#!/bin/sh
rm -f deps/A/*.vo deps/B/*.vo
coqc -R deps/A A deps/A/A.v
coqc -R deps/B A deps/B/A.v
coqc -R deps/B A deps/B/B.v
coqc -R deps/B A -R deps/A A deps/checksum.v
