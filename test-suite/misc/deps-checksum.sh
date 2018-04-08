#!/bin/sh
rm -f misc/deps/A/*.vo misc/deps/B/*.vo
$coqc -R misc/deps/A A misc/deps/A/A.v
$coqc -R misc/deps/B A misc/deps/B/A.v
$coqc -R misc/deps/B A misc/deps/B/B.v
$coqtop -R misc/deps/B A -R misc/deps/A A -load-vernac-source misc/deps/checksum.v
