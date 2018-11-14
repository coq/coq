#!/bin/sh
set -e

$coqc -R misc/quick-include/ QuickInclude -quick misc/quick-include/file1.v
$coqc -R misc/quick-include/ QuickInclude -quick misc/quick-include/file2.v
