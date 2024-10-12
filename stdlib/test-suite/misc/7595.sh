#!/bin/sh
set -e

$coqc -R misc/7595 Test misc/7595/base.v
$coqc -R misc/7595 Test misc/7595/FOO.v
