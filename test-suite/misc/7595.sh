#!/bin/sh
set -e

coqc -R 7595 Test 7595/base.v
coqc -R 7595 Test 7595/FOO.v
