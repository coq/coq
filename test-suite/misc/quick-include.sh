#!/bin/sh
set -e

coqc -R quick-include/ QuickInclude -vio quick-include/file1.v
coqc -R quick-include/ QuickInclude -vio quick-include/file2.v
