#!/usr/bin/env bash

$coqc misc/redirect_printing.v
diff -u redirect_test.out misc/redirect_printing.out
