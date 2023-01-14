#!/usr/bin/env bash

coqc redirect_printing.v
diff -u redirect_test.out redirect_printing.out
