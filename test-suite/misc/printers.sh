#!/bin/sh
if printf "Drop. #use\"include\";; #quit;;\n" | $coqtopbyte 2>&1 | grep -E "Error|Unbound" ; then exit 1; else exit 0; fi
