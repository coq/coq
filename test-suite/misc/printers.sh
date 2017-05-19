printf "Drop. #use\"include\";; #quit;;\n" | $coqtopbyte 2>&1 | grep Unbound
if [ $? = 0 ]; then exit 1; else exit 0; fi

