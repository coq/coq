$coqtop -load-vernac-source misc/exitstatus/illtyped.v
N=$?
$coqc misc/exitstatus/illtyped.v
P=$?
printf "On ill-typed input, coqtop returned $N.\n"
printf "On ill-typed input, coqc returned $P.\n"
if [ $N = 1 -a $P = 1 ]; then exit 0; else exit 1; fi
