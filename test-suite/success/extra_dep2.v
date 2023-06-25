(* coq-prog-args: ("-Q" "prerequisite/subdir" "TestSuite") *)

Set Warnings "+ambiguous-extra-dep".
Fail From TestSuite Extra Dependency "extra_dep.txt".
