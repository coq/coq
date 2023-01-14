From TestSuite Extra Dependency "extra_dep.txt".
Comments From TestSuite Extra Dependency "extra_dep.txt".

From TestSuite Extra Dependency "extra_dep.txt" as d1.

Fail From TestSuite Extra Dependency "extra_dep.txt" as d1.

From TestSuite Extra Dependency "extra_dep.txt" as d2.

Add LoadPath "prerequisite/subdir" as Test.
Set Warnings "+ambiguous-extra-dep".
Fail From Test Extra Dependency "extra_dep.txt".
Fail Comments From Test Extra Dependency "extra_dep.txt".
