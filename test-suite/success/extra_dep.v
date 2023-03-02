From TestSuite Extra Dependency "extra_dep.txt".

From TestSuite Extra Dependency "extra_dep.txt" as d1.

Fail From TestSuite Extra Dependency "extra_dep.txt" as d1.

From TestSuite Extra Dependency "extra_dep.txt" as d2.

Add LoadPath "prerequisite/subdir" as TestSuite.
Set Warnings "+ambiguous-extra-dep".
Fail From TestSuite Extra Dependency "extra_dep.txt".
