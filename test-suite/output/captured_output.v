Capture Output Check 0.
Check 1.
Capture Output Check 2.

#[warn(note="hello")] Definition bar := 3.

Capture Output Check bar.

Capture Output Fail Check 0 0.

Fail Capture Output Check 1 1.

Succeed Capture Output Check 4.

(* multiple captures add the output multiple times NOT interleaved *)
Capture Output Capture Output Check bar.

(* synterp message goes after the interp messages of previous commands *)
Capture Output Reserved Notation "x !" (at level 2).

Print Captured Output.

Drop Captured Output.

Capture Output Check 5.

Succeed Drop Captured Output.

Print Captured Output.
