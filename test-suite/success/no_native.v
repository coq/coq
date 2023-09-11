(* -*- coq-prog-args: ("-native-compiler" "ondemand"); -*- *)

Definition foo := I.
#[native_compile=no] Definition bar := I.
Definition baz := bar.
(* NB this would cause a failure at the end if native compiler was "on"
   Future work: automatically put "native no" on dependents *)

Definition qux := foo.
Eval native_compute in foo. (* sanity check *)

(* trick to make the test pass when native configured off *)
Set Warnings "+native-compiler-disabled".

Fail Eval native_compute in bar. (* check failure of native_compute *)
Fail Eval native_compute in baz. (* check correct handling of transitive dependency on native uncompilable *)

Set Warnings "-native-compiler-disabled".

Eval native_compute in foo. (* check that native compiler not left in an inconsistent state *)

#[native_compile=no] Definition boz : True.
Proof.
exact I.
Fail Qed.
Defined.

Set Warnings "+native-compiler-disabled".

Fail Eval native_compute in boz.
