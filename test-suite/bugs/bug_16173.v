
Section S.
  Variables (a:nat) (b:bool).

  Fail Set Default Proof Using ")".
  Fail Set Default Proof Using "a)".
  Fail Set Default Proof Using "(a . )".
  Fail Set Default Proof Using "(a .".
  Set Default Proof Using "".

  Lemma foo1 : True.
  Proof. trivial. Qed.

  Set Default Proof Using "()".
  Lemma foo2 : True.
  Proof. trivial. Qed.

  Set Default Proof Using "( )".
  Lemma foo2' : True.
  Proof. trivial. Qed.

  Set Default Proof Using "a b".
  Lemma foo3 : True.
  Proof. trivial. Qed.

  Set Default Proof Using "(b a)".
  Lemma foo4 : True.
  Proof. trivial. Qed.
End S.

Check foo1 : True.
Check foo2 : True.
Check foo2' : True.
Check foo3 : nat -> bool -> True.
Check foo4 : nat -> bool -> True.

Require Import Corelib.ssr.ssreflect.
(* ssr makes "\*\)" parse differently so preprocessing has to make sure to insert a space *)
Set Default Proof Using "Type*".
