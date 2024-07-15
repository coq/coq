Module First.
  Definition bar := 1.
  Lemma bar_1 : bar = 1. Proof. reflexivity. Qed.
End First.

Module Import Second.
  Include First.
  Search bar. (*First.bar_1: First.bar = 1*)
  Search "bar".
  Lemma one_bar : 1 = bar. Proof. rewrite bar_1. reflexivity. Qed.
End Second.

Module Type B.
  Definition bar := 1.
  Lemma bar_1 : bar = 1. Proof. reflexivity. Qed.
End B.

Module A.
  Include B.
  Search bar. (* was nothing *)
  Lemma one_bar : 1 = bar. Proof. rewrite bar_1; reflexivity. Qed.
  Search bar. (* was only one_bar *)
End A.

Module Type HasFoo.
  Parameter t : Type.
  Parameter foo : t.
End HasFoo.

Module MakeBaz (Import M : HasFoo).
  Definition baz := fun (_ : unit) => foo.
  Lemma baz_foo : baz tt = foo. Proof. reflexivity. Qed.
End MakeBaz.

Module Import Baz <: HasFoo.
  Definition t := nat.
  Definition foo := 42.
  Include MakeBaz.
  Search baz. (* was nothing *)
  Search "baz". (* was nothing *)
  Lemma foo_bas : foo = baz tt. Proof. rewrite baz_foo. reflexivity. Qed.
End Baz.
