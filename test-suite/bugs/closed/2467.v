(*
In the code below, I would expect the
    NameSetDec.fsetdec.
to solve the Lemma, but I need to do it in steps instead.

This is a regression relative to FSet,

I have v8.3 (13702).
*)

Require Import Coq.MSets.MSets.

Parameter Name : Set.
Parameter Name_compare : Name -> Name -> comparison.
Parameter Name_compare_sym : forall {x y : Name},
                             Name_compare y x = CompOpp (Name_compare x y).
Parameter Name_compare_trans : forall {c : comparison}
                                      {x y z : Name},
                               Name_compare x y = c
                            -> Name_compare y z = c
                            -> Name_compare x z = c.
Parameter Name_eq_leibniz : forall {s s' : Name},
                            Name_compare s s' = Eq
                         -> s = s'.

Module NameOrderedTypeAlt.
Definition t := Name.
Definition compare := Name_compare.
Definition compare_sym := @Name_compare_sym.
Definition compare_trans := @Name_compare_trans.
End NameOrderedTypeAlt.

Module NameOrderedType := OT_from_Alt(NameOrderedTypeAlt).

Module NameOrderedTypeWithLeibniz.
Include NameOrderedType.
Definition eq_leibniz := @Name_eq_leibniz.
End NameOrderedTypeWithLeibniz.

Module NameSetMod := MSetList.MakeWithLeibniz(NameOrderedTypeWithLeibniz).
Module NameSetDec := WDecide (NameSetMod).

Lemma foo : forall (xs ys : NameSetMod.t)
                   (n : Name)
                   (H1 : NameSetMod.Equal xs (NameSetMod.add n ys)),
            NameSetMod.In n xs.
Proof.
NameSetDec.fsetdec.
Qed.
