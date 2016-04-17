
(* Discharge *)

Module Test1.

  Section S.
    Variable Param : Set.
    Inductive foo (A : Set) :=
    | cst : foo A
    | somefoo : A ->  foo A
    | somefoob : Param -> cst = cst -> foo A.

    Definition foo' := somefoob.

  End S.
End Test1.

Module Test2.

  Section S.
    Variable Param : Set.

    Inductive A : Type :=
    | ca : A -> A
    with B : A -> Type :=
         (* | cb (a : A) : B a -> B a *)
         | param (x : Param) a : B a.
  End S.

  Definition foo (P : Set) (x : A P) :=
    match x with
    | ca _ x => x
    end.

  Definition foo' (P : Set) (x : A P) (y : B _ x) :=
    match y with
    | param _ x a => a
    end.
End Test2.

Module Test3.

  Section S.
    Variable Param : Set.

    Inductive A (P2 : Set) : Type :=
    | ca : A P2 -> A P2
    with B (P2 : Set) : A P2 -> Type :=
         (* | cb (a : A) : B a -> B a *)
         | param (x : Param) (a : A P2) : B P2 a.
  End S.

  Definition foo (P : Set) (x : A P P) :=
    match x with
    | ca _ _ x => x
    end.

  Definition foo' (P : Set) (x : A P P) (y : B _ _ x) :=
    match y with
    | param _ _ x a => a
    end.

End Test3.

Module Test4.
  Section S.
    Variable Param : Set.

    Inductive A (P2 : Set) : Type :=
    | ca : A P2 -> A P2
    with B (P2 : Set) : A P2 -> Type :=
         | cb (a : A P2) : B _ (ca _ a) -> B P2 a
         | param (x : Param) (a : A P2) : B P2 a.
  End S.

  Definition foo (P : Set) (x : A P P) :=
    match x with
    | ca _ _ x => x
    end.

  Definition foo' (P : Set) (x : A P P) (y : B _ _ x) :=
    match y with
    | cb _ _ a _ => a
    | param _ _ x a => a
    end.

End Test4.
