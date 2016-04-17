(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter") -*- *)

Module separate.
  Universes i j.

  Inductive A : Type@{i} :=
    with B : Type@{j} :=.

  Constraint i < j.
End separate.

Module diff.
  Universes k l.

  Inductive A : Type@{k} :=
    fooa (a : A) : B -> A
    with B : Type@{l} :=.

  Fail Constraint k < l. (* l <= k due to the constructor *)
End diff.

Module indind.
  Universes m n.

  Inductive A : Type@{m} :=
    with B : A -> Type@{n} :=.

  Fail Constraint n < m. (* m <= n due to the indices matter *)
End indind.

Module notemplate.

  Inductive C (A : Type) : Set :=
  with equiv (A : Type) : C A -> Type :=.
  (* The type cannot fall in Prop due to indices matter *)
  Check eq_refl : ltac:(let t := type of equiv in exact t) = (forall A, C A -> Set).
End notemplate.
