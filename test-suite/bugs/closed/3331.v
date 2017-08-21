(* File reduced by coq-bug-finder from original input, then from 6303 lines to 66 lines, then from 63 lines to 36 lines *)
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y :> A" := (@paths A x y) : type_scope.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (x = y :>_) : type_scope.
Class Contr_internal (A : Type) := BuildContr { center : A ; contr : (forall y : A, center = y) }.
Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.
Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.
Class IsTrunc (n : trunc_index) (A : Type) : Type := Trunc_is_trunc : IsTrunc_internal n A.
Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A) : IsTrunc n (x = y) := H x y.
Notation Contr := (IsTrunc minus_two).
Section groupoid_category.
  Variable X : Type.
  Context `{H : IsTrunc (trunc_S (trunc_S (trunc_S minus_two))) X}.
  Goal X -> True.
    intro d.
    pose (_ : Contr (idpath = idpath :> (@paths (@paths X d d) idpath idpath))) as H'. (* success *)
    clear H'.
    compute in H.
    change (forall (x y : X) (p q : x = y) (r s : p = q), Contr (r = s)) in H.
    assert (H' := H).
    set (foo:=_ : Contr (idpath = idpath :> (@paths (@paths X d d) idpath idpath))). (* success *)
    clear H' foo.
    Set Typeclasses Debug.
    pose (_ : Contr (idpath = idpath :> (@paths (@paths X d d) idpath idpath))). 
Abort. 
