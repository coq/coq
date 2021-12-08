Require Import TestSuite.admit.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.
Arguments paths_rect [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.


Definition equiv_path (A B : Type) (p : A = B) : Equiv A B.
Admitted.

Class Univalence := {
  isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B)
}.

Definition ua_downward_closed `{Univalence} : Univalence.
  constructor.
  intros A B.
  destruct H as [H].
  generalize (fun A B => @eisretr _ _ _ (H (A : Type) (B : Type))).
  generalize (fun A B => @eissect _ _ _ (H (A : Type) (B : Type))).
  let g := match goal with |- _ -> _ -> ?g => constr:(g) end in
  let U0 := match goal with |- (forall (A : ?U0) (B : ?U1), Sect (@?f A B) _) -> (forall (A : ?U2) (B : ?U3), Sect _ (@?f' A B)) -> ?g => constr:(U0) end in
  let U1 := match goal with |- (forall (A : ?U0) (B : ?U1), Sect (@?f A B) _) -> (forall (A : ?U2) (B : ?U3), Sect _ (@?f' A B)) -> ?g => constr:(U1) end in
  let U2 := match goal with |- (forall (A : ?U0) (B : ?U1), Sect (@?f A B) _) -> (forall (A : ?U2) (B : ?U3), Sect _ (@?f' A B)) -> ?g => constr:(U2) end in
  let U3 := match goal with |- (forall (A : ?U0) (B : ?U1), Sect (@?f A B) _) -> (forall (A : ?U2) (B : ?U3), Sect _ (@?f' A B)) -> ?g => constr:(U3) end in
  let f0 := match goal with |- (forall (A : ?U0) (B : ?U1), Sect (@?f A B) _) -> (forall (A : ?U2) (B : ?U3), Sect _ (@?f' A B)) -> ?g => constr:(f) end in
  let f' := match goal with |- (forall (A : ?U0) (B : ?U1), Sect (@?f A B) _) -> (forall (A : ?U2) (B : ?U3), Sect _ (@?f' A B)) -> ?g => constr:(f') end in
  change ((forall (A : U0) (B : U1), Sect (f0 A B) ((fun (A : U0) (B : U1) => @equiv_inv _ _ _ (H A B)) A B))
          -> (forall (A : U2) (B : U3), Sect ((fun (A : U0) (B : U1) => @equiv_inv _ _ _ (H A B)) A B) (f' A B))
          -> g);
    generalize (fun (A : U0) (B : U1) => @equiv_inv _ _ _ (H A B));
    clear H;
    simpl;
    intros fi sect retr.
  pose proof fi as fi'.
  Set Printing All.
  change (forall (A : Type) (B : Type) (_ : Equiv A B), @paths Type A B) in fi'.
  (*refine (@isequiv_adjointify
              _ _
              _ _
              _
              _);
    admit.
  Grab Existential Variables.*)
  admit.
  (*destruct p.*)
  (*specialize (H (A' : Type)).*)
Defined.
(* Error: Unsatisfied constraints:
Top.62 < Top.61
Top.64 <= Top.62
Top.63 <= Top.62
 (maybe a bugged tactic).*)
