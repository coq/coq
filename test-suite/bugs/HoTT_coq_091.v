Set Implicit Arguments.

Set Printing Universes.

Set Asymmetric Patterns.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.
Arguments paths_rect [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Arguments ap {A B} f {x y} p : simpl nomatch.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Inductive type_eq (A : Type) : Type -> Type :=
| type_eq_refl : type_eq A A
| type_eq_impossible : False -> forall B : Type, type_eq A B.

Definition type_eq_sym {A B} (p : type_eq A B) : type_eq B A
  := match p in (type_eq _ B) return (type_eq B A) with
       | type_eq_refl => type_eq_refl _
       | type_eq_impossible f B => type_eq_impossible _ f A
     end.

Definition type_eq_sym_type_eq_sym {A B} (p : type_eq A B) : type_eq_sym (type_eq_sym p) = p
  := match p as p return type_eq_sym (type_eq_sym p) = p with
       | type_eq_refl => idpath
       | type_eq_impossible f _ => idpath
     end.

Module Type LiftT.
  Section local.
    Let type_cast_up_type : Type.
    Proof.
      let U0 := constr:(Type) in
      let U1 := constr:(Type) in
      let unif := constr:(U0 : U1) in
      exact (forall T : U0, { T' : U1 & type_eq T' T }).
    Defined.

    Axiom type_cast_up : type_cast_up_type.
  End local.

  Definition Lift (T : Type) := projT1 (type_cast_up T).
  Definition lift {T} : T -> Lift T
    := match projT2 (type_cast_up T) in (type_eq _ T') return T' -> Lift T with
         | type_eq_refl => fun x => x
         | type_eq_impossible bad _ => match bad with end
       end.
  Section equiv.
    Definition lower' {T} : Lift T -> T
      := match projT2 (type_cast_up T) in (type_eq _ T') return Lift T -> T' with
           | type_eq_refl => fun x => x
           | type_eq_impossible bad _ => match bad with end
         end.
    Definition lift_lower {T} (x : Lift T) : lift (lower' x) = x.
    Proof.
      unfold lower', lift.
      destruct (projT2 (type_cast_up T)) as [|[]].
      reflexivity.
    Defined.
    Definition lower_lift {T} (x : T) : lower' (lift x) = x.
    Proof.
      unfold lower', lift, Lift in *.
      destruct (type_cast_up T) as [T' p]; simpl.
      let y := match goal with |- ?y => constr:(y) end in
      let P := match (eval pattern p in y) with ?f p => constr:(f) end in
      apply (@transport _ P _ _ (type_eq_sym_type_eq_sym p)); simpl in *.
      generalize (type_eq_sym p); intro p'; clear p.
      destruct p' as [|[]]; simpl.
      reflexivity.
    Defined.

    Global Instance isequiv_lift A : IsEquiv (@lift A).
    Proof.
      refine (@BuildIsEquiv
                _ _
                lift lower'
                lift_lower
                lower_lift
                _).
      compute.
      intro x.
      destruct (type_cast_up A) as [T' p].
      let y := match goal with |- ?y => constr:(y) end in
      let P := match (eval pattern p in y) with ?f p => constr:(f) end in
      apply (@transport _ P _ _ (type_eq_sym_type_eq_sym p)); simpl in *.
      generalize (type_eq_sym p); intro p'; clear p.
      destruct p' as [|[]]; simpl.
      reflexivity.
    Defined.
  End equiv.
  Definition lower {A} := (@equiv_inv _ _ (@lift A) _).
End LiftT.

Module Lift : LiftT.
  Section local.
    Let type_cast_up_type : Type.
    Proof.
      let U0 := constr:(Type) in
      let U1 := constr:(Type) in
      let unif := constr:(U0 : U1) in
      exact (forall T : U0, { T' : U1 & type_eq T' T }).
    Defined.

    Definition type_cast_up : type_cast_up_type
      := fun T => existT (fun T' => type_eq T' T) T (type_eq_refl _).
  End local.

  Definition Lift (T : Type) := projT1 (type_cast_up T).
  Definition lift {T} : T -> Lift T
    := match projT2 (type_cast_up T) in (type_eq _ T') return T' -> Lift T with
         | type_eq_refl => fun x => x
         | type_eq_impossible bad _ => match bad with end
       end.
  Section equiv.
    Definition lower' {T} : Lift T -> T
      := match projT2 (type_cast_up T) in (type_eq _ T') return Lift T -> T' with
           | type_eq_refl => fun x => x
           | type_eq_impossible bad _ => match bad with end
         end.
    Definition lift_lower {T} (x : Lift T) : lift (lower' x) = x.
    Proof.
      unfold lower', lift.
      destruct (projT2 (type_cast_up T)) as [|[]].
      reflexivity.
    Defined.
    Definition lower_lift {T} (x : T) : lower' (lift x) = x.
    Proof.
      unfold lower', lift, Lift in *.
      destruct (type_cast_up T) as [T' p]; simpl.
      let y := match goal with |- ?y => constr:(y) end in
      let P := match (eval pattern p in y) with ?f p => constr:(f) end in
      apply (@transport _ P _ _ (type_eq_sym_type_eq_sym p)); simpl in *.
      generalize (type_eq_sym p); intro p'; clear p.
      destruct p' as [|[]]; simpl.
      reflexivity.
    Defined.


    Global Instance isequiv_lift A : IsEquiv (@lift A).
    Proof.
      refine (@BuildIsEquiv
                _ _
                lift lower'
                lift_lower
                lower_lift
                _).
      compute.
      intro x.
      destruct (type_cast_up A) as [T' p].
      let y := match goal with |- ?y => constr:(y) end in
      let P := match (eval pattern p in y) with ?f p => constr:(f) end in
      apply (@transport _ P _ _ (type_eq_sym_type_eq_sym p)); simpl in *.
      generalize (type_eq_sym p); intro p'; clear p.
      destruct p' as [|[]]; simpl.
      reflexivity.
    Defined.
  End equiv.
  Definition lower {A} := (@equiv_inv _ _ (@lift A) _).
End Lift.
(* Toplevel input, characters 15-24:
Anomaly: Invalid argument: enforce_eq_instances called with instances of different lengths.
Please report. *)
