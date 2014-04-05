(* Not having a [return] clause causes the [refine] at the bottom to stack overflow before f65fa9de8a4c9c12d933188a755b51508bd51921 *)

Require Import Coq.Lists.List.
Require Import Relations RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Section hlist.
  Context {iT : Type}.
  Variable F : iT -> Type.

  Inductive hlist : list iT -> Type :=
  | Hnil  : hlist nil
  | Hcons : forall l ls, F l -> hlist ls -> hlist (l :: ls).

  Definition hlist_hd {a b} (hl : hlist (a :: b)) : F a :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | l :: _ => F l
                               end with
      | Hnil => tt
      | Hcons _ _ x _ => x
    end.

  Definition hlist_tl {a b} (hl : hlist (a :: b)) : hlist b :=
    match hl in hlist x return match x with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | Hnil => tt
      | Hcons _ _ _ x => x
    end.

  Lemma hlist_eta : forall ls (h : hlist ls),
    h = match ls as ls return hlist ls -> hlist ls with
          | nil => fun _ => Hnil
          | a :: b => fun h => Hcons (hlist_hd h) (hlist_tl h)
        end h.
  Proof.
    intros. destruct h; auto.
  Qed.

  Variable eqv : forall x, relation (F x).

  Inductive equiv_hlist : forall ls, hlist ls -> hlist ls -> Prop :=
  | hlist_eqv_nil : equiv_hlist Hnil Hnil
  | hlist_eqv_cons : forall l ls x y h1 h2, eqv x y -> equiv_hlist h1 h2 ->
                                            @equiv_hlist (l :: ls) (Hcons x h1) (Hcons y h2).

  Global Instance Reflexive_equiv_hlist (R : forall t, Reflexive (@eqv t)) ls
  : Reflexive (@equiv_hlist ls).
  Proof.
    red. induction x; constructor; auto. reflexivity.
  Qed.

  Global Instance Transitive_equiv_hlist (R : forall t, Transitive (@eqv t)) ls
  : Transitive (@equiv_hlist ls).
  Proof.
    red. induction 1.
    { intro; assumption. }
    { rewrite (hlist_eta z).
      Timeout 2 Fail refine
        (fun H =>
           match H in @equiv_hlist ls X Y
                 return
                 (* Uncommenting the following gives an immediate error in 8.4pl3; commented out results in a stack overflow *)
                 match ls (*as ls return hlist ls -> hlist ls -> Type*) with
                   | nil => fun _ _ : hlist nil => True
                   | l :: ls => fun (X Y : hlist (l :: ls)) =>
                                  equiv_hlist (Hcons x h1) Y
                 end X Y
           with
             | hlist_eqv_nil => I
             | hlist_eqv_cons l ls x y h1 h2 pf pf' =>
               _
           end).
