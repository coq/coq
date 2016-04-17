Unset Elimination Schemes.

(** James construction in Homotopy type theory

  Initial example by Ali Caglayan.
*)

(** The James construction as defined in Brunerie's thesis (https://arxiv.org/abs/1606.05916) has a tricky recursive-recursive definition that we will test here. Without recursive-recursive support in coq, this would have to be defined as a fixpoint into a record type. *)

Inductive Unit : Type := tt : Unit.

Inductive Id {A : Type} (x : A) : A -> Type := refl : Id x x.

Arguments refl {_ _}.

Scheme Id_ind := Induction for Id Sort Type.
Arguments Id_ind [A] x P f y.
Scheme paths_rec := Minimality for Id Sort Type.
Arguments Id [A] x P.

Register refl as core.identity.refl.
Definition Id_rect := Id_ind.
Register Id_rect as core.identity.ind.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : Id x y) (a : P x)
  : P y := match p with refl => a end.

Definition transport_const {A B : Type} {x y : A} (p : Id x y) (a : B)
  : Id (transport (fun _ => B) p a) a
  := match p with refl => refl end.

Definition apD {A : Type} {B : A -> Type} (f : forall a, B a) {x y : A} (p : Id x y)
  : Id (transport B p (f x)) (f y)
  := match p with refl => refl end.

Definition ap {A B : Type} {x y : A} (f : A -> B) (p : Id x y) : Id (f x) (f y)
  := match p with refl => refl end.

Definition id_concat {A : Type} {x y z : A}
  : Id x y -> Id y z -> Id x z.
Proof.
  intros p q.
  destruct p, q.
  apply refl.
Defined.

Lemma apD_const {A B} {x y : A} (f : A -> B) (p : Id x y)
  : Id (apD f p) (id_concat (transport_const p (f x)) (ap f p)).
Proof.
  destruct p; reflexivity.
Defined.

Definition id_concat_1p {A : Type} {x y : A} (p : Id x y)
  : Id (id_concat refl p) p
  := match p with refl => refl end.

Definition id_inv {A : Type} {x y : A} (p : Id x y) : Id y x
  := match p with refl => refl end.

Lemma id_cancelL {A : Type} {w x y : A} (p q : Id x y) (r : Id w x)
  : Id (id_concat r p) (id_concat r q) -> Id p q.
Proof.
  intro l.
  destruct r.
  refine (id_concat (id_inv _) (id_concat l _)).
  all: apply id_concat_1p.
Defined.

(** Here we need the HIT pushout which we fake using a private inductive type *)
Module Export Pushout.

  Private Inductive Pushout {A B C : Type} (f : A -> B) (g : A -> C) : Type :=
  | pushl : B -> Pushout f g
  | pushr : C -> Pushout f g.

  Axiom pglue : forall {A B C : Type} (f : A -> B) (g : A -> C) (x : A),
    Id (pushl f g (f x)) (pushr f g (g x)).

  (** Induction principle that computes on point constructors *)
  Definition Pushout_ind {A B C : Type} (f : A -> B) (g : A -> C)
    (P : Pushout f g -> Type)
    (l : forall b, P (pushl f g b))
    (r : forall c, P (pushr f g c))
    (h : forall a, Id (transport P (pglue f g a) (l (f a))) (r (g a)))
    (x : Pushout f g) : P x
    := match x with
       | pushl _ _ b => l b
       | pushr _ _ c => r c
       end.

  (** Computation rule for the path constructor *)
  Axiom Pushout_ind_beta_pglue
    : forall {A B C : Type} (f : A -> B) (g : A -> C)
    (P : Pushout f g -> Type)
    (l : forall b, P (pushl f g b))
    (r : forall c, P (pushr f g c))
    (h : forall a, Id (transport P (pglue f g a) (l (f a))) (r (g a)))
    (a : A), Id (apD (Pushout_ind f g P l r h) (pglue f g a)) (h a).

End Pushout.

Arguments pushl {A B C f g}.
Arguments pushr {A B C f g}.

Definition Pushout_rec {A B C : Type} (f : A -> B) (g : A -> C)
  (P : Type) (l : B -> P) (r : C -> P)
  (h : forall a, Id (l (f a)) (r (g a)))
  : Pushout f g -> P.
Proof.
  refine (Pushout_ind f g (fun _ => P) l r _).
  intro a.
  exact (id_concat (transport_const _ _) (h a)).
Defined.

Arguments Pushout_rec {A B C} f g P &.

Definition Pushout_rec_beta_pglue {A B C : Type} (f : A -> B) (g : A -> C)
  (P : Type) (l : B -> P) (r : C -> P)
  (h : forall a, Id (l (f a)) (r (g a)))
  : forall a, Id (ap (Pushout_rec f g P l r h) (pglue f g a)) (h a).
Proof.
  intro a.
  refine (id_cancelL _ _ (transport_const (pglue f g a) (l (f a))) _).
  refine (id_concat (id_inv _) _).
  1: apply (apD_const (Pushout_rec f g P l r h) (pglue f g a)).
  exact (Pushout_ind_beta_pglue f g (fun _ => P) l r _ a).
Defined.

Set Printing All.
(* Set Debug Unification. *)
Module GuardFail.
Section James.
  Context (A : Type) (pt : A).
  Notation f J i n :=
  (@Pushout_rec (J n%nat) (prod A (J n%nat)) (J (S n)) (fun x => (pt, x)) (i%function n%nat) (A * J (S n))
    (fun ax => (fst ax, i%function n%nat (snd ax))) (fun y => (pt, y)) (fun x => refl)).

  Notation g J i α β n :=
   (Pushout_rec (fun x => (pt, x)) (i%function n%nat) (J (S n%nat))
      (fun ax => α n%nat (fst ax) (snd ax)) (fun y => y) (fun x => β%function n%nat x)).
(*
  Definition f (J : nat -> Type)
   (i : forall (n : nat), J n -> J (S n))
   (n : nat) : Pushout (fun x => (pt, x)) (i n) -> A * J (S n) :=
    Pushout_rec _ _ _ (fun ax => (fst ax, i n (snd ax))) (fun y => (pt, y)) (fun x => refl). *)

  (*Definition g (J : nat -> Type)
    (i : forall (n : nat), J n -> J (S n))
    (α : forall (n : nat), A -> J n -> J (S n))
    (β : forall (n : nat) (x : J n), Id (α n pt x) (i n x))
    (n : nat) : Pushout (fun x => (pt, x)) (i n) -> J (S n) :=
    Pushout_rec _ _ _ (fun ax => α n (fst ax) (snd ax)) (fun y => y) (fun x => β n x).*)

  (* Guard checking of bodies bails because it cannot unfold [J (S n)] in the definition of f above s*)
  (* If types are taken into account,
     we need to allow all the predicate arguments in matches to be
     considered strict subterms of the initial argument, including the "alias"
     of the matched argument itself. E.g. to allow the (J n) call in the type of [i]. *)


    Definition J : nat -> Type :=
  fix J (n : nat) {struct n} : Type :=
  match n with
  | O => Unit
  | S n0 => J' n0
  end
  with J' (n : nat) : Type :=
  match n with
  | 0 => A
  | S n1 => Pushout (f J i n1) (g J i α β n1)
  end
  with i (n : nat) {struct n} : J n -> J (S n) :=
    match n return J n -> J (S n) with
    | O => fun _ => pt
    | S n' => fun jn => @pushr _ _ _ (f J i n') (g J i α β n') jn
    end
  with α (n : nat) {struct n} : A -> J n -> J (S n) :=
    match n return A -> J n -> J (S n) with
    | O => fun a _ => a
    | S n => fun a jsn => @pushl _ _ _ (f J i n) (g J i α β n) (a, jsn)
    end
  with β (n : nat) {struct n} : forall (x : J n), Id (α n pt x) (i n x) :=
    match n return forall x : J n, Id (α n pt x) (i n x) with
    | O => fun x => refl
    | S n => fun l => pglue (f J i n) (g J i α β n) (pushr l)
    end
  for J.
  End James.
End GuardFail.

Section James.

  Context (A : Type) (pt : A).

  Definition JA J' (n : nat) : Type :=
    match n with
    | 0 => A
    | S n => J' n
    end.

  Definition f (J' : nat -> Type)
   (i : forall (n : nat), JA J' n -> J' n)
   (n : nat) : Pushout (fun x => (pt, x)) (i n) -> A * J' n :=
    Pushout_rec _ _ _ (fun ax => (fst ax, i n (snd ax))) (fun y => (pt, y)) (fun x => refl).

  Definition g (J' : nat -> Type)
    (i : forall (n : nat), JA J' n -> J' n)
    (α : forall (n : nat), A -> JA J' n -> J' n)
    (β : forall (n : nat) (x : JA J' n), Id (α n pt x) (i n x))
    (n : nat) : Pushout (fun x => (pt, x)) (i n) -> J' n :=
    Pushout_rec _ _ _ (fun ax => α n (fst ax) (snd ax)) (fun y => y) (fun x => β n x).

  (* Unset Guard Checking.
    Note we still don't guard-check the return predicates of pattern matchings.
    It does guarantee however that the recursive calls inside the match branches
    are structurally recursive.
  *)

  Definition J' : nat -> Type :=
  fix J' (n : nat) {struct n} : Type :=
  match n with
  | O => A
  | S n1 => Pushout (f J' i n1) (g J' i α β n1)
  end
  with i (n : nat) {struct n} : JA J' n -> J' n :=
    match n return JA J' n -> J' n with
    | O => fun _ => pt
    | S n' => pushr
    end
  with α (n : nat) {struct n} : A -> JA J' n -> J' n :=
    match n return A -> JA J' n -> J' n with
    | O => fun a _ => a
    | S n => fun a jsn => pushl (a, jsn)
    end
  with β (n : nat) {struct n} : forall (x : JA J' n), Id (α n pt x) (i n x) :=
    match n return forall x : JA J' n, Id (α n pt x) (i n x) with
    | O => fun x => refl
    | S n => fun l => pglue (f J' i n) (g  J' i α β n) (pushr l)
    end
  for J'.

  Definition J := JA J'.

  Definition i : forall (n : nat), J n -> J (S n) :=
  fix J' (n : nat) {struct n} : Type :=
  match n with
  | O => A
  | S n1 => Pushout (f J' i n1) (g J' i α β n1)
  end
  with i (n : nat) {struct n} : JA J' n -> J' n :=
    match n return JA J' n -> J' n with
    | O => fun _ => pt
    | S n' => fun jn => @pushr _ _ _ (f J' i n') (g J' i α β n') jn
    end
  with α (n : nat) {struct n} : A -> JA J' n -> J' n :=
    match n return A -> JA J' n -> J' n with
    | O => fun a _ => a
    | S n => fun a jsn => pushl (f:=f J' i n) (g:=g J' i α β n) (a, jsn)
    end
  with β (n : nat) {struct n} : forall (x : JA J' n), Id (α n pt x) (i n x) :=
    match n return forall x : JA J' n, Id (α n pt x) (i n x) with
    | O => fun (x : A) => (@refl A pt)
    | S n => fun l => pglue (f J' i n) (g  J' i α β n)
      (pushr (f:=fun x => (pt, x)) (g:=i n) l)
    end
  for i.


  Definition α : forall (n : nat), A -> J n -> J (S n) :=
  fix J' (n : nat) {struct n} : Type :=
  match n with
  | O => A
  | S n1 => Pushout (f J' i n1) (g J' i α β n1)
  end
  with i (n : nat) {struct n} : JA J' n -> J' n :=
    match n return JA J' n -> J' n with
    | O => fun _ => pt
    | S n' => fun jn => @pushr _ _ _ (f J' i n') (g J' i α β n') jn
    end
  with α (n : nat) {struct n} : A -> JA J' n -> J' n :=
    match n return A -> JA J' n -> J' n with
    | O => fun a _ => a
    | S n => fun a jsn => pushl (f:=f J' i n) (g:=g J' i α β n) (a, jsn)
    end
  with β (n : nat) {struct n} : forall (x : JA J' n), Id (α n pt x) (i n x) :=
    match n return forall x : JA J' n, Id (α n pt x) (i n x) with
    | O => fun (x : A) => (@refl A pt)
    | S n => fun l => pglue (f J' i n) (g  J' i α β n)
      (pushr (f:=fun x => (pt, x)) (g:=i n) l)
    end
  for α.

  Definition β : forall (n : nat) (x : J n), Id (α n pt x) (i n x) :=
  fix J' (n : nat) {struct n} : Type :=
  match n with
  | O => A
  | S n1 => Pushout (f J' i n1) (g J' i α β n1)
  end
  with i (n : nat) {struct n} : JA J' n -> J' n :=
    match n return JA J' n -> J' n with
    | O => fun _ => pt
    | S n' => fun jn => @pushr _ _ _ (f J' i n') (g J' i α β n') jn
    end
  with α (n : nat) {struct n} : A -> JA J' n -> J' n :=
    match n return A -> JA J' n -> J' n with
    | O => fun a _ => a
    | S n => fun a jsn => pushl (f:=f J' i n) (g:=g J' i α β n) (a, jsn)
    end
  with β (n : nat) {struct n} : forall (x : JA J' n), Id (α n pt x) (i n x) :=
    match n return forall x : JA J' n, Id (α n pt x) (i n x) with
    | O => fun (x : A) => (@refl A pt)
    | S n => fun l => pglue (f J' i n) (g  J' i α β n)
      (pushr (f:=fun x => (pt, x)) (g:=i n) l)
    end
  for β.
End James.

Eval compute in J nat 1 2.
