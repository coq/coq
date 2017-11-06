(* -*- mode: coq; coq-prog-args: ("-noinit" "-indices-matter" "-w" "-notation-overridden,-deprecated-option") -*- *)
(*
    The Coq Proof Assistant, version 8.7.1 (January 2018)
    compiled on Jan 21 2018 15:02:24 with OCaml 4.06.0
    from commit 391bb5e196901a3a9426295125b8d1c700ab6992
 *)


Require Export Coq.Init.Notations.
Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Reserved Notation "p @ q" (at level 60, right associativity).
Reserved Notation "! p " (at level 50).

Monomorphic Universe uu.
Monomorphic Universe uu0.
Monomorphic Universe uu1.
Constraint uu0 < uu1.

Global Set Universe Polymorphism.
Global Set Polymorphic Inductive Cumulativity.
Global Unset Universe Minimization ToSet.

Notation UU  := Type (only parsing).
Notation UU0 := Type@{uu0} (only parsing).

Global Set Printing Universes.

 Inductive unit : UU0 := tt : unit.

Inductive paths@{i} {A:Type@{i}} (a:A) : A -> Type@{i} := idpath : paths a a.
Hint Resolve idpath : core .
Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Record total2@{i} { T: Type@{i} } ( P: T -> Type@{i} ) : Type@{i}
  := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Definition foo (X:Type) (xy : @total2 X (λ _, X)) : X.
  induction xy as [x y].
  exact x.
Defined.

Unset Automatic Introduction.

Definition idfun (T : UU) := λ t:T, t.

Definition pathscomp0 {X : UU} {a b c : X} (e1 : a = b) (e2 : b = c) : a = c.
Proof.
  intros. induction e1. exact e2.
Defined.

Hint Resolve @pathscomp0 : pathshints.

Notation "p @ q" := (pathscomp0 p q).

Definition pathsinv0 {X : UU} {a b : X} (e : a = b) : b = a.
Proof.
  intros. induction e. exact (idpath _).
Defined.

Notation "! p " := (pathsinv0 p).

Definition maponpaths {T1 T2 : UU} (f : T1 -> T2) {t1 t2 : T1}
           (e: t1 = t2) : f t1 = f t2.
Proof.
  intros. induction e. exact (idpath _).
Defined.

Definition map_on_two_paths {X Y Z : UU} (f : X -> Y -> Z) {x x' y y'} (ex : x = x') (ey: y = y') :
  f x y = f x' y'.
Proof.
  intros. induction ex. induction ey. exact (idpath _).
Defined.


Definition maponpathscomp0 {X Y : UU} {x1 x2 x3 : X}
           (f : X -> Y) (e1 : x1 = x2) (e2 : x2 = x3) :
  maponpaths f (e1 @ e2) = maponpaths f e1 @ maponpaths f e2.
Proof.
  intros. induction e1. induction e2. exact (idpath _).
Defined.

Definition maponpathsinv0 {X Y : UU} (f : X -> Y)
           {x1 x2 : X} (e : x1 = x2) : maponpaths f (! e) = ! (maponpaths f e).
Proof.
  intros. induction e. exact (idpath _).
Defined.



Definition constr1 {X : UU} (P : X -> UU) {x x' : X} (e : x = x') :
  ∑ (f : P x -> P x'),
  ∑ (ee : ∏ p : P x, tpair _ x p = tpair _ x' (f p)),
  ∏ (pp : P x), maponpaths pr1 (ee pp) = e.
Proof.
  intros. induction e.
  split with (idfun (P x)).
  split with (λ p, idpath _).
  unfold maponpaths. simpl.
  intro. exact (idpath _).
Defined.

Definition transportf@{i} {X : Type@{i}} (P : X -> Type@{i}) {x x' : X}
           (e : x = x') : P x -> P x' := pr1 (constr1 P e).

Lemma two_arg_paths_f@{i} {A : Type@{i}} {B : A -> Type@{i}} {C:Type@{i}} {f : ∏ a, B a -> C} {a1 b1 a2 b2}
      (p : a1 = a2) (q : transportf B p b1 = b2) : f a1 b1 = f a2 b2.
Proof.
  intros. induction p. induction q. exact (idpath _).
Defined.

Definition iscontr@{i} (T:Type@{i}) : Type@{i} := ∑ cntr:T, ∏ t:T, t=cntr.

Lemma proofirrelevancecontr {X : UU} (is : iscontr X) (x x' : X) : x = x'.
Proof.
  intros.
  induction is as [y fe].
  exact (fe x @ !(fe x')).
Defined.


Definition hfiber@{i} {X Y : Type@{i}} (f : X -> Y) (y : Y) : Type@{i} := total2 (λ x, f x = y).

Definition hfiberpair {X Y : UU} (f : X -> Y) {y : Y}
           (x : X) (e : f x = y) : hfiber f y :=
  tpair _ x e.

Definition coconustot (T : UU) (t : T) := ∑ t' : T, t' = t.

Definition coconustotpair (T : UU) {t t' : T} (e: t' = t) : coconustot T t
  := tpair _ t' e.

Lemma connectedcoconustot {T : UU} {t : T} (c1 c2 : coconustot T t) : c1 = c2.
Proof.
  intros.
  induction c1 as [x0 x].
  induction x.
  induction c2 as [x1 y].
  induction y.
  exact (idpath _).
Defined.

Definition isweq@{i} {X Y : Type@{i}} (f : X -> Y) : Type@{i} :=
  ∏ y : Y, iscontr (hfiber f y).

Lemma isProofIrrelevantUnit : ∏ x x' : unit, x = x'.
Proof.
  intros. induction x. induction x'. exact (idpath _).
Defined.

Lemma unitl0 : tt = tt -> coconustot _ tt.
Proof.
  intros e. exact (coconustotpair unit e).
Defined.

Lemma unitl1: coconustot _ tt -> tt = tt.
Proof.
  intro cp. induction cp as [x t]. induction x. exact t.
Defined.

Lemma unitl2: ∏ e : tt = tt, unitl1 (unitl0 e) = e.
Proof.
  intros. unfold unitl0. simpl. exact (idpath _).
Defined.

Lemma unitl3: ∏ e : tt = tt, e = idpath tt.
Proof.
  intros.

  assert (e0 : unitl0 (idpath tt) = unitl0 e).
  { simple refine (connectedcoconustot _ _). }

  set (e1 := maponpaths unitl1 e0).

  exact (! (unitl2 e) @ (! e1) @ (unitl2 (idpath _))).
Defined.

Theorem iscontrpathsinunit (x x' : unit) : iscontr (x = x').
Proof.
  intros.
  split with (isProofIrrelevantUnit x x').
  intros e'.
  induction x.
  induction x'.
  simpl.
  apply unitl3.
Qed.

Lemma ifcontrthenunitl0 (e1 e2 : tt = tt) : e1 = e2.
Proof.
  intros.
  simple refine (proofirrelevancecontr _ _ _).
  exact (iscontrpathsinunit tt tt).
Qed.

Section isweqcontrtounit.

  Universe i.

  (* To see the bug, run it both with and without this constraint: *)

  (* Constraint uu0 < i. *)

  (* Without this constraint, we get i = uu0 in the next definition *)
  Lemma isweqcontrtounit@{} {T : Type@{i}} (is : iscontr@{i} T) : isweq@{i} (λ _:T, tt).
  Proof.
    intros. intro y. induction y.
    induction is as [c h].
    split with (hfiberpair@{i i i} _ c (idpath tt)).
    intros ha.
    induction ha as [x e].
    simple refine (two_arg_paths_f (h x) _).
    simple refine (ifcontrthenunitl0 _ _).
  Defined.

  (*
     Explanation of the bug:

     With the constraint uu0 < i above we get:

            |= uu0 <= bug.3
               uu0 <= i
               uu1 <= i
               i <= bug.3

     from this print statement: *)

         Print isweqcontrtounit.

  (*

     Without the constraint uu0 < i above we get:

            |= i <= bug.3
               uu0 = i

     Since uu0 = i is not inferred when we impose the constraint uu0 < i,
     it is invalid to infer it when we don't.

   *)

  Context (X : Type@{uu1}).

  Check (@isweqcontrtounit X). (* detect a universe inconsistency *)

End isweqcontrtounit.
