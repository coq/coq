(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** We show that any complete Heyting algebra Heyt:Prop is a singleton:
    forall x y : Heyt, x <= y.
    In other words Heyt is degenerate, its true and false values are equal.
    As corollaries, we show that Prop does not inject into a proposition Heyt,
    and we show that the excluded middle principle implies proof irrelevance.

    This specializes the refutation by Reynolds of set semantics for System F:
    John Reynolds. Polymorphism is not set-theoretic.
    [Research Report] RR-0296, INRIA. 1984. inria-00076261
    https://hal.inria.fr/inria-00076261/document

    Here System F is replaced by Coq's universe Prop. This makes sense because
    Prop is impredicative like System F, and Prop can interpret all of System F's
    syntax. For example the forall type alpha in System F is replaced by
    forall alpha:Prop. In his article, Reynolds writes B for Heyt, and it is
    an unspecified system F type with at least 2 different terms. We do have
    those terms here: I True and I False. Our Heyt has a structure of complete
    Heyting algebra, hence does generalize the booleans of System F. *)

Require Import Coq.Relations.Relations.

Section PartialEquivalences.

(** A setoid is a type A equipped with an equivalence relation R, which is interpreted
    as equality on A. In other words, it is the quotient of a type A by an equivalence
    relation R. Here we consider a slight generalization of equivalence relations,
    called partial equivalence relations, where reflexivity is omitted. A quotient
    by an equivalence merges related elements, in addition a quotient by a per erases
    irreflexive elements. *)
Inductive per {A : Type} (R : relation A) : Prop :=
    per_intro : symmetric A R -> transitive A R -> per R.

(** exp R S is mostly used on setoids (A,R),(B,S) where R and S are partial
    equivalence relations. Then, exp R S is the extensional equality for functions
    in A -> B: for all equal inputs, the functions produce equal outputs.
    The erasure of irreflexive elements for exp R S is very elegant:
    it means we only consider functions f : A -> B that respect relations R,S,
    as expected for the quotients (A,R) and (B,S). *)
Definition exp {A B : Type} (R : relation A) (S : relation B) (f g : A -> B) : Prop :=
  forall x y : A, R x y -> S (f x) (g y).

Lemma exp_per : forall (A B : Prop) (R : relation A) (S : relation B),
    per R
    -> per S
    -> per (exp R S).
Proof.
  unfold exp.
  intros A B R S [symR transR] [symS transS].
  apply per_intro.
  - (* symmetry *)
    intros x y H0 s t H1.
    apply symS, H0, symR, H1.
  - (* transitivity *)
    intros x y z H H0 s t H1.
    apply (transS _ (y t)).
    apply H, H1.
    apply H0.
    apply (transR _ s).
    apply symR, H1.
    exact H1.
Qed.

End PartialEquivalences.


Section ReynoldsSet.

(** As Reynolds, we assume an arbitrary C:Prop (instead of a system F type B) with
    a set denotation. We use setoids to represent sets, so the denotation of C is
    given by a partial equivalence relation C_Eq. In other words, the set denotation
    of C is the quotient set (C, C_Eq).

    We generalize Reynolds, by omitting the assumption that C has at least 2 elements.
    We rename C instead of B, so that C is not interpreted as a type of booleans
    for the moment.

    In this section we define the Reynolds setoid (A0, E0), and its bijection with the
    other setoid (A0 -> C) -> C. There is no contradiction here, because C could be
    False, and then A0 = False. Or C could be True, and then A0 = True. The
    contradiction will happen in the next section, when we further assume that C has
    2 different elements. *)

Variable C : Prop.
Variable C_Eq : relation C.
Hypothesis C_Eq_per : per C_Eq.

(** power R is mostly used on a setoid (A,R), where R is a partial equivalence
    relation. Then, power R is the extensional equality on the powerset
    of A: two subsets of A are equal iff they have the same elements. *)
Definition power {A : Prop} (R : relation A) : relation (A -> C) :=
  exp R C_Eq.

Lemma power_per : forall (A : Prop) (R : relation A),
    per R
    -> per (power R).
Proof using C_Eq_per.
  intros A R H.
  apply exp_per.
  exact H.
  exact C_Eq_per.
Qed.


(* Definition of the Reynolds functor PHI (written T in Reynolds' article). *)
Definition PHI (A : Prop) := (A -> C) -> C.
Definition phi {A B : Prop} (f : A -> B) (z : PHI A) : PHI B :=
  fun u : B -> C => z (fun x : A => u (f x)).

Lemma phi_id : forall (A : Prop), phi (fun (x:A) => x) = (fun y => y).
Proof using Type. reflexivity. Qed.

Lemma phi_compose : forall (A B C : Prop) (f : A -> B) (g : B -> C) (x : PHI A),
    (phi g) (phi f x) = phi (fun y => g (f y)) x.
Proof using Type. reflexivity. Qed.

(** We want to construct a type A0 (written W in Reynolds' article) in bijection with
    PHI A0, i.e. a fixed point of type functor PHI. This well-known problem usually
    has 2 different solutions: the least fixed point of PHI and the biggest fixed
    point of PHI. We choose the simpler least fixed point, called inductive type
    Inductive A0 : Prop := A0_cons : PHI A0 -> A0
    As its name suggests, A0 has an induction principle that we call A0_ind below,
    which lifts A0 to any PHI-algebra. This is why A0 is also called the initial
    PHI-algebra.

    We use a general pattern to form inductive types in System F:
    Inductive False := .
    forall A, A.

    Inductive bool := true : bool | false : bool.
    forall A, A -> A -> A.

    Inductive nat := O : nat | S : nat -> nat.
    forall A, A -> (A -> A) -> A.

    Inductive A0 : Prop := A0_cons : PHI A0 -> A0. *)
Definition A0 : Prop := forall A : Prop, (PHI A -> A) -> A.
Definition A0_ind {X : Prop} (f : PHI X -> X) (u : A0) : X := u _ f.
Definition A0_cons (z : PHI A0) : A0 :=
  fun (A : Prop) (f : PHI A -> A) => f (phi (A0_ind f) z).

(** We remark that the definition of A0 is impredicative, as allowed by Prop
    (or System F). If we used Type instead of Prop, A0 would live in a higher
    universe than the quantified variable A. *)

(* A0_ind is a morphism of PHI-algebras *)
Lemma A0_morph_alg : forall {X : Prop} (f : PHI X -> X) (u : PHI A0),
    A0_ind f (A0_cons u) = f (phi (A0_ind f) u).
Proof using Type. reflexivity. Qed.

(** By Lambek's theorem, A0_cons : PHI A0 -> A0 is an isomorphism in the category Prop
    (or System F). In other words, A0 is the least fixed point of functor PHI.
    The inverse morphism A0_match is obtained by considering the algebra
    phi A0_cons : PHI (PHI A0) -> PHI A0,
    and taking the induction morphism from A0 to it.

    Again we remark that the definition of A0_match is impredicative. If we used Type
    instead of Prop, we could still define A0 in higher universes, but Coq would
    refuse A0_match, arguing that the subtype constrains cannot be resolved. *)
Definition A0_match : A0 -> PHI A0 := A0_ind (phi A0_cons).

(** There is a caveat however. The above would be correct if the morphism from A0 to
    another PHI-algebra, written A0_ind, would be unique. This is the difference
    between preinitial and initial algebras. As in Reynolds' article, we will refine
    A0 to get a true initial algebra. We do so by moving from the category Prop
    (or System F) to the category of sets. The idea of assigning sets to types,
    in a way compatible with beta reduction, is called denotational semantics.
    This is what Reynolds discussed in his paper, only assuming the general
    translation rules that a semantics satisfies. Here we will explicitly give the
    set semantics. Our set denotation of A0 is simply a partial equivalence relation
    E0 on A0, which turns A0 into a setoid. In other words, our set denotation of A0
    is a quotient of A0. A0_cons and A0_match induce quotient maps that are truly
    inverse from each other. In the quotient, all morphisms from A0 to any other
    PHI-algera are equalized, which turns the preinitial algebra into an initial
    algebra.

    Here is a synthesis of our set semantics, for all objects involved in our
    final refutation of Iinject
    ----------------------------------------
    System F     | Set denotation
    ----------------------------------------
    Heyt         | (Heyt, Heyt_Eq)
    A0           | (A0, E0)
    A -> B       | (A -> B, exp R S)
    A -> Heyt    | (A -> Heyt, power R)
    PHI A        | (PHI A, power (power R))
    t : A : Prop | t
    A0_cons      | A0_cons
    A0_match     | A0_match

    Proof terms t are denoted by themselves, but in the quotient they may become
    equalized to other terms, or erased when irreflexive.

    First we alias the denotation of PHI A by phi2, and check that PHI extends
    to a functor on sets. *)
Definition phi2 {A : Prop} (R : relation A) : relation (PHI A)
  := power (power R).

(* phi sends a set-function to a set-function
   (which means a function that respects the equality relations). *)
Lemma phi_set_func : forall (A B : Prop) (R : relation A) (S : relation B) (f : A -> B),
    (forall x y:A, R x y -> S (f x) (f y))
    -> forall s t : PHI A,
      phi2 R s t -> phi2 S (phi f s) (phi f t).
Proof using Type.
  intros. intros x y H1. unfold power, exp in H1.
  apply H0. intros a b H2. apply H1, H, H2.
Qed.

(** Definition of the partial equivalence relation E0 on A0, so that A0_cons and
    A0_match are inverse set-functions between (A0, E0) and (PHI A0, phi2 E0).
    This makes the set (A0, E0) an initial PHI-algebra in the category of sets.
    E0 is the intersection of all partial equivalence relations E on A0 such that
    A0_cons is a set-function and such that A0_match is the inverse of A0_cons. E0 is
    therefore the smallest such relation, so that the quotient by E0 modifies A0
    the least. We alias the relation phi2 E0 by G0. *)
Definition E0 (x1 x2 : A0) : Prop :=
  forall E : relation A0,
  per E ->
  (* Assume A0_cons is a set-function that respects relation E.
     This hypothesis prevents E from being empty. *)
  (forall z1 z2 : PHI A0, phi2 E z1 z2 -> E (A0_cons z1) (A0_cons z2)) ->
  (* Assume u and A0_cons (A0_match u) are E-equal, for all (reflexive) elements
     u of the quotient (A,E). *)
  (forall u : A0, E u u -> E u (A0_cons (A0_match u))) ->
  E x1 x2.
Definition F0 : relation (A0 -> C) := power E0. (* Equality on subsets of (A0,E0) *)
Definition G0 : relation (PHI A0) := power F0.

Lemma G0_phi2 : G0 = phi2 E0.
Proof using Type. reflexivity. Qed.

(** What follows proves that the definition of relation E0 fulfills its goal.
    A0_cons is a set-function (PHI A0, phi2 E0) -> (A0, E0) and A0_match is its
    inverse set-function. In other words, the set (A0, E0) is a fixed point
    of the set-functor PHI (and it is an initial algebra, the smallest such
    fixed point).

    First we show that E0 is a partial equivalence, necessary to define a set.
    Recall that irreflexive elements are allowed in partial equivalences: they
    are considered erased in the quotient (A0, E0). *)

Theorem sym_E0 : symmetric A0 E0.
Proof using Type.
unfold symmetric in |- *; intros x y h1.
unfold E0 in |- *; intros E h2 h3 h4.
elim h2.
unfold symmetric in |- *; intros h5 h6.
apply h5.
apply (h1 E).
exact h2.
exact h3.
exact h4.
Qed.

Theorem trans_E0 : transitive A0 E0.
Proof using Type.
unfold transitive in |- *; intros x y z h1 h2.
unfold E0 in |- *; intros E h3 h4 h5.
elim h3.
unfold symmetric, transitive in |- *; intros h6 h7.
apply h7 with y.
apply (h1 E); auto.
apply (h2 E); auto.
Qed.

Theorem per_E0 : per E0.
Proof using Type.
exact (per_intro _ sym_E0 trans_E0).
Qed.

(* A0_cons : PHI A0 -> A0 is a set-function, it respects the equality relation E0.
   In other words, A0_cons is a PHI-algebra in the category of sets. *)
Theorem A0_cons_set_func : forall z1 z2 : PHI A0,
    G0 z1 z2 -> E0 (A0_cons z1) (A0_cons z2).
Proof using Type.
unfold E0 in |- *; intros z1 x2 h1 E h2 h3 h4.
apply h3; hnf in |- *; intros x y h5.
apply h1; hnf in |- *; intros x0 y0 h6.
apply h5.
apply (h6 E); auto.
Qed.

Theorem per_F0 : per F0.
Proof using C_Eq_per.
apply power_per, per_E0.
Qed.

Theorem per_G0 : per G0.
Proof using C_Eq_per.
apply power_per, per_F0.
Qed.

(* Now the inversion theorems. First that A0_match is the right inverse of A0_cons. *)
Theorem id_A0_cons_match :
  forall x : A0, E0 x x -> E0 x (A0_cons (A0_match x)).
Proof using Type.
intros x xrefl E h1 h2 h3.
apply h3.
apply (xrefl E); auto.
Qed.

(* Then A0_match is the left inverse of A0_cons. *)
Theorem id_A0_match_cons :
  forall z : PHI A0, G0 z z -> G0 z (A0_match (A0_cons z)).
Proof using Type.
intros z zrefl x y F0xy.
apply zrefl. intros x0 y0 h3.
apply F0xy.
change (E0 x0 (A0_cons (A0_match y0))).
destruct per_E0 as [sym_E0 trans_E0].
apply (trans_E0 _ y0 _ h3).
apply id_A0_cons_match.
apply (trans_E0 _ x0).
apply sym_E0, h3.
exact h3.
Qed.

(* A0_match : A0 -> PHI A0 is a set-function, it respects the equality relation E0. *)
Theorem A0_match_set_func : forall a b : A0,
    E0 a b -> G0 (A0_match a) (A0_match b).
Proof using C_Eq_per.
intros a b aeqb.
(* E0 is an intersection of relations E,
   we simply show that the goal is one of those relations. *)
pose (fun u v : A0 => G0 (A0_match u) (A0_match v)) as E.
apply (aeqb E).
- (* E is a per *)
  destruct per_G0 as [G0sym G0trans].
  apply per_intro.
  intros x y h4.
  apply G0sym.
  exact h4.
  intros x y z h4 h5.
  apply (G0trans _ (A0_match y)).
  exact h4.
  exact h5.
- (* A0_cons respects E *)
  intros z1 z2 z1eqz2 x y xeqy.
  apply (z1eqz2 (fun u : A0 => x (A0_cons (A0_match u)))
                (fun u : A0 => y (A0_cons (A0_match u)))).
  intros x0 y0 x0eqy0.
  apply xeqy.
  apply A0_cons_set_func. exact x0eqy0.
- (* u and A0_cons (A0_match u) are E-equal *)
  intros u urefl h2.
  exact (id_A0_match_cons (A0_match u) urefl h2).
Qed.

(** We now have an initial PHI-algebra in the category of sets, i.e. a bijection
    between sets (A0, E0) and (PHI A0, phi2 E0). *)

End ReynoldsSet.

Section HeytingAlgebraSingleton.
  (** We apply the Reynolds bijection to show that any complete Heyting algebra
      Heyt:Prop is a singleton (with respect to its setoid equality Heyt_Eq).
      In other words Heyt is degenerate, its true and false values are equal.

      Because of the Heyting algebra structure, the set (A0 -> Heyt) -> Heyt is
      interpreted as the powerset of the powerset of A0, with respect to the truth
      values in Heyt. By composing the Reynolds bijection with the intersection of
      subsets, we get a surjection A0 ->> (A0 -> Heyt). And by the Lawvere fixed
      point theorem, the surjection implies a fixed point of Heyt's negation. Hence
      all truth values of Heyt must be equal. *)

Variable Heyt : Prop.

(* The order on Heyt *)
Variable Heyt_Le : relation Heyt.
Hypothesis Heyt_Le_refl : forall x : Heyt, Heyt_Le x x.
Hypothesis Heyt_Le_trans : forall x y z : Heyt,
    Heyt_Le x y -> Heyt_Le y z -> Heyt_Le x z.
Definition Heyt_Eq (x y : Heyt) : Prop := Heyt_Le x y /\ Heyt_Le y x.

(* The assumption on Heyt_Le that make it a complete Heyting algebra : all families
   of Heyt have a greatest lower bound Heyt_forall, and there is an implication
   Heyt_impl. As a consequence, Heyt also has a minimum Heyt_false and a maximum
   Heyt_true, which are Heyt_forall of the full family and of the empty family.
   There is also a binary GLB Heyt_and. *)
Variable Heyt_forall : forall {X:Prop} (f : X -> Heyt), Heyt.
Hypothesis Heyt_forall_Le : forall {X:Prop} f (x:X), Heyt_Le (Heyt_forall f) (f x).
Hypothesis Heyt_forall_max : forall {X:Prop} f,
    (forall h:Heyt, (forall x : X, Heyt_Le h (f x)) -> Heyt_Le h (Heyt_forall f)).
Inductive bbool : Prop := btrue | bfalse.
Definition Heyt_and (x y : Heyt) : Heyt :=
  Heyt_forall (fun b : bbool => if b then x else y).
Variable Heyt_impl : Heyt -> Heyt -> Heyt.
Hypothesis Heyt_impl_spec : forall x y : Heyt,
    (Heyt_Le (Heyt_and x (Heyt_impl x y)) y)
    /\ (forall z:Heyt, Heyt_Le (Heyt_and x z) y -> Heyt_Le z (Heyt_impl x y)).

Lemma Heyt_and_spec : forall x y : Heyt,
    (Heyt_Le (Heyt_and x y) x)
    /\ (Heyt_Le (Heyt_and x y) y)
    /\ (forall h:Heyt, Heyt_Le h x -> Heyt_Le h y -> Heyt_Le h (Heyt_and x y)).
Proof.
  intros x y. split. 2: split.
  - exact (Heyt_forall_Le _ btrue).
  - exact (Heyt_forall_Le _ bfalse).
  - intros. apply Heyt_forall_max. intros x0. destruct x0; assumption.
Qed.

Definition Heyt_false : Heyt := Heyt_forall (fun h:Heyt => h).
Lemma Heyt_false_spec : forall x:Heyt, Heyt_Le Heyt_false x.
Proof.
  intro x. apply (Heyt_forall_Le (fun h => h)).
Qed.
Definition Heyt_true : Heyt := Heyt_impl Heyt_false Heyt_false.
Lemma Heyt_true_spec : forall x:Heyt, Heyt_Le x Heyt_true.
Proof.
  intro x. apply Heyt_impl_spec.
  apply Heyt_and_spec.
Qed.

Definition Heyt_equiv (x y : Heyt) : Heyt
  := Heyt_and (Heyt_impl x y) (Heyt_impl y x).
Definition Heyt_is_true (x : Heyt) : Prop :=
  forall y:Heyt, Heyt_Le y x.

Lemma Heyt_Eq_per : per Heyt_Eq.
Proof using Heyt_Le_trans.
  apply per_intro.
  - intros x y H. destruct H. split; assumption.
  - intros x y z H H0. destruct H, H0.
    split; apply (Heyt_Le_trans _ y); assumption.
Qed.

Definition H0 : Prop := A0 Heyt.
Definition H0_Eq : relation H0 := E0 Heyt Heyt_Eq.
Definition H0_power_Eq : relation (H0 -> Heyt) := F0 Heyt Heyt_Eq.
Definition H0_power_power_Eq : relation (PHI Heyt H0) := G0 Heyt Heyt_Eq.

Definition H0_diag : Prop := { uv : H0*H0 | H0_Eq (fst uv) (snd uv) }.
Definition H0_power_refl : Prop := { x : H0 -> Heyt | H0_power_Eq x x }.

(** Cantor's theorem needs a surjection A0 ->> (A0 -> Heyt), which we must get
    from the bijection A0_match : A0 ~-> PHI A0. By composition this reduces to
    finding a surjection PHI A0 ->> (A0 -> Heyt). We will define it as a retraction
    of the singleton injection (A0 -> Heyt) -> PHI A0. Several such retractions
    exist, for example intersection or union of subsets, in the sense of the
    complete Heyting algebra Heyt. We choose intersection, where we only consider
    reflexive subsets P, as expected of a quotient by a per. The intersect predicate
    asserts that x:A0 is in this restricted intersection of C:PHI A0. *)
Definition singleton : (H0 -> Heyt) -> PHI Heyt H0 :=
  fun (x y : H0 -> Heyt)
  => Heyt_forall (fun uv:H0_diag => Heyt_equiv (x (fst (proj1_sig uv)))
                                           (y (snd (proj1_sig uv)))).
Definition intersect (C : PHI Heyt H0) (x : H0) : Heyt :=
    Heyt_forall (fun P : H0_power_refl => Heyt_impl (C (proj1_sig P)) (proj1_sig P x)).

(* intersect : PHI A0 -> (A0 -> Heyt) is a set-function, it respects equality
   relations. By composition, inter turns the bijection A0_match : A0 ~-> PHI A0
   into a surjection A0 ->> (A0 -> Heyt), written khi below, which directly violates
   Cantor's theorem about powersets. *)
Lemma lemma_inter :
  forall (z1 z2 : PHI Heyt H0) (x y : H0),
    H0_power_power_Eq z1 z2
    -> H0_Eq x y
    -> Heyt_Le (intersect z1 x) (intersect z2 y).
Proof.
intros z1 z2 x y z1eqz2 xeqy.
unfold intersect.
apply Heyt_forall_max.
intros [g grefl]; simpl.
apply Heyt_impl_spec.
apply (Heyt_Le_trans _ (Heyt_and (z1 g) (Heyt_impl (z1 g) (g x)))).
apply Heyt_and_spec.
apply (Heyt_Le_trans _ (z2 g)).
apply Heyt_and_spec.
apply z1eqz2. exact grefl.
apply (Heyt_Le_trans _ (Heyt_forall
                          (fun P : H0_power_refl => Heyt_impl (z1 (proj1_sig P)) (proj1_sig P x)))).
apply Heyt_and_spec.
exact (Heyt_forall_Le _ (exist (fun x => H0_power_Eq x x) g grefl)).
apply (Heyt_Le_trans _ (g x)).
apply Heyt_impl_spec.
apply grefl.
destruct (per_E0 Heyt Heyt_Eq).
apply H, xeqy.
Qed.

Theorem inter_set_func : forall z1 z2 : PHI Heyt H0,
    H0_power_power_Eq z1 z2 -> H0_power_Eq (intersect z1) (intersect z2).
Proof.
intros z1 z2 z1eqz2 x y xeqy.
split.
exact (lemma_inter z1 z2 x y z1eqz2 xeqy).
apply (lemma_inter z2 z1 y x).
destruct (per_G0 Heyt Heyt_Eq Heyt_Eq_per). apply H, z1eqz2.
destruct (per_E0 Heyt Heyt_Eq). apply H, xeqy.
Qed.

Lemma Heyt_true_impl : forall t y : Heyt,
    (forall z:Heyt, Heyt_Le z t) -> Heyt_Le (Heyt_impl t y) y.
Proof using Heyt_Le_refl Heyt_Le_trans Heyt_forall_Le Heyt_forall_max Heyt_impl_spec.
  intros.
  apply (Heyt_Le_trans _ (Heyt_and t (Heyt_impl t y))).
  2: apply Heyt_impl_spec.
  apply Heyt_and_spec. apply H.
  apply Heyt_Le_refl.
Qed.

(* Proof that intersect is surjective *)
Lemma id_intersect_singleton : forall (P : H0 -> Heyt),
    H0_power_Eq P P -> H0_power_Eq (intersect (singleton P)) P.
Proof.
  intros P Prefl x y xeqy.
  unfold intersect, singleton.
  destruct Heyt_Eq_per as [Eqsym Eqtrans].
  apply (Eqtrans _ (P x)).
  2: apply Prefl, xeqy.
  split.
  - apply (Heyt_Le_trans
             _ _ _ (Heyt_forall_Le _ (exist (fun x => H0_power_Eq x x) P Prefl))).
    simpl.
    apply Heyt_true_impl. intro z.
    apply Heyt_forall_max. intros [Q Qrefl]; simpl.
    apply Heyt_and_spec.
    apply Heyt_impl_spec.
    apply (Heyt_Le_trans _ (P (fst Q))).
    apply Heyt_and_spec.
    apply Prefl.
    destruct (per_E0 _ Heyt_Eq).
    apply H. exact Qrefl.
    apply Heyt_impl_spec.
    apply (Heyt_Le_trans _ (P (snd Q))).
    apply Heyt_and_spec.
    apply Prefl. exact Qrefl.
  - apply Heyt_forall_max. intros [Q Qrefl]; simpl.
    apply Heyt_impl_spec.
    assert (H0_Eq x x) as H2.
    { destruct (per_E0 _ Heyt_Eq). apply (H1 _ y).
      exact xeqy. apply H, xeqy. }
    apply (Heyt_Le_trans _ (Heyt_and (Heyt_equiv (P x) (Q x)) (P x))).
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (Heyt_forall
          (fun uv : H0_diag =>
             Heyt_equiv (P (fst (proj1_sig uv))) (Q (snd (proj1_sig uv)))))).
    apply Heyt_and_spec.
    exact (Heyt_forall_Le _ (exist (fun uv => H0_Eq (fst uv) (snd uv)) (x,x) H2)).
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (Heyt_and (P x) (Heyt_impl (P x) (Q x)))).
    2: apply Heyt_impl_spec.
    apply Heyt_and_spec.
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (Heyt_equiv (P x) (Q x))).
    apply (Heyt_and_spec (Heyt_equiv (P x) (Q x))).
    apply Heyt_and_spec.
Qed.

Lemma Heyt_equiv_set_func : forall a b c d : Heyt,
    Heyt_Eq a b
    -> Heyt_Eq c d
    -> Heyt_Le (Heyt_equiv a c) (Heyt_equiv b d).
Proof.
  intros. apply Heyt_and_spec.
  - apply Heyt_impl_spec.
    apply (Heyt_Le_trans _ c). 2: apply H1. clear H1 d.
    apply (Heyt_Le_trans _ (Heyt_and a (Heyt_equiv a c))).
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ b).
    apply Heyt_and_spec. apply H.
    destruct (Heyt_and_spec b (Heyt_equiv a c)). apply H2.
    clear H b.
    apply (Heyt_Le_trans _ (Heyt_and a (Heyt_impl a c))).
    2: apply Heyt_impl_spec.
    apply Heyt_and_spec.
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (Heyt_equiv a c)).
    apply (Heyt_and_spec a). apply Heyt_and_spec.
  - apply Heyt_impl_spec.
    apply (Heyt_Le_trans _ a). 2: apply H. clear H b.
    apply (Heyt_Le_trans _ (Heyt_and c (Heyt_equiv a c))).
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ d).
    apply Heyt_and_spec. apply H1.
    apply (Heyt_and_spec d).
    clear H1 d.
    apply (Heyt_Le_trans _ (Heyt_and c (Heyt_impl c a))).
    2: apply Heyt_impl_spec.
    apply Heyt_and_spec.
    apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (Heyt_equiv a c)).
    apply (Heyt_and_spec c). apply Heyt_and_spec.
Qed.

Theorem singleton_set_func : forall z1 z2 : H0 -> Heyt,
    H0_power_Eq z1 z2 -> H0_power_power_Eq (singleton z1) (singleton z2).
Proof.
  intros z1 z2 z1eqz2 x y xeqy.
  unfold singleton, Heyt_Eq.
  destruct (per_F0 _ Heyt_Eq Heyt_Eq_per) as [F0sym F0trans].
  destruct (per_E0 _ Heyt_Eq) as [E0sym E0trans].
  split.
  - apply Heyt_forall_max.
    intros [P Pdiag]; simpl.
    apply (Heyt_Le_trans _ (Heyt_equiv (z1 (fst P)) (x (snd P)))).
    exact (Heyt_forall_Le _ (exist (fun uv => H0_Eq (fst uv) (snd uv)) P Pdiag)).
    apply Heyt_equiv_set_func.
    apply z1eqz2.
    apply (E0trans _ (snd P)). exact Pdiag.
    apply E0sym, Pdiag.
    apply xeqy.
    apply (E0trans _ (fst P)).
    apply E0sym, Pdiag. exact Pdiag.
  - apply Heyt_forall_max.
    intros [P Pdiag]; simpl.
    apply (Heyt_Le_trans _ (Heyt_equiv (z2 (fst P)) (y (snd P)))).
    exact (Heyt_forall_Le _ (exist (fun uv => H0_Eq (fst uv) (snd uv)) P Pdiag)).
    apply Heyt_equiv_set_func.
    destruct Heyt_Eq_per. apply H.
    apply z1eqz2.
    apply (E0trans _ (snd P)). exact Pdiag.
    apply E0sym, Pdiag.
    destruct Heyt_Eq_per. apply H.
    apply xeqy.
    apply (E0trans _ (fst P)).
    apply E0sym, Pdiag. exact Pdiag.
Qed.

Definition psi (u : H0 -> Heyt) : H0 := A0_cons Heyt (singleton u).
Definition khi (x : H0) : H0 -> Heyt := intersect (A0_match Heyt x).

(* Proof that khi is surjective, as a composition of surjections. *)
Lemma id_khi_psi : forall (P : H0 -> Heyt),
    H0_power_Eq P P -> H0_power_Eq (khi (psi P)) P.
Proof.
  intros P H. unfold khi, psi.
  destruct (per_F0 _ Heyt_Eq Heyt_Eq_per) as [F0sym F0trans].
  apply (F0trans _ (intersect (singleton P))).
  2: apply id_intersect_singleton, H.
  apply inter_set_func.
  destruct (per_G0 _ _ Heyt_Eq_per) as [G0sym G0trans].
  apply G0sym.
  apply id_A0_match_cons.
  apply singleton_set_func, H.
Qed.

(* A generalization of Cantor's theorem to an arbitrary set Heyt. *)
Lemma Lawvere_fixpoint : forall f : Heyt -> Heyt,
    let q := (fun a:H0 => f (khi a a)) in
    H0_power_Eq q q ->
    let p := psi q in
    Heyt_Eq (f (khi p p)) (khi p p).
Proof.
  intros f q qrefl p.
  destruct Heyt_Eq_per as [Eqsym Eqtrans].
  change (f (khi p p)) with (q p).
  unfold p.
  assert (H0_Eq (psi q) (psi q)).
  { unfold psi. apply A0_cons_set_func.
    apply singleton_set_func. exact qrefl. }
  apply Eqsym.
  exact (id_khi_psi q qrefl _ _ H).
Qed.

Definition u0 : H0 -> Heyt := fun a => Heyt_impl (khi a a) Heyt_false.

Lemma u0_refl : H0_power_Eq u0 u0.
Proof.
  intros x y xeqy. split.
  - unfold u0. apply Heyt_impl_spec.
    apply (Heyt_Le_trans _ (Heyt_and (khi x x) (Heyt_impl (khi x x) Heyt_false))).
    2: apply Heyt_impl_spec.
    apply Heyt_and_spec.
    2: apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (khi y y)).
    apply Heyt_and_spec.
    unfold khi.
    apply inter_set_func. apply A0_match_set_func.
    exact Heyt_Eq_per. exact xeqy. exact xeqy.
  - unfold u0. apply Heyt_impl_spec.
    apply (Heyt_Le_trans _ (Heyt_and (khi y y) (Heyt_impl (khi y y) Heyt_false))).
    2: apply Heyt_impl_spec.
    apply Heyt_and_spec.
    2: apply Heyt_and_spec.
    apply (Heyt_Le_trans _ (khi x x)).
    apply Heyt_and_spec.
    unfold khi.
    destruct (per_E0 _ Heyt_Eq).
    apply inter_set_func. apply A0_match_set_func.
    exact Heyt_Eq_per. apply H, xeqy. apply H, xeqy.
Qed.

Lemma Heyt_singleton : forall x : Heyt, Heyt_Eq x Heyt_false.
Proof.
  intro x. split. 2: apply Heyt_false_spec.
  pose proof (Lawvere_fixpoint (fun (x:Heyt) => Heyt_impl x Heyt_false) u0_refl).
  pose (psi (fun a : H0 => (fun x : Heyt => Heyt_impl x Heyt_false) (khi a a))) as p.
  simpl in H; fold p in H.
  assert (Heyt_Le (khi p p) Heyt_false) as khippFalse.
  { apply (Heyt_Le_trans _ (Heyt_and (khi p p) (Heyt_impl (khi p p) Heyt_false))).
    2: apply Heyt_impl_spec.
    apply Heyt_and_spec. apply Heyt_Le_refl. apply H. }
  apply (Heyt_Le_trans _ (khi p p)). 2: exact khippFalse.
  apply (Heyt_Le_trans _ (Heyt_impl (khi p p) Heyt_false)).
  2: apply H.
  apply Heyt_impl_spec.
  apply (Heyt_Le_trans _ (khi p p)). 2: exact khippFalse.
  apply Heyt_and_spec.
Qed.

End HeytingAlgebraSingleton.


(** We now show that a function I : Prop -> Heyt cannot be injective. For if it were,
    Prop's complete Heyting algebra would be injected into Heyt, and Heyt would be
    a singleton. But since I is injective, Heyt has 2 different values at least :
    I True and I False. *)
Lemma Reynolds : forall (Heyt : Prop) (I : Prop -> Heyt),
    ~forall (P Q : Prop), I P = I Q -> (P <-> Q).
Proof.
  intros Heyt I Iinject.
  (* The injection I has a left inverse T (a.k.a. a retract). This extends Prop's
     Heyting algebra from the image of I to all of Heyt, simply by equalizing
     Heyt's elements outside I with false. *)
  pose (fun (b : Heyt) => exists P:Prop, P /\ b = I P) as T.
  assert (forall x:Prop, x <-> (T (I x))) as id_T_I.
  { split. intro Px. exists x. split. exact Px. reflexivity.
    intros [y [Py xy]]. apply Iinject in xy.
    apply xy, Py. }
  pose (fun (x y : Heyt) => (T x) -> (T y)) as Heyt_Le.
  pose (fun (X:Prop) f => I (forall x:X, T (f x))) as Heyt_forall.
  (* Because I is injective, the true and false of Heyt are different. *)
  assert (~Heyt_Eq _ Heyt_Le (I True) (Heyt_forall Heyt (fun h => h))) as trueNeqFalse.
  { intros [abs _]. unfold Heyt_Le, Heyt_forall in abs.
    pose proof (id_T_I True) as [H _].
    specialize (abs (H Logic.I)).
    apply id_T_I in abs.
    specialize (abs (I False)).
    apply id_T_I in abs.
    contradiction. }
  contradict trueNeqFalse.
  assert (forall x : Heyt, Heyt_Le x x) as le_refl.
  { intros x H. exact H. }
  assert (forall x y z : Heyt, Heyt_Le x y -> Heyt_Le y z -> Heyt_Le x z) as le_trans.
  { intros x y z H H0 H1. apply H0, H, H1. }
  assert (forall (X : Prop) (f : X -> Heyt) (x : X), Heyt_Le (Heyt_forall _ f) (f x))
    as forall_le.
  { intros. intro H. apply id_T_I in H. apply H. }
  assert (forall (X : Prop) (f : X -> Heyt) (h : Heyt),
             (forall x : X, Heyt_Le h (f x)) -> Heyt_Le h (I (forall x : X, T (f x)))) as forall_max.
  { intros. intro H0.
    destruct (id_T_I (forall x : X, T (f x))). apply H1.
    intros. apply H, H0. }
  apply (Heyt_singleton Heyt Heyt_Le le_refl le_trans
                        Heyt_forall forall_le forall_max
                        (fun x y => I (T x -> T y))).
  split.
  - intro H. apply id_T_I in H.
    pose proof (H btrue). simpl in H1.
    specialize (H bfalse). simpl in H. apply id_T_I in H.
    apply H, H1.
  - intros z H H0.
    destruct (id_T_I (T x -> T y)) as [H1 _]; apply H1; clear H1.
    intro H1. apply H. unfold Heyt_and.
    destruct (id_T_I (forall x0 : bbool, T (if x0 then x else z))).
    apply H2. intros. destruct x0. exact H1. exact H0.
Qed.


(** Excluded middle implies proof irrelevance.
    Unfortunately we cannot use the Reynolds contradiction to derive proof
    irrelevance without assuming the excluded middle, because constructively
    it is consistent (and anti-classical) that (nat -> 2) -> 2 is in bijection
    with nat. *)
Lemma EM_PI : (forall P:Prop, P \/ ~P) -> forall (Q:Prop) (a b : Q), a = b.
Proof.
  intros EM Q a b.
  (* By excluded middle, we refute the negation. *)
  destruct (EM (a = b)) as [aeqb | aneqb].
  exact aeqb. exfalso.
  (* Now we have assumed a and b are different, and that plus EM allow to define
     an injection I : Prop->Q, which violates Reynolds. *)
  pose (fun P:Prop => if EM P then a else b) as I.
  apply (Reynolds Q I). intros.
  unfold I in H.
  destruct (EM P), (EM Q0).
  - split; intros; assumption.
  - exfalso. contradict aneqb. exact H.
  - exfalso. contradict aneqb. symmetry. exact H.
  - split; intros; contradiction.
Qed.
