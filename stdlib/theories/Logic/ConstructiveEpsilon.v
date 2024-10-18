(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i $Id: ConstructiveEpsilon.v 12112 2009-04-28 15:47:34Z herbelin $ i*)

(** This provides with a proof of the constructive form of definite
and indefinite descriptions for Sigma^0_1-formulas (hereafter called
"small" formulas), which infers the sigma-existence (i.e.,
[Type]-existence) of a witness to a decidable predicate over a
countable domain from the regular existence (i.e.,
[Prop]-existence). *)

(** Coq does not allow case analysis on sort [Prop] when the goal is in
not in [Prop]. Therefore, one cannot eliminate [exists n, P n] in order to
show [{n : nat | P n}]. However, one can perform a recursion on an
inductive predicate in sort [Prop] so that the returning type of the
recursion is in [Type]. This trick is described in Coq'Art book, Sect.
14.2.3 and 15.4. In particular, this trick is used in the proof of
[Fix_F] in the module Coq.Init.Wf. There, recursion is done on an
inductive predicate [Acc] and the resulting type is in [Type].

To find a witness of [P] constructively, we program the well-known
linear search algorithm that tries P on all natural numbers starting
from 0 and going up.  Such an algorithm needs a suitable termination
certificate.  We offer two ways for providing this termination
certificate: a direct one, based on an ad-hoc predicate called
[before_witness], and another one based on the predicate [Acc].
For the first one we provide explicit and short proof terms. *)

(** The method based on [before_witness] (2009) can be seen as an ancestor
of the first ingredient of the Braga method, by Dominique Larchey-Wendling
and Jean-François Monin (Types'18, then in more details in [[1]]).
In this approach, the termination certificate is usually combined
with an inductive relational presentation of the recursive function
of interest. This became especially useful here since the introduction
of [epsilon_smallest], stating that the output of the linear search
algorithm is minimal, whereas in the 2009 version, the only
postcondition considered stated that the output satisfies [P].
In this file, the linear search program is named [prog_linear_search]
because [linear_search] happens to be the name of a similar but
different program in the 2009 version: both programs take as input a
natural number [start] and a termination certificate, and
the output of [prog_linear_search] is a natural number [n]
whereas the output of [linear_search] is [n] packed with a proof
of [(P n)]. The inductive relation for linear search is named [rel_ls].

The Braga method usually consists in defining a function [f_conform]
intended to be extracted as (the OCaml translation of) an n-ary
function [f], with inputs [x...] and output type [{y | R x... y}]
where [R] is an inductive n+1-ary relational presentation of [f].
An additional input of [f_conform] is a termination certificate
whose type can be derived from [R]. Partial correctness properties
are proved on [R], then transported on [f_conform] (an alternative,
not considered for linear search, is to simulate an inductive-recursive
scheme for [f_conform]).
In the present case, the Coq name of [f] is then [prog_linear_search],
[R] is [rel_ls] and the type of the termination certificate is named
[before_witness].
In simple situations such as linear search, one can as well
directly define the type of the termination certificate and
the n+1-ary Coq version of [f].
Several variants of the proofs are offered for the record:
- a version that follows the steps in [[1]], named [linear_search_conform];
- a variant of the latter, named [linear_search_conform_alt],
  where the recursive call is no longer encapsulated in a
  pattern-matching (avoiding packing-unpacking steps which
  are for instance removed at extraction at the price of
  an additional optimization step).
- a version where [prog_linear_search] is directly programmed
  and its conformity to [rel_ls] (by dependent induction on
  the termination certificate), and then the properties of
  its output are separately proven.
It is interesting to see that in the last version, the conformity
proof slightly deviates from the definition of [prog_linear_search],
resulting in an unpleasant duplication of proof obligations, because
the first pattern-matching is performed on [P_dec start] in the
function and on the termination certificate in the conformity proof.
This deviation seems to be unavoidable because crucial proof steps
require the guard argument of the fixpoint to start with a constructor.

The three programs [prog_linear_search], [linear_search_conform]
and [linear_search_conform_alt] are purposely presented in a
very similar manner, using [refine] and postponing proof obligations
related to conformity to [rel_ls].

 [[1]] Dominique Larchey-Wendling and Jean-François Monin.
     The Braga Method: Extracting Certified Algorithms from
     Complex Recursive Schemes in Coq, chapter 8, pages 305--386.
     In K. Mainzer, P. Schuster, and H. Schwichtenberg, editors.
     Proof and Computation II: From Proof Theory and Univalent
     Mathematics to Program Extraction and Verification.
     World Scientific, September 2021.
*)

(** Based on ideas from Benjamin Werner and Jean-François Monin *)

(** Contributed by Yevgeniy Makarov and Jean-François Monin *)

(* -------------------------------------------------------------------- *)

(* Direct version *)

Require Import Arith.

Section ConstructiveIndefiniteGroundDescription_Direct.

Variable P : nat -> Prop.

Hypothesis P_dec : forall n, {P n}+{~(P n)}.


(** The termination argument is [before_witness n], which says that
any number before any witness (not necessarily the [x] of [exists x :A, P x])
makes the search eventually stops. *)

Inductive before_witness (n:nat) : Prop :=
  | stop : P n -> before_witness n
  | next : before_witness (S n) -> before_witness n.

(* Computation of the initial termination certificate *)
Fixpoint O_witness (n : nat) : before_witness n -> before_witness 0 :=
  match n return (before_witness n -> before_witness 0) with
    | 0 => fun b => b
    | S n => fun b => O_witness n (next n b)
  end.

(* Inversion of [inv_before_witness n] in a way such that the result
is structurally smaller even in the [stop] case. *)
Definition inv_before_witness :
  forall n, before_witness n -> ~(P n) -> before_witness (S n) :=
  fun n b not_p =>
    match b with
      | stop _ p => match not_p p with end
      | next _ b => b
    end.

(** Basic program *)
Fixpoint prog_linear_search start (b : before_witness start) : nat :=
  match P_dec start with
    | left yes => start
    | right no => prog_linear_search (S start) (inv_before_witness start b no)
  end.

(** rel_ls = relational version of linear search *)
Inductive rel_ls : nat -> nat -> Prop :=
| Rstop : forall {found}, P found -> rel_ls found found
| Rnext : forall {start found}, ~(P start) -> rel_ls (S start) found -> rel_ls start found.

(** Following the Braga method, the output is packed with a proof of its conformity wrt rel_ls *)
Definition linear_search_conform start (b : before_witness start) : {n : nat | rel_ls start n}.
  revert start b.
  refine (fix loop start b :=
     match P_dec start with
      | left yes => exist _ start _
      | right no =>
        let (n, r) := loop (S start) (inv_before_witness start b no) in
        exist _ n _
     end).
  - apply (Rstop yes).
  - apply (Rnext no r).
Defined.

(** A variant where the computational contents is closer to [prog_linear_search]
    (no deconstruction/reconstruction of the result), using a suitable
    abstraction of the postcondition.
    The predicate [rel_ls start] is abstracted into [Q], with an additional
    implication [rq] they are equivalent (but only one direction is needed);
    and as linear search is tail recursive, [Q] can be fixed (but [rq] varies,
    behaving like a logical continuation). *)
Definition linear_search_conform_alt start (b : before_witness start) : {n : nat | rel_ls start n}.
  refine ((fun Q: nat -> Prop => _ : (forall y, rel_ls start y -> Q y) -> {n | Q n})
            (rel_ls start) (fun y r => r)).
  revert start b.
  refine (fix loop start b :=
    fun rq =>
      match P_dec start with
      | left yes => exist _ start _
      | right no => loop (S start) (inv_before_witness start b no) _
      end).
  - apply rq, (Rstop yes).
  - intros y r. apply rq, (Rnext no r).
Defined.

(** Start at 0 *)
Definition linear_search_from_0_conform (e : exists n, P n) : {n:nat | rel_ls 0 n} :=
    let b := let (n, p) := e in O_witness n (stop n p) in
    linear_search_conform 0 b.

(** Partial correctness properties *)

(** rel_ls entails P on the output *)
Theorem rel_ls_post : forall {start found}, rel_ls start found -> P found.
Proof.
  intros * rls. induction rls as [x p | x y b rls IHrls].
  - exact p.
  - exact IHrls.
Qed.

(** rel_ls entails minimality of the output *)
Lemma rel_ls_lower_bound {found start} :
  rel_ls start found -> forall {k}, P k -> start <= k -> found <= k.
Proof.
  induction 1 as [x p | x y no _ IH]; intros k pk greater.
  - exact greater.
  - destruct greater as [ | k greater].
    + case (no pk).
    + apply (IH _ pk), le_n_S, greater.
Qed.

(** For compatibility with previous version *)
Definition linear_search start (b : before_witness start) : {n : nat | P n} :=
  let (n, p) := linear_search_conform start b in exist _ n (rel_ls_post p).

(** Main definitions *)
Definition constructive_indefinite_ground_description_nat :
  (exists n, P n) -> {n:nat | P n}.
Proof.
  intro e; destruct (linear_search_from_0_conform e) as [found r]; exists found.
  apply (rel_ls_post r).
Defined.

Definition epsilon_smallest :
  (exists n : nat, P n) -> { n : nat | P n /\ forall k, P k -> n <= k }.
Proof.
  intro e; destruct (linear_search_from_0_conform e) as [found r]; exists found.
  split.
  - apply (rel_ls_post r).
  - intros k pk. apply (rel_ls_lower_bound r pk), Nat.le_0_l.
Defined.

(** NB. The previous version used a negative formulation:
    [forall k, k < n -> ~P k]
    Lemmas [le_not_lt] and [lt_not_le] can help if needed. *)

(************************************************************************)

(** In simple situations like here, a direct proof that [prog_linear_search]
    satisfies [rel_ls] can be provided.
    On the computational side of the proof, the fixpoint (coming from
    [before_witness_dep_ind]) has to come first, before the pattern matching
    on [P_dec], so we get a slight mismatch between the program
    [prog_linear_search] and the proof; in particular, there is a duplication
    for [Rstop].
 *)

Scheme before_witness_dep_ind := Induction for before_witness Sort Prop.

Lemma linear_search_rel : forall start b, rel_ls start (prog_linear_search start b).
Proof.
  intros start b.
  induction b as [n p | n b IHb] using before_witness_dep_ind;
  unfold prog_linear_search; destruct (P_dec n) as [yes | no]; fold prog_linear_search.
  - apply Rstop, yes.
  - case (no p).
  - apply Rstop, yes.
  - apply (Rnext no), IHb.
Qed.

(** Start at 0 *)
Definition linear_search_from_0 (e : exists n, P n) : nat :=
    let b := let (n, p) := e in O_witness n (stop n p) in
    prog_linear_search 0 b.

Lemma linear_search_from_0_rel (e : exists n, P n) :
  rel_ls 0 (linear_search_from_0 e).
Proof. apply linear_search_rel. Qed.

(** Main definitions *)
Definition constructive_indefinite_ground_description_nat_direct :
  (exists n, P n) -> {n:nat | P n}.
Proof.
  intro e. exists (linear_search_from_0 e).
  apply (rel_ls_post (linear_search_from_0_rel e)).
Defined.

Definition epsilon_smallest_direct :
  (exists n : nat, P n) -> { n : nat | P n /\ forall k, P k -> n <= k }.
Proof.
  intro e. exists (linear_search_from_0 e). split.
  - apply (rel_ls_post (linear_search_from_0_rel e)).
  - intros k pk.
    apply (@rel_ls_lower_bound _ 0 (linear_search_from_0_rel e) k pk), Nat.le_0_l.
Defined.

End ConstructiveIndefiniteGroundDescription_Direct.

(************************************************************************)

(* Version using the predicate [Acc] *)

Section ConstructiveIndefiniteGroundDescription_Acc.

Variable P : nat -> Prop.

Hypothesis P_decidable : forall n : nat, {P n} + {~ P n}.

(** The predicate [Acc] delineates elements that are accessible via a
given relation [R]. An element is accessible if there are no infinite
[R]-descending chains starting from it.

To use [Fix_F], we define a relation R and prove that if [exists n, P n]
then 0 is accessible with respect to R. Then, by induction on the
definition of [Acc R 0], we show [{n : nat | P n}].

The relation [R] describes the connection between the two successive
numbers we try. Namely, [y] is [R]-less then [x] if we try [y] after
[x], i.e., [y = S x] and [P x] is false. Then the absence of an
infinite [R]-descending chain from 0 is equivalent to the termination
of our searching algorithm. *)

Let R (x y : nat) : Prop := x = S y /\ ~ P y.

Local Notation acc x := (Acc R x).

Lemma P_implies_acc : forall x : nat, P x -> acc x.
Proof.
intros x H. constructor.
intros y [_ not_Px]. absurd (P x); assumption.
Qed.

Lemma P_eventually_implies_acc : forall (x : nat) (n : nat), P (n + x) -> acc x.
Proof.
intros x n; generalize x; clear x; induction n as [|n IH]; simpl.
- apply P_implies_acc.
- intros x H. constructor. intros y [fxy _].
  apply IH. rewrite fxy.
  replace (n + S x) with (S (n + x)); auto with arith.
Defined.

Corollary P_eventually_implies_acc_ex : (exists n : nat, P n) -> acc 0.
Proof.
intros H; elim H. intros x Px. apply P_eventually_implies_acc with (n := x).
replace (x + 0) with x; auto with arith.
Defined.

(** In the following statement, we use the trick with recursion on
[Acc]. This is also where decidability of [P] is used. *)

Theorem acc_implies_P_eventually : acc 0 -> {n : nat | P n}.
Proof.
intros Acc_0. pattern 0. apply Fix_F with (R := R); [| assumption].
clear Acc_0; intros x IH.
destruct (P_decidable x) as [Px | not_Px].
- exists x; simpl; assumption.
- set (y := S x).
  assert (Ryx : R y x).
  + unfold R; split; auto.
  + destruct (IH y Ryx) as [n Hn].
    exists n; assumption.
Defined.

Theorem constructive_indefinite_ground_description_nat_Acc :
  (exists n : nat, P n) -> {n : nat | P n}.
Proof.
intros H; apply acc_implies_P_eventually.
apply P_eventually_implies_acc_ex; assumption.
Defined.

End ConstructiveIndefiniteGroundDescription_Acc.

(************************************************************************)

Section ConstructiveGroundEpsilon_nat.

Variable P : nat -> Prop.

Hypothesis P_decidable : forall x : nat, {P x} + {~ P x}.

Definition constructive_ground_epsilon_nat (E : exists n : nat, P n) : nat
  := proj1_sig (constructive_indefinite_ground_description_nat P P_decidable E).

Definition constructive_ground_epsilon_spec_nat (E : (exists n, P n)) : P (constructive_ground_epsilon_nat E)
  := proj2_sig (constructive_indefinite_ground_description_nat P P_decidable E).

End ConstructiveGroundEpsilon_nat.

(************************************************************************)

Section ConstructiveGroundEpsilon.

(** For the current purpose, we say that a set [A] is countable if
there are functions [f : A -> nat] and [g : nat -> A] such that [g] is
a left inverse of [f]. *)

Variable A : Type.
Variable f : A -> nat.
Variable g : nat -> A.

Hypothesis gof_eq_id : forall x : A, g (f x) = x.

Variable P : A -> Prop.

Hypothesis P_decidable : forall x : A, {P x} + {~ P x}.

Definition P' (x : nat) : Prop := P (g x).

Lemma P'_decidable : forall n : nat, {P' n} + {~ P' n}.
Proof.
intro n; unfold P'; destruct (P_decidable (g n)); auto.
Defined.

Lemma constructive_indefinite_ground_description : (exists x : A, P x) -> {x : A | P x}.
Proof.
intro H. assert (H1 : exists n : nat, P' n).
{ destruct H as [x Hx]. exists (f x); unfold P'. rewrite gof_eq_id; assumption. }
apply (constructive_indefinite_ground_description_nat P' P'_decidable)  in H1.
destruct H1 as [n Hn]. exists (g n); unfold P' in Hn; assumption.
Defined.

Lemma constructive_definite_ground_description : (exists! x : A, P x) -> {x : A | P x}.
Proof.
  intros; apply constructive_indefinite_ground_description; firstorder.
Defined.

Definition constructive_ground_epsilon (E : exists x : A, P x) : A
  := proj1_sig (constructive_indefinite_ground_description E).

Definition constructive_ground_epsilon_spec (E : (exists x, P x)) : P (constructive_ground_epsilon E)
  := proj2_sig (constructive_indefinite_ground_description E).

End ConstructiveGroundEpsilon.

(* begin hide *)
(* Compatibility: the qualificative "ground" was absent from the initial
names of the results in this file but this had introduced confusion
with the similarly named statement in Description.v *)
Notation constructive_indefinite_description_nat :=
  constructive_indefinite_ground_description_nat (only parsing).
Notation constructive_epsilon_spec_nat :=
  constructive_ground_epsilon_spec_nat (only parsing).
Notation constructive_epsilon_nat :=
  constructive_ground_epsilon_nat (only parsing).
Notation constructive_indefinite_description :=
  constructive_indefinite_ground_description (only parsing).
Notation constructive_definite_description :=
  constructive_definite_ground_description (only parsing).
Notation constructive_epsilon_spec :=
  constructive_ground_epsilon_spec (only parsing).
Notation constructive_epsilon :=
  constructive_ground_epsilon (only parsing).
(* end hide *)
