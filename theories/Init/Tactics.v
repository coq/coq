(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Notations.
Require Import Logic.
Require Import Specif.

(** * Useful tactics *)

(** Ex falso quodlibet : a tactic for proving False instead of the current goal.
    This is just a nicer name for tactics such as [elimtype False]
    and other [cut False]. *)

Ltac exfalso := elimtype False.

(** A tactic for proof by contradiction. With contradict H,
    -   H:~A |-  B    gives       |-  A
    -   H:~A |- ~B    gives  H: B |-  A
    -   H: A |-  B    gives       |- ~A
    -   H: A |- ~B    gives  H: B |- ~A
    -   H:False leads to a resolved subgoal.
   Moreover, negations may be in unfolded forms,
   and A or B may live in Type *)

Ltac contradict H :=
  let save tac H := let x:=fresh in intro x; tac H; rename x into H
  in
  let negpos H := case H; clear H
  in
  let negneg H := save negpos H
  in
  let pospos H :=
    let A := type of H in (exfalso; revert H; try fold (~A))
  in
  let posneg H := save pospos H
  in
  let neg H := match goal with
   | |- (~_) => negneg H
   | |- (_->False) => negneg H
   | |- _ => negpos H
  end in
  let pos H := match goal with
   | |- (~_) => posneg H
   | |- (_->False) => posneg H
   | |- _ => pospos H
  end in
  match type of H with
   | (~_) => neg H
   | (_->False) => neg H
   | _ => (elim H;fail) || pos H
  end.

(* Transforming a negative goal [ H:~A |- ~B ] into a positive one [ B |- A ]*)

Ltac swap H :=
  idtac "swap is OBSOLETE: use contradict instead.";
  intro; apply H; clear H.

(* To contradict an hypothesis without copying its type. *)

Ltac absurd_hyp H :=
  idtac "absurd_hyp is OBSOLETE: use contradict instead.";
  let T := type of H in
  absurd T.

(* A useful complement to contradict. Here H:A while G allows concluding ~A *)

Ltac false_hyp H G :=
  let T := type of H in absurd T; [ apply G | assumption ].

(* A case with no loss of information. *)

Ltac case_eq x := generalize (eq_refl x); pattern x at -1; case x.

(* use either discriminate or injection on a hypothesis *)

Ltac destr_eq H := discriminate H || (try (injection H; clear H; intro H)).

(* Similar variants of destruct *)

Tactic Notation "destruct_with_eqn" constr(x) :=
  destruct x eqn:?.
Tactic Notation "destruct_with_eqn" ident(n) :=
  try intros until n; destruct n eqn:?.
Tactic Notation "destruct_with_eqn" ":" ident(H) constr(x) :=
  destruct x eqn:H.
Tactic Notation "destruct_with_eqn" ":" ident(H) ident(n) :=
  try intros until n; destruct n eqn:H.

(** Break every hypothesis of a certain type *)

Ltac destruct_all t :=
 match goal with
  | x : t |- _ => destruct x; destruct_all t
  | _ => idtac
 end.

(* Rewriting in all hypothesis several times everywhere *)

Tactic Notation "rewrite_all" constr(eq) := repeat rewrite eq in *.
Tactic Notation "rewrite_all" "<-" constr(eq) := repeat rewrite <- eq in *.

(** Tactics for applying equivalences.

The following code provides tactics "apply -> t", "apply <- t",
"apply -> t in H" and "apply <- t in H". Here t is a term whose type
consists of nested dependent and nondependent products with an
equivalence A <-> B as the conclusion. The tactics with "->" in their
names apply A -> B while those with "<-" in the name apply B -> A. *)

(* The idea of the tactics is to first provide a term in the context
whose type is the implication (in one of the directions), and then
apply it. The first idea is to produce a statement "forall ..., A ->
B" (call this type T) and then do "assert (H : T)" for a fresh H.
Thus, T can be proved from the original equivalence and then used to
perform the application. However, currently in Ltac it is difficult
to produce such T from the original formula.

Therefore, we first pose the original equivalence as H. If the type of
H is a dependent product, we create an existential variable and apply
H to this variable. If the type of H has the form C -> D, then we do a
cut on C. Once we eliminate all products, we split (i.e., destruct)
the conjunction into two parts and apply the relevant one. *)

Ltac find_equiv H :=
let T := type of H in
lazymatch T with
| ?A -> ?B =>
  let H1 := fresh in
  let H2 := fresh in
  cut A;
  [intro H1; pose proof (H H1) as H2; clear H H1;
   rename H2 into H; find_equiv H |
   clear H]
| forall x : ?t, _ =>
  let a := fresh "a" with
      H1 := fresh "H" in
    evar (a : t); pose proof (H a) as H1; unfold a in H1;
    clear a; clear H; rename H1 into H; find_equiv H
| ?A <-> ?B => idtac
| _ => fail "The given statement does not seem to end with an equivalence."
end.

Ltac bapply lemma todo :=
let H := fresh in
  pose proof lemma as H;
  find_equiv H; [todo H; clear H | .. ].

Tactic Notation "apply" "->" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H).

Tactic Notation "apply" "<-" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H).

Tactic Notation "apply" "->" constr(lemma) "in" hyp(J) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H in J).

Tactic Notation "apply" "<-" constr(lemma) "in" hyp(J) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H in J).

(** An experimental tactic simpler than auto that is useful for ending
    proofs "in one step" *)

Ltac easy :=
  let rec use_hyp H :=
    match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ => try solve [inversion H]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ /\ _ |- _  => exact H || (destruct_hyp H; use_hyps)
    | H : _ |- _ => solve [inversion H]
    | _ => idtac
    end in
  let rec do_atom :=
    solve [reflexivity | symmetry; trivial] ||
    contradiction ||
    (split; do_atom)
  with do_ccl := trivial with eq_true; repeat do_intro; do_atom in
  (use_hyps; do_ccl) || fail "Cannot solve this goal".

Tactic Notation "now" tactic(t) := t; easy.

(** Slightly more than [easy]*)

Ltac easy' := repeat split; simpl; easy || now destruct 1.

(** A tactic to document or check what is proved at some point of a script *)

Ltac now_show c := change c.

(** Support for rewriting decidability statements *)

Set Implicit Arguments.

Lemma decide_left : forall (C:Prop) (decide:{C}+{~C}),
  C -> forall P:{C}+{~C}->Prop, (forall H:C, P (left _ H)) -> P decide.
Proof.
intros; destruct decide. apply H0. contradiction.
Qed.

Lemma decide_right : forall (C:Prop) (decide:{C}+{~C}),
  ~C -> forall P:{C}+{~C}->Prop, (forall H:~C, P (right _ H)) -> P decide.
Proof.
intros; destruct decide. contradiction. apply H0.
Qed.

Tactic Notation "decide" constr(lemma) "with" constr(H) :=
  let try_to_merge_hyps H :=
     try (clear H; intro H) ||
     (let H' := fresh H "bis" in intro H'; try clear H') ||
     (let H' := fresh in intro H'; try clear H') in
  match type of H with
  | ~ ?C => apply (decide_right lemma H); try_to_merge_hyps H
  | ?C -> False => apply (decide_right lemma H); try_to_merge_hyps H
  | _ => apply (decide_left lemma H); try_to_merge_hyps H
  end.

(** Clear an hypothesis and its dependencies *)

Tactic Notation "clear" "dependent" hyp(h) :=
 let rec depclear h :=
  clear h ||
  match goal with
   | H : context [ h ] |- _ => depclear H; depclear h
  end ||
  fail "hypothesis to clear is used in the conclusion (maybe indirectly)"
 in depclear h.

(** Revert an hypothesis and its dependencies :
    this is actually generalize dependent... *)

Tactic Notation "revert" "dependent" hyp(h) :=
 generalize dependent h.
