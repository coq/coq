(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Notations.
Require Import Logic.

(** Useful tactics *)

(* A shorter name for generalize + clear, can be seen as an anti-intro *)

Tactic Notation "revert" ne_hyp_list(l) := generalize l; clear l.

(* to contradict an hypothesis without copying its type. *)

Ltac absurd_hyp h := 
  let T := type of h in 
  absurd T.

(* A useful complement to absurd_hyp. Here t : ~ A where H : A. *)
Ltac false_hyp H t :=
absurd_hyp H; [apply t | assumption].

(* Transforming a negative goal [ H:~A |- ~B ] into a positive one [ B |- A ]*)

Ltac swap H := intro; apply H; clear H.

(* A case with no loss of information. *)

Ltac case_eq x := generalize (refl_equal x); pattern x at -1; case x.

(* A tactic for easing the use of lemmas f_equal, f_equal2, ... *)

Ltac f_equal := 
  let cg := try congruence in
  let r := try reflexivity in 
  match goal with 
   | |- ?f ?a = ?f' ?a' => cut (a=a'); [cg|r]
   | |- ?f ?a ?b = ?f' ?a' ?b' => 
      cut (b=b');[cut (a=a');[cg|r]|r]
   | |- ?f ?a ?b ?c = ?f' ?a' ?b' ?c'=> 
      cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]
   | |- ?f ?a ?b ?c ?d= ?f' ?a' ?b' ?c' ?d'=> 
      cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]|r]
   | |- ?f ?a ?b ?c ?d ?e= ?f' ?a' ?b' ?c' ?d' ?e'=> 
      cut (e=e');[cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]|r]|r]
   | |- ?f ?a ?b ?c ?d ?e ?g= ?f' ?a' ?b' ?c' ?d' ?e' ?g' => 
      cut (f=f');[cut (e=e');[cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]|r]|r]|r]
   | _ => idtac
  end.

(* Specializing universal hypothesis. 
   The word "specialize" is already used for a not-documented-anymore 
   tactic still used in some users contribs. Any idea for a better name?
*)

Tactic Notation "narrow" hyp(H) "with" constr(x) := 
 generalize (H x); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) := 
 generalize (H x y); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) constr(z):= 
 generalize (H x y z); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) constr(z) constr(t):= 
 generalize (H x y z t); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) constr(z) constr(t) constr(u):= 
 generalize (H x y z t u); clear H; intro H.

(* Rewriting in all hypothesis several times everywhere *)

Tactic Notation "rewrite_all" constr(eq) := repeat rewrite eq in *.
Tactic Notation "rewrite_all" "<-" constr(eq) := repeat rewrite <- eq in *.

(* Keeping a copy of an expression *)

Ltac remembertac x a :=
  let x := fresh x in
  let H := fresh "Heq" x in
  (set (x:=a) in *; assert (H: x=a) by reflexivity; clearbody x).

Tactic Notation "remember" constr(c) "as" ident(x) := remembertac x c.

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
| _ => fail "The given statement does not seem to end with an equivalence"
end.

Ltac bapply lemma todo :=
let H := fresh in
  pose proof lemma as H;
  find_equiv H; [todo H; clear H | .. ].

Tactic Notation "apply" "->" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H).

Tactic Notation "apply" "<-" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H).

Tactic Notation "apply" "->" constr(lemma) "in" ident(J) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H in J).

Tactic Notation "apply" "<-" constr(lemma) "in" ident(J) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H in J).

(** A tactic simpler than auto that is useful for ending proofs "in one step" *)
Tactic Notation "now" tactic(t) :=
t;
match goal with
| H : _ |- _ => solve [inversion H]
| _ => solve [trivial | reflexivity | symmetry; trivial | discriminate | split]
| _ => fail 1 "Cannot solve this goal"
end.
