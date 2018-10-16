(* Test apply in *)

Goal (forall x y, x = S y -> y=y) -> 2 = 4 -> 3=3.
intros H H0.
apply H in H0.
assumption.
Qed.

Require Import ZArith.
Goal (forall x y z, ~ z <= 0 -> x * z < y * z -> x <= y)%Z.
intros; apply Znot_le_gt, Z.gt_lt in H.
apply Zmult_lt_reg_r, Z.lt_le_incl in H0; auto.
Qed.

(* Test application under tuples *)

Goal (forall x, x=0 <-> 0=x) -> 1=0 -> 0=1.
intros H H'.
apply H in H'.
exact H'.
Qed.

(* Test as clause *)

Goal (forall x, x=0 <-> (0=x /\ True)) -> 1=0 -> True.
intros H H'.
apply H in H' as (_,H').
exact H'.
Qed.

(* Test application modulo conversion *)

Goal (forall x, id x = 0 -> 0 = x) -> 1 = id 0 -> 0 = 1.
intros H H'.
apply H in H'.
exact H'.
Qed.

(* Check apply/eapply distinction in presence of open terms *)

Parameter h : forall x y z : nat, x = z -> x = y.
Arguments h {x y}.
Goal 1 = 0 -> True.
intro H.
apply h in H || exact I.
Qed.

Goal False -> 1 = 0.
intro H.
apply h || contradiction.
Qed.

(* Check if it unfolds when there are not enough premises *)

Goal forall n, n = S n -> False.
intros.
apply n_Sn in H.
assumption.
Qed.

(* Check naming in with bindings; printing used to be inconsistent before *)
(* revision 9450 *)

Notation S':=S (only parsing).
Goal (forall S, S = S' S) -> (forall S, S = S' S).
intros.
apply H with (S0 := S).
Qed.

(* Check inference of implicit arguments in bindings *)

Goal exists y : nat -> Type, y 0 = y 0.
exists (fun x => True).
trivial.
Qed.

(* Check universe handling in typed unificationn *)

Definition E := Type.
Goal exists y : E, y = y.
exists Prop.
trivial.
Qed.

Variable Eq : Prop = (Prop -> Prop) :> E.
Goal Prop.
rewrite Eq.
Abort.

(* Check insertion of coercions in bindings *)

Coercion eq_true : bool >-> Sortclass.
Goal exists A:Prop, A = A.
exists true.
trivial.
Qed.

(* Check use of unification of bindings types in specialize *)

Module Type Test.
Variable P : nat -> Prop.
Variable L : forall (l : nat), P l -> P l.
Goal P 0 -> True.
intros.
specialize L with (1:=H).
Abort.
End Test.

(* Two examples that show that hnf_constr is used when unifying types
   of bindings (a simplification of a script from Field_Theory) *)

Require Import List.
Open Scope list_scope.
Fixpoint P (l : list nat) : Prop :=
  match l with
  | nil => True
  | e1 :: nil => e1 = e1
  | e1 :: l1 => e1 = e1 /\ P l1
  end.
Variable L : forall n l, P (n::l) -> P l.

Goal forall (x:nat) l, P (x::l) -> P l.
intros.
apply L with (1:=H).
Qed.

Goal forall (x:nat) l, match l with nil => x=x | _::_ => x=x /\ P l end -> P l.
intros.
apply L with (1:=H).
Qed.

(* The following call to auto fails if the type of the clause
   associated to the H is not beta-reduced [but apply H works]
   (a simplification of a script from FSetAVL) *)

Definition apply (f:nat->Prop) := forall x, f x.
Goal apply (fun n => n=0) -> 1=0.
intro H.
auto.
Qed.

(* The following fails if the coercion Zpos is not introduced around p
   before trying a subterm that matches the left-hand-side of the equality
   (a simplication of an example taken from Nijmegen/QArith) *)

Require Import ZArith.
Coercion Zpos : positive >-> Z.
Variable f : Z -> Z -> Z.
Variable g : forall q1 q2 p : Z, f (f q1 p) (f q2 p) = Z0.
Goal forall p q1 q2, f (f q1 (Zpos p)) (f q2 (Zpos p)) = Z0.
intros; rewrite g with (p:=p).
reflexivity.
Qed.

(* A funny example where the behavior differs depending on which of a
   multiple solution to a unification problem is chosen (an instance
   of this case can be found in the proof of Buchberger.BuchRed.nf_divp) *)

Definition succ x := S x.
Goal forall (I : nat -> Set) (P : nat -> Prop) (Q : forall n:nat, I n -> Prop),
  (forall x y, P x -> Q x y) ->
  (forall x, P (S x)) -> forall y: I (S 0), Q (succ 0) y.
intros.
apply H with (y:=y).
(* [x] had two possible instances: [S 0], coming from unifying the
   type of [y] with [I ?n] and [succ 0] coming from the unification with
   the goal; only the first one allows the next apply (which
   does not work modulo delta) work *)
apply H0.
Qed.

(* A similar example with a arbitrary long conversion between the two
   possible instances *)

Fixpoint compute_succ x :=
  match x with O => S 0 | S n => S (compute_succ n) end.

Goal forall (I : nat -> Set) (P : nat -> Prop) (Q : forall n:nat, I n -> Prop),
  (forall x y, P x -> Q x y) ->
  (forall x, P (S x)) -> forall y: I (S 100), Q (compute_succ 100) y.
intros.
apply H with (y:=y).
apply H0.
Qed.

(* Another example with multiple convertible solutions to the same
   metavariable (extracted from Algebra.Hom_module.Hom_module, 10th
   subgoal which precisely fails) *)

Definition ID (A:Type) := A.
Goal forall f:Type -> Type,
  forall (P : forall A:Type, A -> Prop),
  (forall (B:Type) x, P (f B) x -> P (f B) x) ->
  (forall (A:Type) x, P (f (f A)) x) ->
  forall (A:Type) (x:f (f A)), P (f (ID (f A))) x.
intros.
apply H.
(* The parameter [B] had two possible instances: [ID (f A)] by direct
   unification and [f A] by unification of the type of [x]; only the
   first choice makes the next command fail, as it was
   (unfortunately?) in Hom_module *)
try apply H.
unfold ID; apply H0.
Qed.

(* Test hyp in "apply -> ... in hyp" is correctly instantiated by Ltac *)

Goal (True <-> False) -> True -> False.
intros Heq H.
match goal with [ H : True |- _ ] => apply -> Heq in H end.
Abort.

(* Test coercion below product and on non meta-free terms in with bindings *)
(* Cf wishes #1408 from E. Makarov *)

Parameter bool_Prop :> bool -> Prop.
Parameter r : bool -> bool -> bool.
Axiom ax : forall (A : Set) (R : A -> A -> Prop) (x y : A), R x y.

Theorem t : r true false.
apply ax with (R := r).
Qed.

(* Check verification of type at unification (submitted by Stéphane Lengrand):
   without verification, the first "apply" works what leads to the incorrect
   instantiation of x by Prop *)

Theorem u : ~(forall x:Prop, ~x).
unfold not.
intro.
eapply H.
apply (forall B:Prop,B->B) || (instantiate (1:=True); exact I).
Defined.

(* Fine-tuning coercion insertion in presence of unfolding (bug #1883) *)

Parameter name : Set.
Definition atom := name.

Inductive exp : Set :=
  | var : atom -> exp.

Coercion var : atom >-> exp.

Axiom silly_axiom : forall v : exp, v = v -> False.

Lemma silly_lemma : forall x : atom, False.
intros x.
apply silly_axiom with (v := x).  (* fails *)
reflexivity.
Qed.

(* Check that unification does not commit too early to a representative
   of an eta-equivalence class that would be incompatible with other
   unification constraints *)

Lemma eta : forall f : (forall P, P 1),
  (forall P, f P = f P) ->
   forall Q, f (fun x => Q x) = f (fun x => Q x).
intros.
apply H.
Qed.

(* Test propagation of evars from subgoal to brother subgoals *)

  (* This works because unfold calls clos_norm_flags which calls nf_evar *)

Lemma eapply_evar_unfold : let x:=O in O=x -> 0=O.
intros x H; eapply eq_trans;
[apply H | unfold x;match goal with |- ?x = ?x => reflexivity end].
Qed.

(* Test non-regression of (temporary) bug 1981 *)

Goal exists n : nat, True.
eapply ex_intro.
exact O.
trivial.
Qed.

(* Check pattern-unification on evars in apply unification *)

Lemma evar : exists f : nat -> nat, forall x, f x = 0 -> x = 0.
Proof.
eexists; intros x H.
apply H.
Qed.

(* Check that "as" clause applies to main premise only and leave the
   side conditions away *)

Lemma side_condition : 
  forall (A:Type) (B:Prop) x, (True -> B -> x=0) -> B -> x=x.
Proof.
intros.
apply H in H0 as ->.
reflexivity.
exact I.
Qed.

(* Check that "apply" is chained on the last subgoal of each lemma and
   that side conditions come first (as it is the case since 8.2) *)

Lemma chaining : 
  forall A B C : Prop,
  (1=1 -> (2=2 -> A -> B) /\ True) ->
  (3=3 -> (True /\ (4=4 -> C -> A))) -> C -> B.
Proof.
intros.
apply H, H0.
exact (refl_equal 1).
exact (refl_equal 2).
exact (refl_equal 3).
exact (refl_equal 4).
assumption.
Qed.

(* Check that the side conditions of "apply in", even when chained and
   used through conjunctions, come last (as it is the case for single
   calls to "apply in" w/o destruction of conjunction since 8.2) *)

Lemma chaining_in :
  forall A B C : Prop, 
  (1=1 -> True /\ (B -> 2=2 -> 5=0)) ->
  (3=3 -> (A -> 4=4 -> B) /\ True) -> A -> 0=5.
Proof.
intros.
apply H0, H in H1 as ->.
exact (refl_equal 0).
exact (refl_equal 1).
exact (refl_equal 2).
exact (refl_equal 3).
exact (refl_equal 4).
Qed.

(* From 12612, Dec 2009, descent in conjunctions is more powerful *)
(* The following, which was failing badly in bug 1980, is now
   properly rejected, as descend in conjunctions builds an
   ill-formed elimination from Prop to the domain of ex which is in Type. *)

Goal True.
Fail eapply ex_intro.
exact I.
Qed.

Goal True.
Fail eapply (ex_intro _).
exact I.
Qed.

(* No failure here, because the domain of ex is in Prop *)

Goal True.
eapply (ex_intro (fun _ => 0=0) I).
reflexivity.
Qed.

Goal True.
eapply (ex_intro (fun _ => 0=0) I _).
Unshelve. (* In 8.4:  Grab Existential Variables. *)
reflexivity.
Qed.

Goal True.
eapply (fun (A:Prop) (x:A) => conj I x).
Unshelve. (* In 8.4: the goal ?A was there *)
exact I.
Qed.

(* Testing compatibility mode with v8.4 *)

Goal True.
Fail eapply existT.
Set Universal Lemma Under Conjunction.
eapply existT.
Abort.

(* The following was not accepted from r12612 to r12657 *)

Record sig0 := { p1 : nat; p2 : p1 = 0 }.

Goal forall x : sig0, p1 x = 0.
intro x;
apply x.
Qed.

(* The following worked in 8.2 but was not accepted from r12229 to
   r12926 because "simple apply" started to use pattern unification of
   evars. Evars pattern unification for simple (e)apply was disabled
   in 12927 but "simple eapply" below worked from 12898 to 12926
   because pattern-unification also started supporting abstraction
   over Metas. However it did not find the "simple" solution and hence
   the subsequent "assumption" failed. *)

Goal exists f:nat->nat, forall x y, x = y -> f x = f y.
intros; eexists; intros.
simple eapply (@f_equal nat).
assumption.
Existential 1 := fun x => x.
Qed.

(* The following worked in 8.2 but was not accepted from r12229 to
   r12897 for the same reason because eauto uses "simple apply". It
   worked from 12898 to 12926 because eauto uses eassumption and not
   assumption. *)

Goal exists f:nat->nat, forall x y, x = y -> f x = f y.
intros; eexists; intros.
eauto.
Existential 1 := fun x => x.
Qed.

(* The following was accepted before r12612 but is still not accepted in r12658

Goal forall x : { x:nat | x = 0}, proj1_sig x = 0.
intro x;
apply x.

*)

Section A.

Variable map : forall (T1 T2 : Type) (f : T1 -> T2) (t11 t12 : T1),
  identity (f t11) (f t12).

Variable mapfuncomp : forall (X Y Z : Type) (f : X -> Y) (g : Y -> Z) (x x' : X),
  identity (map Y Z g (f x) (f x')) (map X Z (fun x0 : X => g (f x0)) x x').

Goal forall X:Type, forall Y:Type, forall f:X->Y, forall x : X, forall x' : X, 
  forall g : Y -> X,
  let gf := (fun x : X => g (f x)) : X -> X in
   identity (map Y X g (f x) (f x')) (map X X gf x x').
intros.
apply mapfuncomp.
Abort.

End A.

(* Check "with" clauses refer to names as they are printed *)

Definition hide p := forall n:nat, p = n.

Goal forall n, (forall n, n=0) -> hide n -> n=0.
unfold hide.
intros n H H'.
(* H is displayed as (forall n, n=0) *)
apply H with (n:=n).
Undo.
(* H' is displayed as (forall n0, n=n0) *)
apply H' with (n0:=0).
Qed.

(* Check that evars originally present in goal do not prevent apply in to work*)

Goal (forall x, x <= 0 -> x = 0) -> exists x, x <= 0 -> 0 = 0.
intros.
eexists.
intros.
apply H in H0.
Abort.

(* Check correct failure of apply in when hypothesis is dependent *)

Goal forall H:0=0, H = H.
intros.
Fail apply eq_sym in H.
Abort.

(* Check that unresolved evars not originally present in goal prevent
   apply in to work*)

Goal (forall x y, x <= 0 -> x + y = 0) -> exists x, x <= 0 -> 0 = 0.
intros.
eexists.
intros.
Fail apply H in H0.
Abort.

(* Check naming pattern in apply in *)

Goal ((False /\ (True -> True))) -> True -> True.
intros F H.
apply F in H as H0. (* Check that H0 is not used internally *)
exact H0.
Qed.

Goal ((False /\ (True -> True/\True))) -> True -> True/\True.
intros F H.
apply F in H as (?,?).
split.
exact H. (* Check that generated names are H and H0 *)
exact H0.
Qed.

(* This failed at some time in between 18 August 2014 and 2 September 2014 *)

Goal forall A B C: Prop, (True -> A -> B /\ C) -> A -> B.
intros * H.
apply H.
Abort.

(* This failed between 2 and 3 September 2014 *)

Goal forall A B C D:Prop, (A<->B)/\(C<->D) -> A -> B.
intros.
apply H in H0.
pose proof I as H1. (* Test that H1 does not exist *)
Abort.

Goal forall A B C D:Prop, (A<->B)/\(C<->D) -> A.
intros.
apply H.
pose proof I as H0. (* Test that H0 does not exist *)
Abort.

(* The first example below failed at some time in between 18 August
   2014 and 2 September 2014 *)

Goal forall x, 2=0 -> x+1=2 -> (forall x, S x = 0) -> True.
intros x H H0 H1.
eapply eq_trans in H. 2:apply H0.
rewrite H1 in H.
change (x+0=0) in H. (* Check the result in H1 *)
Abort.

Goal forall x, 2=x+1 -> (forall x, S x = 0) -> 2 = 0.
intros x H H0.
eapply eq_trans. apply H.
rewrite H0.
change (x+0=0).
Abort.

(* 2nd order apply used to have delta on local definitions even though
   it does not have delta on global definitions; keep it by
   compatibility while finding a more uniform way to proceed. *)

Goal forall f:nat->nat, (forall P x, P (f x)) -> let x:=f 0 in x = 0.
intros f H x.
apply H.
Qed.

(* Test that occur-check is not too restrictive (see comments of #3141) *)
Lemma bar (X: nat -> nat -> Prop) (foo:forall x, X x x) (a: unit) (H: tt = a):
  exists x, exists y, X x y.
Proof.
intros; eexists; eexists ?[y]; case H.
apply (foo ?y).
Grab Existential Variables.
exact 0.
Qed.

(* Test position of new hypotheses when using "apply ... in ... as ..." *)
Goal (True -> 0=0 /\ True) -> True -> False -> True/\0=0.
intros H H0 H1.
apply H in H0 as (a,b).
(* clear H1:False *) match goal with H:_ |- _ => clear H end.
split.
- (* use b:True *) match goal with H:_ |- _ => exact H end.
- (* clear b:True *) match goal with H:_ |- _ => clear H end.
  (* use a:0=0 *) match goal with H:_ |- _ => exact H end.
Qed.

(* Test choice of most dependent solution *)
Goal forall n, n = 0 -> exists p, p = n /\ p = 0.
intros. eexists ?[p]. split. rewrite H.
reflexivity. (* Compatibility tells [?p:=n] rather than [?p:=0] *)
exact H. (* this checks that the goal is [n=0], not [0=0] *)
Qed.

(* Check insensitivity to alphabetic order of names*)
(* In both cases, the last name is conventionally chosen *)
(* Before 8.9, the name coming first in alphabetic order *)
(* was chosen. *)
Goal forall m n, m = n -> n = 0 -> exists p, p = n /\ p = 0.
intros. eexists ?[p]. split. rewrite H.
reflexivity.
exact H0.
Qed.

Goal forall n m, n = m -> m = 0 -> exists p, p = m /\ p = 0.
intros. eexists ?[p]. split. rewrite H.
reflexivity.
exact H0.
Qed.
