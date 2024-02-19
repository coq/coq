(* This file showcases the use of the [run], [block] and [unblock] primitives,
   in the context of proof by reflection.

   Proof by reflection is a common, and generally very efficient technique for
   proving that a proposition from some limited domain is equivalent to (or is
   entailed by) a simpler proposition. Here, our domain will be [Prop], and we
   will restrict to conjunctions ([_ /\ _]), [True], and [False]. Our ultimate
   goal will be to provide an efficient tactic to simplify propositions by:
   - removing [True] conjuncts,
   - collapsing to [False] if any conjunct is [False].

   To make this example more self-contained, the [Logic] module below provides
   the lemmas we will need to later prove simplification correct. *)

Require Import Setoid.
Module Logic.
  Lemma iff_trivial (P : Prop) : P <-> P.
  Proof. split; intros H; exact H. Qed.

  Lemma and_comm (P1 P2 : Prop) : P1 /\ P2 <-> P2 /\ P1.
  Proof.
    split.
    - intros [H1 H2]; split; [exact H2 | exact H1].
    - intros [H2 H1]; split; [exact H1 | exact H2].
  Qed.

  Lemma and_true (P : Prop) : P /\ True <-> P.
  Proof.
    split.
    - intros [HP _]. exact HP.
    - intros HP. split; [exact HP| exact I].
  Qed.

  Lemma true_and (P : Prop) : True /\ P <-> P.
  Proof. rewrite and_comm. rewrite and_true. apply iff_trivial. Qed.

  Lemma and_false (P : Prop) : P /\ False <-> False.
  Proof.
    split.
    - intros [_ HF]. exact HF.
    - intros HF. exfalso. exact HF.
  Qed.

  Lemma false_and (P : Prop) : False /\ P <-> False.
  Proof. rewrite and_comm. rewrite and_false. apply iff_trivial. Qed.
End Logic.

(* Proof by reflection typically involves four components:
   1) a //reification// of the supported domain of propositions as a datatype,
   2) a meta-program used to //reify// a proposition into said datatype,
   3) a //denotation// (or //reflection//) function interpreting said datatype
      as a proposition,
   4) a //correct// simplification procedure defined on the datatype.

   Here, we follow exactly these steps, starting with defining the type [prop]
   of reified propositions. *)

Require Import Force.Force.

Inductive prop :=
  | conj  : prop -> prop -> prop
  | true  : prop
  | false : prop
  | inj   : Blocked Prop -> prop.

(* This type has four constructors, the first three of which correspond to the
   connectives that our simplification procedure will handle (i.e., [conj _ _]
   for [_ /\ _], [true] for [True], and [false] for [False]). The last [inj _]
   constructor is meant to represent "user-terms": propositions that are meant
   to be left untouched by our simplification procedure, as we do not have any
   way do deal with them.

   In a usual setting, without the new primitives, the type of the argument of
   [inj _] would be [Prop]. Here however, we rely on the new type [Blocked _],
   taken from the [Force.Force] module declaring the primitives, to explicitly
   mark the term as "blocked" for (kernel) reduction.

   To build a term of type [Block Prop], one must rely on primitive [block].

     block : forall {T : Type}, T -> Blocked T

   We rely on it to define our Ltac2 reification function below. Note that the
   reification process is otherwise straight-forward, and usual. *)

Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Ltac2 rec reify (p : constr) : constr :=
  lazy_match! p with
  | ?p1 /\ ?p2 => let p1 := reify p1 in let p2 := reify p2 in '(conj $p1 $p2)
  | True       => '(true)
  | False      => '(false)
  | ?p         => '(inj (block $p))
  end.

(* We now turn to the reflection function, whose role is to interpret a [prop]
   into a proposition, or more precisely, a blocked proposition. *)

Fixpoint reflect (p : prop) : Blocked Prop :=
  match p with
  | conj p1 p2 => block ((unblock (reflect p1)) /\ (unblock (reflect p2)))
  | true       => block True
  | false      => block False
  | inj P      => P
  end.

(* The use of a [Blocked Prop] (as apposed to the more usual [Prop]) allows us
   to safely force the reduction of [reflect _], while making sure that [Prop]
   connectives like [_ /\ _] will not be reduced themselves. This matters more
   in settings where the connectives can actually reduce, which is typically a
   problem in embedded logics like Iris.

   The implementation of [reflect] is straight-forward following the types:
   - In the [true]/[false] cases, a [block] must be used to protect [True] and
     [False], since they have type [Prop], and we expect a [Blocked Prop].
   - In the [inj P] case, [P] is already blocked so we just take it.
   - In the [conj p1 p2] case, we use [block] around [_ /\ _], but need to use
     the [unblock] function to turn the recursive calls into propositions.

   The [unblock] primitive is basically a destructor for the [Blocked _] type,
   similarly to how [block _] can be seen as a constructor.

     unblock : forall {T : Type}, Blocked T -> T

   In terms of reduction, the combination of [block] and [unblock] is slightly
   more subtle. In particular, an [unblock] withing a [block] will trigger the
   reduction of its argument, even if the whole term is "blocked". This has to
   do with the fact that the semantics of the new primitives rely on full lazy
   reduction, not just weak-head normalization.

   Let us now turn to the last building block of our example: [simplify]. *)

Fixpoint simplify (p : prop) : prop :=
  match p with
  | conj p1 p2 =>
      match simplify p1 with
      | true  => simplify p2
      | false => false
      | p1    =>
          match simplify p2 with
          | true  => p1
          | false => false
          | p2    => conj p1 p2
          end
      end
  | _ => p
  end.

(* The simplification function is usual as it operates on [prop]. However, its
   correctness lemma involves [unblock] since the return value of [reflect] is
   a blocked proposition. Nonetheless, the proof remains fairly usual since we
   can use [lazy] to evaluate [unblock (block p)] into [p]. *)

Lemma simplify_ok (p : prop) :
  unblock (reflect (simplify p)) <-> unblock (reflect p).
Proof.
  induction p; lazy -[iff]; fold simplify reflect.
  - rewrite <-IHp1; clear IHp1.
    rewrite <-IHp2; clear IHp2.
    destruct (simplify p1); lazy -[iff]; fold simplify reflect.
    + destruct (simplify p2); lazy -[iff]; fold simplify reflect.
      * apply Logic.iff_trivial.
      * rewrite Logic.and_true. apply Logic.iff_trivial.
      * rewrite Logic.and_false. apply Logic.iff_trivial.
      * apply Logic.iff_trivial.
    + rewrite Logic.true_and. apply Logic.iff_trivial.
    + rewrite Logic.false_and. apply Logic.iff_trivial.
    + destruct (simplify p2); lazy -[iff]; fold simplify reflect.
      * apply Logic.iff_trivial.
      * rewrite Logic.and_true. apply Logic.iff_trivial.
      * rewrite Logic.and_false. apply Logic.iff_trivial.
      * apply Logic.iff_trivial.
  - apply Logic.iff_trivial.
  - apply Logic.iff_trivial.
  - apply Logic.iff_trivial.
Qed.

(* Note that the proof requires a bit of manual refolding, due to [lazy] being
   too eager when unfolding fixpoints, but that's an independent issue.

   Now that we have all the necessary pieces, we need to setup our tactic. The
   first step is to turn our correctness lemma into a proof term that actually
   triggers the forcing of reduction, using the [run] primitive.

     run : forall {T K : Type}, Blocked T -> (T -> K) -> K
   
   The [run] primitive forces the full evaluation of the blocked term it takes
   as first (non-implicit) argument, respecting the blocked terms it contains,
   and it then feeds the result to its second (non-implicit) argument. *)

Lemma simplify_ok_run (p : prop) :
  run (block (unblock (reflect (simplify p)) -> unblock (reflect p))) id.
Proof. lazy; fold reflect simplify. apply simplify_ok. Qed.

(* The proof of [simplify_ok_run] trivially follows from [simplify_ok].

   Note that we again need a few [block] and [unblock] to make the types work.
   Said otherwise, we need to "protect" [_ -> _] similarly to what we did with
   [_ /\ _] in [reflect] earlier.

   Note also that it is essential that the type of [simplify_ok_run] is of the
   form [run _ _]. Indeed, we need [run] to get in the way of the type-checker
   when [simplify_of_run] is applied to a reified proposition, and its type is
   reduced to a (non-dependent) product.

   We can now implement our tactic by combining [simplify_ok_run] with [reify]
   in a simple Ltac2 function. *)

Ltac2 truely_simplify (p : constr) : unit :=
  let reified := reify p in
  let p := '(simplify_ok_run $reified _) in
  refine p.

(* It takes as input a term [p] representing the proposition from the goal.

   A simple Ltac wrapper can then be defined to match on the goal and call the
   [truely_simplify] Ltac2 function. *)

Ltac truely_simplify :=
  let truely_simplify :=
    ltac2:(p |- truely_simplify (Option.get (Ltac1.to_constr p)))
  in
  lazymatch goal with |- ?p => unshelve truely_simplify p end.

(* Testing the tactic on the following goal yields the expected result. *)

Goal True /\ (True /\ 1 + 1 = 2) /\ (True /\ True /\ 2 + 1 = 3).
Proof.
  truely_simplify.
  lazymatch goal with |- 1 + 1 = 2 /\ 2 + 1 = 3 => idtac | _ => fail "?!" end.
  split; reflexivity.
Qed.
