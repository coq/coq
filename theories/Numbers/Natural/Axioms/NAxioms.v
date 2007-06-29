Require Export NDomain.

(*********************************************************************
*                            Peano Axioms                            *
*********************************************************************)

Module Type NatSignature.
Declare Module Export DomainModule : DomainSignature.

Parameter Inline O : N.
Parameter Inline S : N -> N.

Notation "0" := O.
Notation "1" := (S O).

Add Morphism S with signature E ==> E as S_wd.

(* It is natural to formulate induction for well-defined predicates
only because standard induction
forall P, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n
does not hold in the setoid context (for example, there is no reason
for (P x) hold when x == 0 but x <> 0). However, it is possible to
formulate induction without mentioning well-defidedness (see OtherInd.v);
this formulation is equivalent. *)
Axiom induction :
  forall P : N -> Prop, pred_wd E P ->
    P 0 -> (forall n : N, P n -> P (S n)) -> forall n : N, P n.

(* Why do we separate induction and recursion?

(1) When induction and recursion are the same, they are dependent
(nondependent induction does not make sense). However, one must impose
conditions on the predicate, or codomain, that it respects the setoid
equality. For induction this means considering predicates P for which
forall n n', n == n' -> (P n <-> P n') holds. For recursion, where P :
nat -> Set, we cannot say (P n <-> P n'). It may make sense to require
forall n n', n == n' -> (P n = P n').

(2) Unlike induction, recursion requires that two equalities hold:
[recursion a f 0 == a] and [recursion a f (S n) == f n (recursion a f n)]
(or something like this). It may be difficult to state, let alone prove,
these equalities because the left- and the right-hand sides may have
different types (P t1) and (P t2) where t1 == t2 is provable but t1 and t2
are not convertible into each other. Nevertheless, these equalities may
be proved using dependent equality (EqdepFacts) or JM equality (JMeq).
However, requiring this for any implementation of natural numbers seems
a little complex. It may make sense to devote a separate module to dependent
recursion (see DepRec.v). *)

Parameter Inline recursion : forall A : Set, A -> (N -> A -> A) -> N -> A.

Implicit Arguments recursion [A].

(* Suppose the codomain A has a setoid equality relation EA. If A is a
function space C -> D, it makes sense to consider extensional
functional equality as EA. Indeed, suppose, for example, that we say
[Definition g (x : N) : C -> D := (recursion ... x ...)]. We would
like to show that the function g of two arguments is well-defined.
This requirement is the same as the requirement that the functions of
one argument (g x) and (g x') are extensionally equal whenever x ==
x', i.e.,

forall x x' : N, x == x' -> eq_fun (g x) (g x'),

which is the same as

forall x x' : N, x == x' -> forall y y' : C, EC y y' -> ED (g x y) (g x' y')

where EC and ED are setoid equalities on C and D, respectively.

Now, if we consider EA to be extensional equality on the function
space, we cannot require that EA is reflexive. Indeed, reflexivity of
EA:

forall f : C -> D, eq_fun f f

or

forall f : C -> D, forall x x', EC x x' -> ED (f x) (f x')

means that every function f ; C -> D is well-defined, which is in
general false. We can expect that EA is symmetric and transitive,
i.e., that EA is a partial equivalence relation (PER). However, there
seems to be no need to require this in the following axioms.

When we defined a function by recursion, the arguments of this
function may occur in the recursion's base case a, the counter x, or
the step function f. For example, in the following definition:

Definition plus (x y : N) := recursion y (fun _ p => S p) x.

one argument becomes the base case and the other becomes the counter.

In the definitions of times:

Definition times (x y : N) := recursion 0 (fun x p => plus y p) x.

the argument y occurs in the step function. Thus it makes sense to
formulate an axiom saying that (recursion a f x) is equal to
(recursion a' f' x') whenever (EA a a'), x == x', and eq_fun2 f f'. We
need to vary all three arguments; for example, claiming that
(recursion a f x) equals (recursion a' f x') with the same f whenever
(EA a a') and x == x' is not enough to prove well-defidedness of
multiplication defined above.

This leads to the axioms given below. There is a question if it is
possible to formulate simpler axioms that would imply this statement
for any implementation. Indeed, the proof seems to have to proceed by
straighforward induction on x. The difficulty is that we cannot prove
(EA (recursion a f x) (recursion a' f' x')) using the induction axioms
above because recursion is not declared to be a setoid morphism:
that's what we are proving! Therefore, this has to be proved by
induction inside each particular implementation. *)

Axiom recursion_wd : forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : N -> A -> A, eq_fun2 E EA EA f f' ->
      forall x x' : N, x == x' ->
        EA (recursion a f x) (recursion a' f' x').

(* Can we instead declare recursion as a morphism? It does not seem
so. For this, we need to register the relation EA, and for this we
need to declare it as a variable in a section. But information about
morhisms is lost when sections are closed. *)

(* When the function recursion is polymorphic on the codomain A, there
seems no other option than to return the given base case a when the
counter is 0. Therefore, we can formulate the following axioms with
Leibniz equality. *)

Axiom recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f 0 = a.

Axiom recursion_S :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).

(* It may be possible to formulate recursion_0 and recursion_S as follows:
Axiom recursion_0 :
  forall (a : A) (f : N -> A -> A),
    EA a a -> forall x : N, x == 0 -> EA (recursion a f x) a.

Axiom recursion_S :
  forall (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n m : N, n == S m -> EA (recursion a f n) (f m (recursion a f m)).

Then it is possible to prove recursion_wd (see IotherInd.v). This
raises some questions:

(1) Can the axioms recursion_wd, recursion_0 and recursion_S (both
variants) proved for all reasonable implementations?

(2) Can these axioms be proved without assuming that EA is symmetric
and transitive? In OtherInd.v, recursion_wd can be proved from
recursion_0 and recursion_S by assuming symmetry and transitivity.

(2) Which variant requires proving less for each implementation? Can
it be that proving all three axioms about recursion has some common
parts which have to be repeated? *)

Implicit Arguments recursion_wd [A].
Implicit Arguments recursion_0 [A].
Implicit Arguments recursion_S [A].

End NatSignature.

Module NatProperties (Export NatModule : NatSignature).

Module Export  DomainPropertiesModule := DomainProperties DomainModule.

(* This tactic applies the induction axioms and solves the resulting
goal "pred_wd E P" *)
Ltac induct n :=
  try intros until n;
  pattern n; apply induction; clear n;
  [unfold NumPrelude.pred_wd;
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in intros n m H; qmorphism n m | |].

Definition if_zero (A : Set) (a b : A) (n : N) : A :=
  recursion a (fun _ _ => b) n.

Add Morphism if_zero with signature LE_Set ==> LE_Set ==> E ==> LE_Set as if_zero_wd.
Proof.
unfold LE_Set.
intros; unfold if_zero; now apply recursion_wd with (EA := (@eq A));
[| unfold eq_fun2; now intros |].
Qed.

Theorem if_zero_0 : forall (A : Set) (a b : A), if_zero A a b 0 = a.
Proof.
unfold if_zero; intros; now rewrite recursion_0.
Qed.

Theorem if_zero_S : forall (A : Set) (a b : A) (n : N), if_zero A a b (S n) = b.
Proof.
intros; unfold if_zero.
now rewrite (recursion_S (@eq A)); [| | unfold fun2_wd; now intros].
Qed.

Implicit Arguments if_zero [A].

(* To prove this statement, we need to provably different terms,
e.g., true and false *)
Theorem S_0 : forall n, ~ S n == 0.
Proof.
intros n H.
assert (true = false); [| discriminate].
replace true with (if_zero false true (S n)) by apply if_zero_S.
pattern false at 2; replace false with (if_zero false true 0) by apply if_zero_0.
change (LE_Set bool (if_zero false true (S n)) (if_zero false true 0)).
rewrite H. unfold LE_Set. reflexivity.
Qed.

Definition pred (n : N) : N := recursion 0 (fun m _ => m) n.

Add Morphism pred with signature E ==> E as pred_wd.
Proof.
intros; unfold pred.
now apply recursion_wd with (EA := E); [| unfold eq_fun2; now intros |].
Qed.

Theorem pred_0 : pred 0 == 0.
Proof.
unfold pred; now rewrite recursion_0.
Qed.

Theorem pred_S : forall n, pred (S n) == n.
Proof.
intro n; unfold pred; now rewrite (recursion_S E); [| unfold fun2_wd; now intros |].
Qed.

Theorem S_inj : forall m n, S m == S n -> m == n.
Proof.
intros m n H.
setoid_replace m with (pred (S m)) by (symmetry; apply pred_S).
setoid_replace n with (pred (S n)) by (symmetry; apply pred_S).
now apply pred_wd.
Qed.

Theorem not_eq_S : forall n m, n # m -> S n # S m.
Proof.
intros n m H1 H2. apply S_inj in H2. now apply H1.
Qed.

Theorem not_eq_Sn_n : forall n, S n # n.
Proof.
induct n.
apply S_0.
intros n IH H. apply S_inj in H. now apply IH.
Qed.

Theorem not_all_eq_0 : ~ forall n, n == 0.
Proof.
intro H; apply (S_0 0). apply H.
Qed.

Theorem not_0_implies_S : forall n, n # 0 <-> exists m, n == S m.
Proof.
intro n; split.
induct n; [intro H; now elim H | intros n _ _; now exists n].
intro H; destruct H as [m H]; rewrite H; apply S_0.
Qed.

Theorem nondep_induction :
  forall P : N -> Prop, NumPrelude.pred_wd E P ->
    P 0 -> (forall n, P (S n)) -> forall n, P n.
Proof.
intros; apply induction; auto.
Qed.

Ltac nondep_induct n :=
  try intros until n;
  pattern n; apply nondep_induction; clear n;
  [unfold NumPrelude.pred_wd;
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in intros n m H; qmorphism n m | |].

Theorem O_or_S : forall n, n == 0 \/ exists m, n == S m.
Proof.
nondep_induct n; [now left | intros n; right; now exists n].
Qed.

(* The following is useful for reasoning about, e.g., Fibonacci numbers *)
Section DoubleInduction.
Variable P : N -> Prop.
Hypothesis P_correct : NumPrelude.pred_wd E P.

Add Morphism P with signature E ==> iff as P_morphism.
Proof.
exact P_correct.
Qed.

Theorem double_induction :
  P 0 -> P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
Proof.
intros until 3.
assert (D : forall n, P n /\ P (S n)); [ |intro n; exact (proj1 (D n))].
induct n; [ | intros n [IH1 IH2]]; auto.
Qed.

End DoubleInduction.

(* The following is useful for reasoning about, e.g., Ackermann function *)
Section TwoDimensionalInduction.
Variable R : N -> N -> Prop.
Hypothesis R_correct : rel_wd E R.

Add Morphism R with signature E ==> E ==> iff as R_morphism.
Proof.
exact R_correct.
Qed.

Theorem two_dim_induction :
   R 0 0 ->
   (forall n m, R n m -> R n (S m)) ->
   (forall n, (forall m, R n m) -> R (S n) 0) -> forall n m, R n m.
Proof.
intros H1 H2 H3. induct n.
induct m.
exact H1. exact (H2 0).
intros n IH. induct m.
now apply H3. exact (H2 (S n)).
Qed.

End TwoDimensionalInduction.

End NatProperties.
