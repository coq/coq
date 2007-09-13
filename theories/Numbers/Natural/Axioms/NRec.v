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

Axiom recursion_succ :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).

(* It may be possible to formulate recursion_0 and recursion_succ as follows:
Axiom recursion_0 :
  forall (a : A) (f : N -> A -> A),
    EA a a -> forall x : N, x == 0 -> EA (recursion a f x) a.

Axiom recursion_succ :
  forall (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n m : N, n == S m -> EA (recursion a f n) (f m (recursion a f m)).

Then it is possible to prove recursion_wd (see IotherInd.v). This
raises some questions:

(1) Can the axioms recursion_wd, recursion_0 and recursion_succ (both
variants) proved for all reasonable implementations?

(2) Can these axioms be proved without assuming that EA is symmetric
and transitive? In OtherInd.v, recursion_wd can be proved from
recursion_0 and recursion_succ by assuming symmetry and transitivity.

(2) Which variant requires proving less for each implementation? Can
it be that proving all three axioms about recursion has some common
parts which have to be repeated? *)

Implicit Arguments recursion_wd [A].
Implicit Arguments recursion_0 [A].
Implicit Arguments recursion_succ [A].

Definition if_zero (A : Set) (a b : A) (n : N) : A :=
  recursion a (fun _ _ => b) n.

Add Morphism if_zero with signature LE_succet ==> LE_succet ==> E ==> LE_succet as if_zero_wd.
Proof.
unfold LE_succet.
intros; unfold if_zero; now apply recursion_wd with (EA := (@eq A));
[| unfold eq_fun2; now intros |].
Qed.

Theorem if_zero_0 : forall (A : Set) (a b : A), if_zero A a b 0 = a.
Proof.
unfold if_zero; intros; now rewrite recursion_0.
Qed.

Theorem if_zero_succ : forall (A : Set) (a b : A) (n : N), if_zero A a b (S n) = b.
Proof.
intros; unfold if_zero.
now rewrite (recursion_succ (@eq A)); [| | unfold fun2_wd; now intros].
Qed.

Implicit Arguments if_zero [A].

(* To prove this statement, we need to provably different terms,
e.g., true and false *)
Theorem succ_0 : forall n, ~ S n == 0.
Proof.
intros n H.
assert (true = false); [| discriminate].
replace true with (if_zero false true (S n)) by apply if_zero_succ.
pattern false at 2; replace false with (if_zero false true 0) by apply if_zero_0.
change (LE_succet bool (if_zero false true (S n)) (if_zero false true 0)).
rewrite H. unfold LE_succet. reflexivity.
Qed.

Theorem succ_inj : forall m n, S m == S n -> m == n.
Proof.
intros m n H.
setoid_replace m with (A (S m)) by (symmetry; apply pred_succ).
setoid_replace n with (A (S n)) by (symmetry; apply pred_succ).
now apply pred_wd.
Qed.

(* The following section is devoted to defining a function that, given
two numbers whose some equals 1, decides which number equals 1. The
main property of the function is also proved .*)

(* First prove a theorem with ordinary disjunction *)
Theorem plus_eq_1 :
  forall m n : N, m + n == 1 ->  (m == 0 /\ n == 1) \/ (m == 1 /\ n == 0).
induct m.
intros n H; rewrite plus_0_l in H; left; now split.
intros n IH m H; rewrite plus_succ_l in H; apply succ_inj in H;
apply plus_eq_0 in H; destruct H as [H1 H2];
now right; split; [apply succ_wd |].
Qed.

Definition plus_eq_1_dec (m n : N) : bool := recursion true (fun _ _ => false) m.

Theorem plus_eq_1_dec_step_wd : fun2_wd E eq_bool eq_bool (fun _ _ => false).
Proof.
unfold fun2_wd; intros. unfold eq_bool. reflexivity.
Qed.

Add Morphism plus_eq_1_dec with signature E ==> E ==> eq_bool as plus_eq_1_dec_wd.
Proof.
unfold fun2_wd, plus_eq_1_dec.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
unfold eq_bool; reflexivity.
unfold eq_fun2; unfold eq_bool; reflexivity.
assumption.
Qed.

Theorem plus_eq_1_dec_0 : forall n : N, plus_eq_1_dec 0 n = true.
Proof.
intro n. unfold plus_eq_1_dec.
now apply recursion_0.
Qed.

Theorem plus_eq_1_dec_succ : forall m n : N, plus_eq_1_dec (S n) m = false.
Proof.
intros n m. unfold plus_eq_1_dec.
now rewrite (recursion_succ eq_bool);
[| unfold eq_bool | apply plus_eq_1_dec_step_wd].
Qed.

Theorem plus_eq_1_dec_correct :
  forall m n : N, m + n == 1 ->
    (plus_eq_1_dec m n = true  -> m == 0 /\ n == 1) /\
    (plus_eq_1_dec m n = false -> m == 1 /\ n == 0).
Proof.
intros m n; induct m.
intro H. rewrite plus_0_l in H.
rewrite plus_eq_1_dec_0.
split; [intros; now split | intro H1; discriminate H1].
intros m _ H. rewrite plus_eq_1_dec_succ.
split; [intro H1; discriminate | intros _ ].
rewrite plus_succ_l in H. apply succ_inj in H.
apply plus_eq_0 in H; split; [apply succ_wd | ]; tauto.
Qed.

Definition times_eq_0_dec (n m : N) : bool :=
  recursion true (fun _ _ => recursion false (fun _ _ => false) m) n.

Lemma times_eq_0_dec_wd_step :
  forall y y', y == y' ->
    eq_bool (recursion false (fun _ _ => false) y)
            (recursion false (fun _ _ => false) y').
Proof.
intros y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
now unfold eq_bool.
unfold eq_fun2. intros. now unfold eq_bool.
assumption.
Qed.

Add Morphism times_eq_0_dec with signature E ==> E ==> eq_bool
as times_eq_0_dec_wd.
unfold fun2_wd, times_eq_0_dec.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (EA := eq_bool).
now unfold eq_bool.
unfold eq_fun2; intros. now apply times_eq_0_dec_wd_step.
assumption.
Qed.

Theorem times_eq_0_dec_correct :
  forall n m, n * m == 0 ->
    (times_eq_0_dec n m = true ->  n == 0) /\
    (times_eq_0_dec n m = false -> m == 0).
Proof.
nondep_induct n; nondep_induct m; unfold times_eq_0_dec.
rewrite recursion_0; split; now intros.
intro n; rewrite recursion_0; split; now intros.
intro; rewrite recursion_0; rewrite (recursion_succ eq_bool);
[split; now intros | now unfold eq_bool | unfold fun2_wd; unfold eq_bool; now intros].
intro m; rewrite (recursion_succ eq_bool).
rewrite times_succ_l. rewrite plus_succ_r. intro H; now apply succ_0 in H.
now unfold eq_bool.
unfold fun2_wd; intros; now unfold eq_bool.
Qed.
