
Theorem t1 : forall (A : Set) (a : A) (f : A -> A), f a = a -> f (f a) = a.
intros.
 congruence.
Qed.

Theorem t2 :
 forall (A : Set) (a b : A) (f : A -> A) (g : A -> A -> A),
 a = f a -> g b (f a) = f (f a) -> g a b = f (g b a) -> g a b = a.
intros.
 congruence.
Qed.

(* 15=0 /\ 10=0 /\ 6=0 -> 0=1 *)

Theorem t3 :
 forall (N : Set) (o : N) (s d : N -> N),
 s (s (s (s (s (s (s (s (s (s (s (s (s (s (s o)))))))))))))) = o ->
 s (s (s (s (s (s (s (s (s (s o))))))))) = o ->
 s (s (s (s (s (s o))))) = o -> o = s o.
intros.
 congruence.
Qed.

(* Examples that fail due to dependencies *)

(* yields transitivity problem *)

Theorem dep :
 forall (A : Set) (P : A -> Set) (f g : forall x : A, P x)
   (x y : A) (e : x = y) (e0 : f y = g y), f x = g x.
intros;  dependent rewrite e; exact e0.
Qed.

(* yields congruence problem *)

Theorem dep2 :
 forall (A B : Set)
   (f : forall (A : Set) (b : bool), if b then unit else A -> unit)
   (e : A = B), f A true = f B true.
intros;  rewrite e; reflexivity.
Qed.


(* example that Congruence. can solve
	(dependent function applied to the same argument)*)

Theorem dep3 :
 forall (A : Set) (P : A -> Set) (f g : forall x : A, P x),
 f = g -> forall x : A, f x = g x.		intros.
 congruence.
Qed.

(* Examples with injection rule *)

Theorem inj1 :
 forall (A : Set) (a b c d : A), (a, c) = (b, d) -> a = b /\ c = d.
intros.
split;  congruence.
Qed.

Theorem inj2 :
 forall (A : Set) (a c d : A) (f : A -> A * A),
 f = pair (B:=A) a -> Some (f c) = Some (f d) -> c = d.
intros.
 congruence.
Qed.

(* Examples with discrimination rule *)

Theorem discr1 : true = false -> False.
intros.
 congruence.
Qed.

Theorem discr2 : Some true = Some false -> False.
intros.
 congruence.
Qed.

(* example with implications *)

Theorem arrow : forall (A B: Prop) (C D:Set) , A=B -> C=D  ->
(A -> C) = (B -> D).
congruence.
Qed.


Set Implicit Arguments.

Parameter elt: Set.
Parameter elt_eq: forall (x y: elt), {x = y} + {x <> y}.
Definition t (A: Set) := elt -> A.
Definition get (A: Set) (x: elt) (m: t A) := m x.
Definition set (A: Set) (x: elt) (v: A) (m: t A) :=
    fun (y: elt) => if elt_eq y x then v else m y.
Lemma gsident:
  forall (A: Set) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
Proof.
  intros. unfold get, set. case (elt_eq j i); intro.
  congruence.
  auto.
Qed.

(* bug 2447 is now closed (PC, 2014) *)

Section bug_2447.

Variable T:Type.

Record R := mkR {x:T;y:T;z:T}.

Variables a a' b b' c c':T.



Lemma bug_2447: mkR a b c = mkR a' b c -> a = a'.
congruence.
Qed.

Lemma bug_2447_variant1: mkR a b c = mkR a b' c -> b = b'.
congruence.
Qed.

Lemma bug_2447_variant2: mkR a b c = mkR a b c' -> c = c'.
congruence.
Qed.


End bug_2447.

(* congruence was supposed to do discriminate but it was bugged for
   types with indices *)

Inductive I : nat -> Type := C : I 0 | D : I 0.
Goal ~C=D.
congruence.
Qed.

(* Example by Jonathan Leivant, congruence up to universes *)
Section JLeivant.
  Variables S1 S2 : Set.

  Definition T1 : Type := S1.
  Definition T2 : Type := S2.

  Goal T1 = T1.
    congruence.
    Undo.
    unfold T1.
    congruence.
  Qed.
End JLeivant.

(* An example with primitive projections *)

Module PrimitiveProjections.
Set Primitive Projections.
Record t (A:Type) := { f : A }.
Goal forall g (a:t nat), @f nat = g -> f a = 0 -> g a = 0.
congruence.
Undo.
intros.
unfold f in H0. (* internally turn the projection to unfolded form *)
congruence.
Qed.
End PrimitiveProjections.
