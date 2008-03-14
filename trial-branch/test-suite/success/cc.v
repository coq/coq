
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
            
            
            