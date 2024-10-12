Require Eqdep_dec.

(* Check the behaviour of Injection *)

(* Check that Injection tries Intro until *)

Unset Structural Injection.
Lemma l1 : forall x : nat, S x = S (S x) -> False.
 injection 1.
apply n_Sn.
Qed.

Lemma l2 : forall (x : nat) (H : S x = S (S x)), H = H -> False.
 injection H.
intros.
apply (n_Sn x H0).
Qed.

(* Check that no tuple needs to be built *)
Lemma l3 :
 forall x y : nat,
 existT (fun n : nat => {n = n} + {n = n}) x (left _ (refl_equal x)) =
 existT (fun n : nat => {n = n} + {n = n}) y (left _ (refl_equal y)) ->
 x = y.
intros x y H.
 injection H.
exact (fun H => H).
Qed.

(* Check that a tuple is built (actually the same as the initial one) *)
Lemma l4 :
 forall p1 p2 : {0 = 0} + {0 = 0},
 existT (fun n : nat => {n = n} + {n = n}) 0 p1 =
 existT (fun n : nat => {n = n} + {n = n}) 0 p2 ->
 existT (fun n : nat => {n = n} + {n = n}) 0 p1 =
 existT (fun n : nat => {n = n} + {n = n}) 0 p2.
intros.
 injection H.
exact (fun H => H).
Qed.
Set Structural Injection.

(* Test injection as *)

Lemma l5 : forall x y z t : nat, (x,y) = (z,t) -> x=z.
intros; injection H as Hxz Hyt.
exact Hxz.
Qed.

(* Check the variants of injection *)

Goal forall x y, S x = S y -> True.
injection 1 as H'.
Undo.
intros.
injection H as H'.
Undo.
Ltac f x := injection x.
f H.
Abort.

Goal (forall x y : nat, x = y -> S x = S y) -> True.
intros.
try injection (H O) || exact I.
Qed.

Goal (forall x y : nat, x = y -> S x = S y) -> True.
intros.
einjection (H O).
2:instantiate (1:=O).
Abort.

Goal (forall x y : nat, x = y -> S x = S y) -> True.
intros.
einjection (H O ?[y]) as H0.
instantiate (y:=O).
Abort.

(* Test the injection intropattern *)

Goal forall (a b:nat) l l', cons a l = cons b l' -> a=b.
intros * [= H1 H2].
exact H1.
Qed.

(* Test injection using K, knowing that an equality is decidable *)
(* Basic case, using sigT *)

Scheme Equality for nat.
Unset Structural Injection.
Goal forall n:nat, forall P:nat -> Type, forall H1 H2:P n,
  existT P n H1 = existT P n H2 -> H1 = H2.
intros.
injection H.
intro H0. exact H0.
Abort.
Set Structural Injection.

Goal forall n:nat, forall P:nat -> Type, forall H1 H2:P n,
  existT P n H1 = existT P n H2 -> H1 = H2.
intros.
injection H as H0.
exact H0.
Abort.

(* Test injection using K, knowing that an equality is decidable *)
(* Basic case, using sigT, with "as" clause *)

Goal forall n:nat, forall P:nat -> Type, forall H1 H2:P n,
  existT P n H1 = existT P n H2 -> H1 = H2.
intros.
injection H as H.
exact H.
Abort.

(* Test injection using K, knowing that an equality is decidable *)
(* Dependent case not directly exposing sigT *)

Inductive my_sig (A : Type) (P : A -> Type) : Type :=
    my_exist : forall x : A, P x -> my_sig A P.

Goal forall n:nat, forall P:nat -> Type, forall H1 H2:P n,
  my_exist _ _ n H1 = my_exist _ _ n H2 -> H1 = H2.
intros.
injection H as H.
exact H.
Abort.

(* Test injection using K, knowing that an equality is decidable *)
(* Dependent case not directly exposing sigT deeply nested *)

Goal forall n:nat, forall P:nat -> Type, forall H1 H2:P n,
  (my_exist _ _ n H1,0) = (my_exist _ _ n H2,0) -> H1 = H2.
intros * [= H].
exact H.
Abort.

(* Test the Keep Proof Equalities option. *)
Set Keep Proof Equalities.
Unset Structural Injection.

Inductive pbool : Prop := Pbool1 | Pbool2.

Inductive pbool_shell : Set := Pbsc : pbool -> pbool_shell.

Goal Pbsc Pbool1 = Pbsc Pbool2 -> True.
injection 1.
match goal with
 |- Pbool1 = Pbool2 -> True => idtac | |- True => fail
end.
Abort.

(* Injection in the presence of local definitions *)
Inductive A := B (T := unit) (x y : bool) (z := x).
Goal forall x y x' y', B x y = B x' y' -> y = y'.
intros * [= H1 H2].
exact H2.
Qed.

(* Injection does not project at positions in Prop... allow it?

Inductive t (A:Prop) : Set := c : A -> t A.
Goal forall p q : True\/True, c _ p = c _ q -> False.
intros.
injection H.
Abort.

*)

(* Injection does not project on discriminable positions... allow it?

Goal 1=2 -> 1=0.
intro H.
injection H.
intro; assumption.
Qed.

*)
