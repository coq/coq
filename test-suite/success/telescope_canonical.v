Structure Inner := mkI { is :> Type }.
Structure Outer := mkO { os :> Inner }.
Canonical Structure natInner := mkI nat.
Canonical Structure natOuter := mkO natInner.
Definition hidden_nat := nat.
Axiom P : forall S : Outer, is (os S) -> Prop.
Lemma test1 (n : hidden_nat) : P _ n.
Admitted.

Structure Pnat := mkP { getp : nat }.
Definition my_getp := getp.
Axiom W : nat -> Prop.

(* Fix *)
Canonical Structure add1Pnat n := mkP (plus n 1).
Definition test_fix n := (refl_equal _ : W (my_getp _)  = W (n + 1)).

(* Case *)
Definition pred n := match n with 0 => 0 | S m => m end.
Canonical Structure predSS n := mkP (pred n).
Definition test_case x := (refl_equal _ : W (my_getp _)  = W (pred x)).
Fail Definition test_case' := (refl_equal _ : W (my_getp _)  = W (pred 0)).

Canonical Structure letPnat' := mkP 0.
Definition letin := (let n := 0 in n).
Definition test4 := (refl_equal _ : W (getp _)  = W letin).
Definition test41 := (refl_equal _ : W (my_getp _)  = W letin).
Definition letin2 (x : nat) := (let n := x in n).
Canonical Structure letPnat'' x := mkP (letin2 x).
Definition test42 x := (refl_equal _ : W (my_getp _)  = W (letin2 x)).
Fail Definition test42' x := (refl_equal _ : W (my_getp _)  = W x).

Structure Morph := mkM { f :> nat -> nat }.
Definition my_f := f.
Axiom Q : (nat -> nat) -> Prop.

(* Lambda *)
Canonical Structure addMorh x := mkM (plus x).
Definition test_lam x := (refl_equal _ : Q (my_f _) = Q (plus x)).
Definition test_lam' := (refl_equal _ : Q (my_f _) = Q (plus 0)).

(* Simple tests to justify Sort and Prod as "named". 
   They are already normal, so they cannot loose their names, 
   but still... *)
Structure Sot := mkS { T : Type }.
Axiom R : Type -> Prop.
Canonical Structure tsot := mkS (Type).
Definition test_sort := (refl_equal _ : R (T _) = R Type).
Canonical Structure tsot2 := mkS (nat -> nat).
Definition test_prod := (refl_equal _ : R (T _) = R (nat -> nat)).

(* Var *)
Section Foo.
Variable v : nat.
Definition my_v := v.
Canonical Structure vP := mkP my_v.
Definition test_var := (refl_equal _ : W (getp _)  = W my_v).
Canonical Structure vP' := mkP v.
Definition test_var' := (refl_equal _ : W (my_getp _)  = W my_v).
End Foo.

(* Rel *)
Definition test_rel v := (refl_equal _ : W (my_getp _)  = W (my_v v)).
Goal True.
pose (x := test_rel 2).
match goal with x := _ : W (my_getp (vP 2)) = _ |- _ => idtac end.
apply I.
Qed.




