(* Check typing in the presence of let-in in inductive arity *)

Inductive I : let a := 1 in a=a -> let b := 2 in Type := C : I (eq_refl).
Lemma a : forall x:I eq_refl, match x in I a b c return b = b with C => eq_refl end = eq_refl.
intro.
match goal with |- ?c => let x := eval cbv in c in change x end.
Abort.

Check forall x:I eq_refl, match x in I x return x = x with C => eq_refl end = eq_refl.

(* This is bug #3210 *)

Inductive I' : let X := Set in X :=
| C' : I'.

Definition foo (x : I') : bool :=
  match x with
  C' => true
  end.

(* Bug found in november 2015: was wrongly failing in 8.5beta2 and 8.5beta3 *)

Inductive I2 (A:Type) : let B:=A in forall C, let D:=(C*B)%type in Type :=
  E2 : I2 A nat.

Check fun x:I2 nat nat => match x in I2 _ X Y Z return X*Y*Z with
  E2 _ => (0,0,(0,0))
  end.

(* This used to succeed in 8.3, 8.4 and 8.5beta1 *)

Inductive IND : forall X:Type, let Y:=X in Type :=
  C : IND True.

Definition F (x:IND True) (A:Type) :=
  (* This failed in 8.5beta2 though it should have been accepted *)
  match x in IND Y Z return Z with
  C => I
  end.

Theorem paradox : False.
  (* This succeeded in 8.3, 8.4 and 8.5beta1 because F had wrong type *)
Fail Proof (F C False).
