(* Check discharge of arguments scopes + other checks *)

(* This is bug #4865 *)

Notation "<T>" := true : bool_scope.
Section A.
  Check negb <T>.
  Global Arguments negb : clear scopes.
  Fail Check negb <T>.
End A.

(* Check that no scope is re-computed *)
Fail Check negb <T>.

(* Another test about arguments scopes in sections *)

Notation "0" := true.
Section B.
  Variable x : nat.
  Let T := nat -> nat.
  Definition f y : T := fun z => x + y + z.
  Fail Check f 1 0.   (* 0 in nat, 0 in bool *)
  Fail Check f 0 0.   (* 0 in nat, 0 in bool *)
  Check f 0 1.        (* 0 and 1 in nat *)
  Global Arguments f _%nat_scope _%nat_scope.
  Check f 0 0.        (* both 0 in nat *)
End B.

(* Check that only the scope for the extra product on x is re-computed *)
Check f 0 0 0.   (* All 0 in nat *)

Section C.
  Variable x : nat.
  Let T := nat -> nat.
  Definition g y : T := fun z => x + y + z.
  Global Arguments g : clear scopes.
  Check g 1.          (* 1 in nat *)
End C.

(* Check that only the scope for the extra product on x is re-computed *)
Check g 0.            (* 0 in nat *)
Fail Check g 0 1 0. (* 2nd 0 in bool *)
Fail Check g 0 0 1. (* 2nd 0 in bool *)

(* Another test on arguments scopes: checking scope for expanding arities *)
(* Not sure this is very useful, but why not *)
                  
Fixpoint arr n := match n with 0%nat => nat | S n => nat -> arr n end.
Fixpoint lam n : arr n := match n with 0%nat => 0%nat | S n => fun x => lam n  end.
Notation "0" := true.
Arguments lam _%nat_scope _%nat_scope : extra scopes.
Check (lam 1 0).
