(* Test the nonuniform attribute to silence warnings on coercions
   not satisfying the non uniform inheritance condition. *)

Module Test0.

Parameter C : nat -> bool -> Type.
Parameter D : Type.
Parameter f : forall (n : nat) (b : bool), C n b -> D.

(* uniform inheritance satisfied, no warning *)
Coercion f : C >-> D.

End Test0.

Module Test1.

Parameter C : nat -> bool -> Type.
Parameter D : Type.
Parameter f : forall (b : bool) (n : nat), C n b -> D.

(* uniform inheritance not satisfied, warning *)
Coercion f : C >-> D.

End Test1.

Module Test2.

Parameter C : nat -> bool -> Type.
Parameter D : Type.
Parameter f : forall (b : bool) (n : nat), C n b -> D.

(* uniform inheritance not satisfied but attribute, no warning *)
#[warning="-uniform-inheritance"] Coercion f : C >-> D.

End Test2.

Module Test3.

Parameter C : nat -> bool -> Type.
Parameter D : Type.
Parameter f : forall (n : nat) (b : bool), C n b -> D.

(* uniform inheritance satisfied, no warning *)
Coercion f' := f.

End Test3.

Module Test4.

Parameter C : nat -> bool -> Type.
Parameter D : Type.
Parameter f : forall (b : bool) (n : nat), C n b -> D.

(* uniform inheritance not satisfied, warning *)
Coercion f' := f.

End Test4.

Module Test5.

Parameter C : nat -> bool -> Type.
Parameter D : Type.
Parameter f : forall (b : bool) (n : nat), C n b -> D.

(* uniform inheritance not satisfied but attribute, no warning *)
#[warning="-uniform-inheritance"] Coercion f' := f.

End Test5.
