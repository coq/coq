(* Interaction between coercions and casts *)
(*   Example provided by Eduardo Gimenez   *)

Parameter Z S : Set.

Parameter f : S -> Z.
Coercion f : S >-> Z.

Parameter g : Z -> Z.

Check (fun s => g (s:S)).


(* Check uniform inheritance condition *)

Parameter h : nat -> nat -> Prop.
Parameter i : forall n m : nat, h n m -> nat.
Coercion i : h >-> nat.

(* Check coercion to funclass when the source occurs in the target *)

Parameter C : nat -> nat -> nat.
Coercion C : nat >-> Funclass.

(* Remark: in the following example, it cannot be decide whether C is
   from nat to Funclass or from A to nat. An explicit Coercion command is
   expected 

Parameter A : nat -> Prop.
Parameter C:> forall n:nat, A n -> nat.
*)

