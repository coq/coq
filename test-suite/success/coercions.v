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

(* Remark: in the following example, it cannot be decided whether C is
   from nat to Funclass or from A to nat. An explicit Coercion command is
   expected

Parameter A : nat -> Prop.
Parameter C:> forall n:nat, A n -> nat.
*)

(* Check coercion between products based on eta-expansion *)
(* (there was a de Bruijn bug until rev 9254) *)

Section P.

Variable E : Set.
Variables C D : E -> Prop.
Variable G :> forall x, C x -> D x.

Check fun (H : forall y:E, y = y -> C y) => (H : forall y:E, y = y -> D y).

End P.

(* Check that class arguments are computed the same when looking for a
   coercion and when applying it (class_args_of) (failed until rev 9255) *)

Section Q.

Variable bool : Set.
Variables C D : bool -> Prop.
Variable G :> forall x, C x -> D x.
Variable f : nat -> bool.

Definition For_all (P : nat -> Prop) := forall x, P x.

Check fun (H : For_all (fun x => C (f x))) => H : forall x, D (f x).
Check fun (H : For_all (fun x => C (f x))) x => H x : D (f x).
Check fun (H : For_all (fun x => C (f x))) => H : For_all (fun x => D (f x)).

End Q.

(* Combining class lookup and path lookup so that if a lookup fails, another
   descent in the class can be found (see wish #1934) *)

Record Setoid : Type :=
{ car :>  Type }.

Record Morphism (X Y:Setoid) : Type :=
{evalMorphism :> X -> Y}.

Definition extSetoid (X Y:Setoid) : Setoid.
constructor.
exact (Morphism X Y).
Defined.

Definition ClaimA := forall (X Y:Setoid) (f: extSetoid X Y) x, f x= f x.

Coercion irrelevent := (fun _ => I) : True -> car (Build_Setoid True).

Definition ClaimB := forall (X Y:Setoid) (f: extSetoid X Y) (x:X), f x= f x.

