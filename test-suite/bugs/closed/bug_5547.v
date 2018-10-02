(* Checking typability of intermediate return predicates in nested pattern-matching *)

Inductive A : (Type->Type) -> Type := J : A (fun x => x).
Definition ret (x : nat * A (fun x => x))
  := match x return Type with
     | (y,z) => match z in A f return f Type with
                | J => bool
                end
     end.
Definition foo : forall x, ret x.
Proof.
Fail refine (fun x
          => match x return ret x with
             | (y,J) => true
             end
         ).
