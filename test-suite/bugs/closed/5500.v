(* Too weak check on the correctness of return clause was leading to an anomaly *)

Inductive Vector A: nat -> Type :=
  nil: Vector A O
| cons: forall n, A -> Vector A n -> Vector A (S n).

(* This could be made working with a better inference of inner return
   predicates from the return predicate at the higher level of the
   nested matching. Currently, we only check that it does not raise an
   anomaly, but eventually, the "Fail" could be removed. *)

Fail Definition hd_fst A x n (v: A * Vector A (S n)) :=
  match v as v0 return match v0 with
                       (l, r) =>
                       match r in Vector _ n return match n with 0 => Type | S _ => Type end with
                         nil _ => A
                       | cons _ _ _ _ => A
                       end
                       end with
    (_, nil _) => x
  | (_, cons _ n hd tl) => hd
  end.

(* This is another example of failure but involving beta-reduction and
   not iota-reduction. Thus, for this one, I don't see how it could be
   solved by small inversion, whatever smart is small inversion. *)

Inductive A : (Type->Type) -> Type := J : A (fun x => x).

Fail Check fun x : nat * A (fun x => x) =>
  match x return match x with
                 (y,z) => match z in A f return f Type with J => bool end
                 end with
  (y,J) => true
  end.
