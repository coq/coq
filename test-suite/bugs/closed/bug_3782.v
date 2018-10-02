Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 2674 lines to 136 lines, then from 115 lines to 61 lines *)
(* coqc version trunk (October 2014) compiled on Oct 28 2014 14:33:38 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-trunk,(no branch) (53bfe9cf58a3c40e6eb7120d25c1633a9cea3126) *)
Class IsEquiv {A B : Type} (f : A -> B) := {}.
Record Equiv A B := { equiv_fun : A -> B ; equiv_isequiv : IsEquiv equiv_fun }.
Arguments equiv_fun {A B} _ _.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Set Printing Coercions.
Set Printing Implicit.
Module NonPrim.
  Unset Primitive Projections.
  Record TruncType (n : nat) := { trunctype_type :> Type }.
  Canonical Structure default_TruncType := fun n T => (@Build_TruncType n T).
  Goal (forall (s d : TruncType 0) (m : trunctype_type 0 s -> trunctype_type 0 d),
          @IsEquiv (trunctype_type 0 s) (trunctype_type 0 d) m -> Type) ->
  forall (T T0 : Type) (m : T0 -> T), @IsEquiv T0 T m -> True.
    intros isiso_isequiv' mc md e e'.
    (pose (@isiso_isequiv'
             _ _
             (e
              : (Build_TruncType 0 md) ->
                (Build_TruncType 0 mc))
             e') as i || fail "too early"); clear i.
    pose (@isiso_isequiv'
            _ _ _
            e').
    admit.
  Defined.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Record TruncType (n : nat) := { trunctype_type :> Type }.
  Canonical Structure default_TruncType := fun n T => (@Build_TruncType n T).
  Goal (forall (s d : TruncType 0) (m : trunctype_type 0 s -> trunctype_type 0 d),
          @IsEquiv (trunctype_type 0 s) (trunctype_type 0 d) m -> Type) ->
  forall (T T0 : Type) (m : T0 -> T), @IsEquiv T0 T m -> True.
    intros isiso_isequiv' mc md e e'.
    (pose (@isiso_isequiv'
             _ _
             (e
              : (Build_TruncType 0 md) ->
                (Build_TruncType 0 mc))
             e') as i || fail "too early"); clear i.
    Set Printing Existential Instances.
    Set Debug Unification.
    pose (@isiso_isequiv'
            _ _ _
            e'). (* Toplevel input, characters 48-50:
Error:
In environment
isiso_isequiv' : forall (s d : TruncType 0)
                   (m : trunctype_type 0 s -> trunctype_type 0 d),
                 @IsEquiv (trunctype_type 0 s) (trunctype_type 0 d) m -> Type
mc : Type
md : Type
e : md -> mc
e' : @IsEquiv md mc e
The term "e'" has type "@IsEquiv md mc e" while it is expected to have type
 "@IsEquiv (trunctype_type 0 ?t) (trunctype_type 0 ?t0) ?t1".
                  *)
    admit.
  Defined.
End Prim.
