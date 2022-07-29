(* A test on the order of treatment of conversion problems *)
(* Extracted from fiat-crypto *)
(* See #16311 *)

Require Import Coq.ZArith.ZArith Coq.Lists.List.

Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Reserved Notation "~> R" (at level 70).
Reserved Notation "'return' x" (at level 70, format "'return'  x").
Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x.
Admitted.
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).

Declare Scope cps_scope.

Notation "~> R" := (forall T (_:R->T), T) : type_scope.

Definition cpsreturn {T} (x:T) := x.

Notation "'return' x" := (cpsreturn (fun T (continuation:_->T) => continuation x)) : cps_scope.
Local Open Scope Z_scope.
Declare Scope runtime_scope.
Delimit Scope runtime_scope with RT.
Local Open Scope cps_scope.


Parameter runtime_mul : Z -> Z -> Z.
Infix "*" := runtime_mul : runtime_scope.

Definition square_cps (p:list (Z*Z)) : ~> list (Z*Z).
exact (list_rect
      _
      (return nil)
      (fun t ts acc T k
       => (dlet two_t2 := (2 * snd t)%RT in
               acc
                 _
                 (fun acc
                  => k (((fst t * fst t, (snd t * snd t)%RT)
                           :: (map (fun t'
                                    => (fst t * fst t', (two_t2 * snd t')%RT))
                                   ts))
                          ++ acc))))
      p).
Defined.
