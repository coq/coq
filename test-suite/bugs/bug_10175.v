From Stdlib Require Import ssreflect ssrbool ssrfun.
From Stdlib Require Import List.

Import Nat.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  := (filter test l, filter (fun x => negb (test x)) l).

Definition fold (A B: Type) f l b:= @fold_right B A f b l.

Theorem partition_fst: forall (X : Type)  (test : X -> bool) (l : list X),
                         fold_right andb true (map test (fst (partition test l))) = true.
Proof.
  move => ? test.
  elim => [|x xs IHxs] //.
  case H: eqb (test x) true.  (* <-- anomaly here! *)
Abort.
