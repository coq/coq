(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Euclidean division *)

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Require Le.
Require Euclid_def.
Require Compare_dec.

Implicit Variables Type n,a,b,q,r:nat.

Fixpoint inf_dec [n:nat] : nat->bool :=
      [m:nat] Cases n m of
                  O     _     => true
              | (S n')  O     => false
              | (S n') (S m') => (inf_dec n' m')
             end.

Theorem div1 : (b:nat)(gt b O)->(a:nat)(diveucl a b).
Realizer Fix div1 {div1/2: nat->nat->diveucl :=
  [b,a]Cases a of
         O     => (O,O)
       | (S n) =>
           let (q,r) = (div1 b n) in
             if (le_gt_dec b (S r)) then ((S q),O)
	     else (q,(S r))
       end}.
Program_all.
Rewrite e.
Replace b with (S r).
Simpl.
Elim plus_n_O; Auto with arith.
Apply le_antisym; Auto with arith.
Elim plus_n_Sm; Auto with arith.
Qed.

Theorem div2 : (b:nat)(gt b O)->(a:nat)(diveucl a b).
Realizer Fix div1 {div1/2: nat->nat->diveucl :=
  [b,a]Cases a of
         O     => (O,O)
       | (S n) =>
           let (q,r) = (div1 b n) in
             if (inf_dec b (S r)) :: :: { {(le b (S r))}+{(gt b (S r))} }
             then ((S q),O)
	     else (q,(S r))
       end}.
Program_all.
Rewrite e.
Replace b with (S r).
Simpl.
Elim plus_n_O; Auto with arith.
Apply le_antisym; Auto with arith.
Elim plus_n_Sm; Auto with arith.
Qed.
