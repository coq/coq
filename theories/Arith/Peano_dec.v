(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Decidable.

Theorem O_or_S : (n:nat)({m:nat|(S m)=n})+{O=n}.
Proof.
Induction n.
Auto.
Intros p H; Left; Exists p; Auto.
Qed.

Theorem eq_nat_dec : (n,m:nat){n=m}+{~(n=m)}.
Proof.
Induction n; Induction m; Auto.
Intros q H'; Elim (H q); Auto.
Qed.

Hints Resolve O_or_S eq_nat_dec : arith.

Theorem dec_eq_nat:(x,y:nat)(decidable (x=y)).
Intros x y; Unfold decidable; Elim (eq_nat_dec x y); Auto with arith.
Save.

