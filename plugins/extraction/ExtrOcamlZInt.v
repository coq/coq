(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction of [positive], [N] and [Z] into Ocaml's [int] *)

Require Coq.extraction.Extraction.

Require Import ZArith NArith.
Require Import ExtrOcamlBasic.

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [Z] into [int] is definitively *not* a good idea.
    See the Disclaimer in [ExtrOcamlNatInt]. *)

(** Mapping of [positive], [Z], [N] into [int]. The last strings
    emulate the matching, see documentation of [Extract Inductive]. *)

Extract Inductive positive => int
[ "(fun p->1+2*p)" "(fun p->2*p)" "1" ]
"(fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))".

Extract Inductive Z => int [ "0" "" "(~-)" ]
"(fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))".

Extract Inductive N => int [ "0" "" ]
"(fun f0 fp n -> if n=0 then f0 () else fp n)".

(** Nota: the "" above is used as an identity function "(fun p->p)" *)

(** Efficient (but uncertified) versions for usual functions *)

Extract Constant Pos.add => "(+)".
Extract Constant Pos.succ => "Pervasives.succ".
Extract Constant Pos.pred => "fun n -> Pervasives.max 1 (n-1)".
Extract Constant Pos.sub => "fun n m -> Pervasives.max 1 (n-m)".
Extract Constant Pos.mul => "( * )".
Extract Constant Pos.min => "Pervasives.min".
Extract Constant Pos.max => "Pervasives.max".
Extract Constant Pos.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".
Extract Constant Pos.compare_cont =>
 "fun c x y -> if x=y then c else if x<y then Lt else Gt".


Extract Constant N.add => "(+)".
Extract Constant N.succ => "Pervasives.succ".
Extract Constant N.pred => "fun n -> Pervasives.max 0 (n-1)".
Extract Constant N.sub => "fun n m -> Pervasives.max 0 (n-m)".
Extract Constant N.mul => "( * )".
Extract Constant N.min => "Pervasives.min".
Extract Constant N.max => "Pervasives.max".
Extract Constant N.div => "fun a b -> if b=0 then 0 else a/b".
Extract Constant N.modulo => "fun a b -> if b=0 then a else a mod b".
Extract Constant N.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".


Extract Constant Z.add => "(+)".
Extract Constant Z.succ => "Pervasives.succ".
Extract Constant Z.pred => "Pervasives.pred".
Extract Constant Z.sub => "(-)".
Extract Constant Z.mul => "( * )".
Extract Constant Z.opp => "(~-)".
Extract Constant Z.abs => "Pervasives.abs".
Extract Constant Z.min => "Pervasives.min".
Extract Constant Z.max => "Pervasives.max".
Extract Constant Z.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".

Extract Constant Z.of_N => "fun p -> p".
Extract Constant Z.abs_N => "Pervasives.abs".

(** Z.div and Z.modulo are quite complex to define in terms of (/) and (mod).
    For the moment we don't even try *)


