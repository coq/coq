(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction of [positive], [N] and [Z] into Ocaml's [int] *)

Require Import ZArith NArith ZOdiv_def.
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

Extract Constant Pplus => "(+)".
Extract Constant Psucc => "succ".
Extract Constant Ppred => "fun n -> max 1 (n-1)".
Extract Constant Pminus => "fun n m -> max 1 (n-m)".
Extract Constant Pmult => "( * )".
Extract Constant Pmin => "min".
Extract Constant Pmax => "max".
Extract Constant Pcompare =>
 "fun x y c -> if x=y then c else if x<y then Lt else Gt".


Extract Constant Nplus => "(+)".
Extract Constant Nsucc => "succ".
Extract Constant Npred => "fun n -> max 0 (n-1)".
Extract Constant Nminus => "fun n m -> max 0 (n-m)".
Extract Constant Nmult => "( * )".
Extract Constant Nmin => "min".
Extract Constant Nmax => "max".
Extract Constant Ndiv => "fun a b -> if b=0 then 0 else a/b".
Extract Constant Nmod => "fun a b -> if b=0 then a else a mod b".
Extract Constant Ncompare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".


Extract Constant Zplus => "(+)".
Extract Constant Zsucc => "succ".
Extract Constant Zpred => "pred".
Extract Constant Zminus => "(-)".
Extract Constant Zmult => "( * )".
Extract Constant Zopp => "(~-)".
Extract Constant Zabs => "abs".
Extract Constant Zmin => "min".
Extract Constant Zmax => "max".
Extract Constant Zcompare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".

Extract Constant Z_of_N => "fun p -> p".
Extract Constant Zabs_N => "abs".

(** Zdiv and Zmod are quite complex to define in terms of (/) and (mod).
    For the moment we don't even try *)


