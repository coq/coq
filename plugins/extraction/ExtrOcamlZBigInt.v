(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction of [positive], [N] and [Z] into Ocaml's [big_int] *)

Require Import ZArith NArith ZOdiv_def.
Require Import ExtrOcamlBasic.

(** NB: The extracted code should be linked with [nums.cm(x)a]
    from ocaml's stdlib and with the wrapper [big.ml] that
    simlifies the use of [Big_int] (it could be found in the sources
    of Coq). *)

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [Z] into [big_int] isn't necessarily a good idea.
    See the Disclaimer in [ExtrOcamlNatInt]. *)

(** Mapping of [positive], [Z], [N] into [big_int]. The last strings
    emulate the matching, see documentation of [Extract Inductive]. *)

Extract Inductive positive => "Big.big_int"
 [ "Big.doubleplusone" "Big.double" "Big.one" ] "Big.positive_case".

Extract Inductive Z => "Big.big_int"
 [ "Big.zero" "" "Big.opp" ] "Big.z_case".

Extract Inductive N => "Big.big_int"
 [ "Big.zero" "" ] "Big.n_case".

(** Nota: the "" above is used as an identity function "(fun p->p)" *)

(** Efficient (but uncertified) versions for usual functions *)

Extract Constant Pplus => "Big.add".
Extract Constant Psucc => "Big.succ".
Extract Constant Ppred => "fun n -> Big.max Big.one (Big.pred n)".
Extract Constant Pminus => "fun n m -> Big.max Big.one (Big.sub n m)".
Extract Constant Pmult => "Big.mult".
Extract Constant Pmin => "Big.min".
Extract Constant Pmax => "Big.max".
Extract Constant Pcompare =>
 "fun x y c -> Big.compare_case c Lt Gt x y".

Extract Constant Nplus => "Big.add".
Extract Constant Nsucc => "Big.succ".
Extract Constant Npred => "fun n -> Big.max Big.zero (Big.pred n)".
Extract Constant Nminus => "fun n m -> Big.max Big.zero (Big.sub n m)".
Extract Constant Nmult => "Big.mult".
Extract Constant Nmin => "Big.min".
Extract Constant Nmax => "Big.max".
Extract Constant Ndiv =>
 "fun a b -> if Big.eq b Big.zero then Big.zero else Big.div a b".
Extract Constant Nmod =>
 "fun a b -> if Big.eq b Big.zero then Big.zero else Big.modulo a b".
Extract Constant Ncompare => "Big.compare_case Eq Lt Gt".

Extract Constant Zplus => "Big.add".
Extract Constant Zsucc => "Big.succ".
Extract Constant Zpred => "Big.pred".
Extract Constant Zminus => "Big.sub".
Extract Constant Zmult => "Big.mult".
Extract Constant Zopp => "Big.opp".
Extract Constant Zabs => "Big.abs".
Extract Constant Zmin => "Big.min".
Extract Constant Zmax => "Big.max".
Extract Constant Zcompare => "Big.compare_case Eq Lt Gt".

Extract Constant Z_of_N => "fun p -> p".
Extract Constant Zabs_N => "Big.abs".

(** Zdiv and Zmod are quite complex to define in terms of (/) and (mod).
    For the moment we don't even try *)

(** Test:
Require Import ZArith NArith.

Extraction "/tmp/test.ml"
 Pplus Ppred Pminus Pmult Pcompare Npred Nminus Ndiv Nmod Ncompare
 Zplus Zmult BinInt.Zcompare Z_of_N Zabs_N Zdiv.Zdiv Zmod.
*)
