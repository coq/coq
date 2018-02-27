(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction of [positive], [N] and [Z] into Ocaml's [big_int] *)

Require Coq.extraction.Extraction.

Require Import ZArith NArith.
Require Import ExtrOcamlBasic.

(** NB: The extracted code should be linked with [nums.cm(x)a]
    from ocaml's stdlib and with the wrapper [big.ml] that
    simplifies the use of [Big_int] (it can be found in the sources
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

Extract Constant Pos.add => "Big.add".
Extract Constant Pos.succ => "Big.succ".
Extract Constant Pos.pred => "fun n -> Big.max Big.one (Big.pred n)".
Extract Constant Pos.sub => "fun n m -> Big.max Big.one (Big.sub n m)".
Extract Constant Pos.mul => "Big.mult".
Extract Constant Pos.min => "Big.min".
Extract Constant Pos.max => "Big.max".
Extract Constant Pos.compare =>
 "fun x y -> Big.compare_case Eq Lt Gt x y".
Extract Constant Pos.compare_cont =>
 "fun c x y -> Big.compare_case c Lt Gt x y".

Extract Constant N.add => "Big.add".
Extract Constant N.succ => "Big.succ".
Extract Constant N.pred => "fun n -> Big.max Big.zero (Big.pred n)".
Extract Constant N.sub => "fun n m -> Big.max Big.zero (Big.sub n m)".
Extract Constant N.mul => "Big.mult".
Extract Constant N.min => "Big.min".
Extract Constant N.max => "Big.max".
Extract Constant N.div =>
 "fun a b -> if Big.eq b Big.zero then Big.zero else Big.div a b".
Extract Constant N.modulo =>
 "fun a b -> if Big.eq b Big.zero then Big.zero else Big.modulo a b".
Extract Constant N.compare => "Big.compare_case Eq Lt Gt".

Extract Constant Z.add => "Big.add".
Extract Constant Z.succ => "Big.succ".
Extract Constant Z.pred => "Big.pred".
Extract Constant Z.sub => "Big.sub".
Extract Constant Z.mul => "Big.mult".
Extract Constant Z.opp => "Big.opp".
Extract Constant Z.abs => "Big.abs".
Extract Constant Z.min => "Big.min".
Extract Constant Z.max => "Big.max".
Extract Constant Z.compare => "Big.compare_case Eq Lt Gt".

Extract Constant Z.of_N => "fun p -> p".
Extract Constant Z.abs_N => "Big.abs".

(** Z.div and Z.modulo are quite complex to define in terms of (/) and (mod).
    For the moment we don't even try *)

(** Test:
Require Import ZArith NArith.

Extraction "/tmp/test.ml"
 Pos.add Pos.pred Pos.sub Pos.mul Pos.compare N.pred N.sub N.div N.modulo N.compare
 Z.add Z.mul Z.compare Z.of_N Z.abs_N Z.div Z.modulo.
*)
