(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * FSetAVL : Implementation of FSetInterface via AVL trees *)

(** This module implements finite sets using AVL trees.
    It follows the implementation from Ocaml's standard library,

    All operations given here expect and produce well-balanced trees
    (in the ocaml sense: heights of subtrees shouldn't differ by more
    than 2), and hence has low complexities (e.g. add is logarithmic
    in the size of the set). But proving these balancing preservations
    is in fact not necessary for ensuring correct operational behavior
    and hence fulfilling the FSet interface. As a consequence,
    balancing results are not part of this file anymore, they can
    now be found in [FSetFullAVL].

    Four operations ([union], [subset], [compare] and [equal]) have
    been slightly adapted in order to have only structural recursive
    calls. The precise ocaml versions of these operations have also
    been formalized (thanks to Function+measure), see [ocaml_union],
    [ocaml_subset], [ocaml_compare] and [ocaml_equal] in
    [FSetFullAVL]. The structural variants compute faster in Coq,
    whereas the other variants produce nicer and/or (slightly) faster
    code after extraction.
*)

Require Import FSetInterface ZArith Int.

Set Implicit Arguments.
Unset Strict Implicit.

(** This is just a compatibility layer, the real implementation
    is now in [MSetAVL] *)

Require FSetCompat MSetAVL Orders OrdersAlt.

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.
 Module X' := OrdersAlt.Update_OT X.
 Module MSet := MSetAVL.IntMake I X'.
 Include FSetCompat.Backport_Sets X MSet.
End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).

