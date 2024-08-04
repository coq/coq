(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type type_descr

val remember : type_descr -> type_descr
(** Remember values at this position.
    The argument should be not be a [remember]. *)

val ignore : type_descr

val array : type_descr -> type_descr

val sum : type_descr array array -> type_descr
(** The array is for the non constant constructors.
    Constant constructors are ignored. *)

val tuple : type_descr array -> type_descr

val pair : type_descr -> type_descr -> type_descr

val list : type_descr -> type_descr

val slist : type_descr -> type_descr

val cofix : (type_descr -> type_descr) -> type_descr
(** Must be productive. [remember] counts as the identity for productivity analysis. *)

type analysis

val raw_length : analysis -> int
(** for debug printing *)

val analysis_equal : analysis -> analysis -> bool

val analyse : type_descr -> Obj.t -> analysis

(** [Unshared] means refcount = 1, [Fresh] means refcount > 1 *)
type sharing_info =
  | Unshared of int
  | Fresh of int
  | Seen of int

val step : analysis -> analysis * sharing_info

val is_done : analysis -> bool

val max_index : analysis -> int
(** The max [Fresh] in the analysis. [-1] if [is_done]. *)

val to_list : analysis -> sharing_info list

val raw : analysis -> string
