(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Util
open Formula
open Tacmach
open Names

val right_reversible : right_pattern -> bool
	
val left_reversible : left_pattern -> bool

module CM: Map.S with type key=constr

module HP: Heap.S with type elt=left_formula

type t = {hyps:HP.t;hatoms: identifier CM.t;gl:right_formula}

val add_left : identifier * constr -> t -> counter -> t

val re_add_left_list : left_formula list -> t -> t

val change_right : constr -> t -> counter -> t

val find_left : constr -> t -> identifier

val rev_left : t -> bool

val is_empty_left : t -> bool

val take_left : t -> left_formula * t

val take_right : t -> right_formula

val empty_seq : t

