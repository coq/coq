(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Term
open Declarations

val pr : string -> unit
val pri : int -> unit
val prch : char -> unit
val pnl : unit -> unit
val prl : string -> unit
val pr_list : ('a -> unit) -> string -> 'a list -> unit

val pr_ind : imap -> inductive -> unit
val pr_construct : imap -> constructor -> unit
val pr_fix : fixpoint -> unit
val pr_cofix : cofixpoint -> unit

val prc : imap -> constr -> unit
val prv : imap -> constr array -> unit

val init : unit -> unit

val trace : unit -> unit
val untrace : unit -> unit

val enter : string -> unit
val enter_pr : string -> ('a -> unit) -> 'a -> unit

val leave : 'a -> 'a
val leave_pr : ('a -> unit) -> 'a -> 'a

val branch : string -> unit
val branch_pr : string -> ('a -> unit) -> 'a -> unit
