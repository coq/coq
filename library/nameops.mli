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
open Environ

(* Identifiers and names *)
val pr_id : identifier -> Pp.std_ppcmds
val wildcard : identifier

val make_ident : string -> int option -> identifier
val repr_ident : identifier -> string * int option

val atompart_of_id : identifier -> string

val add_suffix : identifier -> string -> identifier
val add_prefix : string -> identifier -> identifier

val lift_ident           : identifier -> identifier
val next_ident_away      : identifier -> identifier list -> identifier
val next_ident_away_from : identifier -> identifier list -> identifier

val next_name_away : name -> identifier list -> identifier
val next_name_away_with_default :
  string -> name -> identifier list -> identifier

val out_name : name -> identifier


val pr_lab : label -> Pp.std_ppcmds

(* some preset paths *)

val default_module : dir_path

(* This is the root of the standard library of Coq *)
val coq_root : module_ident

(* This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : dir_path
