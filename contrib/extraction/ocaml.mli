(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Some utility functions to be reused in module [Haskell]. *)

open Pp
open Miniml
open Names
open Term
open Nametab
open Table

val current_module : identifier option ref
val cons_cofix : Refset.t ref

val collapse_type_app : ml_type list -> ml_type list

val open_par : bool -> std_ppcmds
val close_par : bool -> std_ppcmds
val pp_abst : identifier list -> std_ppcmds
val pr_binding : identifier list -> std_ppcmds

val rename_id : identifier -> Idset.t -> identifier

val lowercase_id : identifier -> identifier
val uppercase_id : identifier -> identifier

type env = identifier list * Idset.t

val rename_vars: Idset.t -> identifier list -> env
val rename_tvars: 
  Idset.t -> identifier list -> identifier list * identifier Idmap.t
val push_vars : identifier list -> env -> identifier list * env
val get_db_name : int -> env -> identifier

val keywords : Idset.t

val preamble : extraction_params -> std_ppcmds

(*s Production of Ocaml syntax. We export both a functor to be used for 
    extraction in the Coq toplevel and a function to extract some 
    declarations to a file. *)

module Make : functor(P : Mlpp_param) -> Mlpp





