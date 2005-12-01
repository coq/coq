(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Some utility functions to be reused in module [Haskell]. *)

open Pp
open Names
open Libnames
open Miniml

val pp_par : bool -> std_ppcmds -> std_ppcmds
val pp_abst : identifier list -> std_ppcmds
val pp_apply : std_ppcmds -> bool -> std_ppcmds list -> std_ppcmds 
val pr_binding : identifier list -> std_ppcmds

val rename_id : identifier -> Idset.t -> identifier

val lowercase_id : identifier -> identifier
val uppercase_id : identifier -> identifier

val pr_upper_id : identifier -> std_ppcmds

type env = identifier list * Idset.t

val rename_vars: Idset.t -> identifier list -> env
val rename_tvars: Idset.t -> identifier list -> identifier list 
val push_vars : identifier list -> env -> identifier list * env
val get_db_name : int -> env -> identifier

val keywords : Idset.t

val preamble : 
  extraction_params -> module_path list -> bool*bool*bool -> bool -> std_ppcmds

val preamble_sig : 
  extraction_params -> module_path list -> bool*bool*bool -> std_ppcmds

(*s Production of Ocaml syntax. We export both a functor to be used for 
    extraction in the Coq toplevel and a function to extract some 
    declarations to a file. *)

module Make : functor(P : Mlpp_param) -> Mlpp





