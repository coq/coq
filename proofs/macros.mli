
(* $Id$ *)

(*i*)
open Names
open Tacmach
open Proof_trees
(*i*)

(* This file contains the table of macro tactics. The body of the
   defined tactics is stored as an ast with variables, which are
   substituted by the real arguments at calling time.
   User defined tactics are stored in a separate table so that they
   are sensible to the Reset and Require commands. *)

type macro_data = {
  mac_args : string list;
  mac_body : Ast.act }

val add_macro_hint : string -> string list * Ast.act -> unit
val lookup         : string -> macro_data 
val macro_expand   : Coqast.loc -> string -> tactic_arg list -> Coqast.t
