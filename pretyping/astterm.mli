(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                               July 1st 1999                              *)
(*                                                                          *)
(****************************************************************************)
(*                               astterm.mli                                *)
(****************************************************************************)

open Names
open Term
open Evd

val dbize_op : CoqAst.loc -> string -> CoqAst.t list -> constr list -> constr
val dbize    : unit assumptions -> CoqAst.t -> constr

val absolutize_cci : 'c evar_map -> unit assumptions -> constr -> constr
val dbize_cci      : 'c evar_map -> unit assumptions -> CoqAst.t -> constr
val absolutize_fw  : 'c evar_map -> unit assumptions -> constr -> constr
val dbize_fw       : 'c evar_map -> unit assumptions -> CoqAst.t -> constr

val raw_constr_of_com :
  'c evar_map -> 'a assumptions -> CoqAst.t -> constr
val raw_fconstr_of_com :
  'c evar_map -> 'a assumptions -> CoqAst.t -> constr
val raw_constr_of_compattern :
  'c evar_map -> 'a assumptions -> CoqAst.t -> constr

val globalize_command : CoqAst.t -> CoqAst.t
val globalize_ast     : CoqAst.t -> CoqAst.t

(* $Id$ *)
