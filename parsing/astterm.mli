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
open Rawterm

(*
val dbize_op : CoqAst.loc -> string -> CoqAst.t list -> constr list -> constr
val dbize    : unit assumptions -> CoqAst.t -> constr

val absolutize_cci : 'c evar_map -> unit assumptions -> constr -> constr
*)
val dbize_cci      : 'c evar_map -> unit assumptions -> CoqAst.t -> rawconstr

(*
val absolutize_fw  : 'c evar_map -> unit assumptions -> constr -> constr
*)
val dbize_fw       : 'c evar_map -> unit assumptions -> CoqAst.t -> rawconstr

val raw_constr_of_com :
  'c evar_map -> 'a assumptions -> CoqAst.t -> rawconstr
val raw_fconstr_of_com :
  'c evar_map -> 'a assumptions -> CoqAst.t -> rawconstr
val raw_constr_of_compattern :
  'c evar_map -> 'a assumptions -> CoqAst.t -> rawconstr

val globalize_command : CoqAst.t -> CoqAst.t
val globalize_ast     : CoqAst.t -> CoqAst.t

(*i Ceci était avant dans Trad
    Maintenant elles sont là car relève des ast i*)

val type_of_com : context -> Coqast.t -> typed_type

val constr_of_com_casted : 'c evar_map -> context -> Coqast.t -> constr ->
  constr

val constr_of_com1 : bool -> 'c evar_map -> context -> Coqast.t -> constr
val constr_of_com : 'c evar_map -> context -> Coqast.t -> constr
val constr_of_com_sort : 'c evar_map -> context -> Coqast.t -> constr

val fconstr_of_com1 : bool -> 'c evar_map -> context -> Coqast.t -> constr
val fconstr_of_com : 'c evar_map -> context -> Coqast.t -> constr
val fconstr_of_com_sort : 'c evar_map -> context -> Coqast.t -> constr

(* Typing with Trad, and re-checking with Mach *)

val fconstruct :'c evar_map -> context -> Coqast.t -> unsafe_judgment
val fconstruct_type :
  'c evar_map -> context -> Coqast.t -> typed_type

(* Typing, re-checking with universes constraints *)
val fconstruct_with_univ :
  'c evar_map -> context -> Coqast.t -> judgement

(* $Id$ *)
