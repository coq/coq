(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pretty-printers for tactic_expr syntactic
    objects and their subcomponents. *)

open Pp
open Genarg
open Names
open Constrexpr
open Tacexpr
open Ppextend
open Environ
open Pattern
open Misctypes

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a glob_extra_genarg_printer =
    (glob_constr_and_expr -> std_ppcmds) ->
    (glob_constr_and_expr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a extra_genarg_printer =
    (Term.constr -> std_ppcmds) ->
    (Term.constr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

val declare_extra_genarg_pprule :
  ('a, 'b, 'c) genarg_type ->
  'a raw_extra_genarg_printer ->
  'b glob_extra_genarg_printer ->
  'c extra_genarg_printer -> unit

type grammar_terminals = string option list

type pp_tactic = {
  pptac_args : argument_type list;
  pptac_prods : int * grammar_terminals;
}

val declare_ml_tactic_pprule : ml_tactic_name -> pp_tactic -> unit
val declare_notation_tactic_pprule : KerName.t -> pp_tactic -> unit

(** The default pretty-printers produce {!Pp.std_ppcmds} that are
    interpreted as raw strings. *)
include Pptacticsig.Pp

(** The rich pretty-printers produce {!Pp.std_ppcmds} that are
    interpreted as annotated strings. The annotations can be
    retrieved using {!RichPp.rich_pp}. Their definitions are
    located in {!Ppannotation.t}. *)
module Richpp : Pptacticsig.Pp

