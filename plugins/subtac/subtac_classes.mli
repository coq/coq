(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Topconstr
open Util
open Typeclasses
open Implicit_quantifiers
open Classes
(*i*)

val type_ctx_instance :     Evd.evar_map ref ->
  Environ.env ->
    ('a * Term.constr option * Term.constr) list ->
    Topconstr.constr_expr list ->
    Term.constr list ->
    Term.constr list

val new_instance :
  ?global:bool ->
  local_binder list ->
  typeclass_constraint ->
  constr_expr ->
  ?generalize:bool ->
  int option ->
  identifier * Subtac_obligations.progress
