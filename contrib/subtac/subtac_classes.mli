(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.mli 6748 2005-02-18 22:17:50Z herbelin $ i*)

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

val type_ctx_instance :     Evd.evar_defs ref ->
    Environ.env ->
    (Names.identifier * 'a * Term.constr) list ->
    Topconstr.constr_expr list ->
    (Names.identifier * Term.constr) list ->
    (Names.identifier * Term.constr) list *
    (Names.identifier * Term.constr option * Term.constr) list

val new_instance : 
  Topconstr.local_binder list ->
  typeclass_constraint ->
  binder_def_list ->
  unit
