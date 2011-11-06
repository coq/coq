(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Declarations
open Environ
open Libnames
open Miniml
open Mod_subst

(*s Functions upon ML modules. *)

val struct_ast_search : (ml_ast -> bool) -> ml_structure -> bool
val struct_type_search : (ml_type -> bool) -> ml_structure -> bool

type do_ref = global_reference -> unit

val decl_iter_references : do_ref -> do_ref -> do_ref -> ml_decl -> unit
val spec_iter_references : do_ref -> do_ref -> do_ref -> ml_spec -> unit

val signature_of_structure : ml_structure -> ml_signature

val msid_of_mt : ml_module_type -> module_path

val get_decl_in_structure : global_reference -> ml_structure -> ml_decl

(* Some transformations of ML terms. [optimize_struct] simplify
   all beta redexes (when the argument does not occur, it is just
   thrown away; when it occurs exactly once it is substituted; otherwise
   a let-in redex is created for clarity) and iota redexes, plus some other
   optimizations. The first argument is the list of objects we want to appear.
*)

val optimize_struct : global_reference list -> ml_structure -> ml_structure
