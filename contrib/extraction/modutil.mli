(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

(*s Functions upon modules missing in [Modops]. *) 

(* Add _all_ direct subobjects of a module, not only those exported. 
   Build on the [Modops.add_signature] model. *)

val add_structure : module_path -> module_structure_body -> env -> env 

(* Apply a module path substitution on a module.
   Build on the [Modops.subst_modtype] model. *)

val subst_module : substitution -> module_body -> module_body 
val subst_meb : substitution -> module_expr_body -> module_expr_body
val subst_msb : substitution -> module_structure_body -> module_structure_body

(* Change a msid in a module type, to follow a module expr. *)

val replicate_msid : module_expr_body -> module_type_body -> module_type_body

(*s More utilities concerning [module_path]. *)

val mp_length : module_path -> int
val prefixes_mp : module_path -> MPset.t
val modfile_of_mp : module_path -> module_path
val common_prefix_from_list : module_path -> module_path list -> module_path
val add_labels_mp : module_path -> label list -> module_path

(*s Functions upon ML modules. *)

val struct_ast_search : ml_ast -> ml_structure -> bool
val struct_type_search : ml_type -> ml_structure -> bool

type do_ref = global_reference -> unit 

val decl_iter_references : do_ref -> do_ref -> do_ref -> ml_decl -> unit
val spec_iter_references : do_ref -> do_ref -> do_ref -> ml_spec -> unit
val struct_iter_references : do_ref -> do_ref -> do_ref -> ml_structure -> unit

type 'a updown = { mutable up : 'a ; mutable down : 'a }

val struct_get_references_set : ml_structure -> Refset.t updown
val struct_get_references_list : ml_structure -> global_reference list updown

val signature_of_structure : ml_structure -> ml_signature

val get_decl_in_structure : global_reference -> ml_structure -> ml_decl

(* Some transformations of ML terms. [optimize_struct] simplify
   all beta redexes (when the argument does not occur, it is just
   thrown away; when it occurs exactly once it is substituted; otherwise
   a let-in redex is created for clarity) and iota redexes, plus some other
   optimizations. *)

val optimize_struct : 
  extraction_params -> ml_decl list option -> ml_structure -> ml_structure
