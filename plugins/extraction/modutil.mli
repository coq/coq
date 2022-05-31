(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Functions upon ML modules. *)

val struct_ast_search : (Miniml.ml_ast -> bool) -> Miniml.ml_structure -> bool
val struct_type_search : (Miniml.ml_type -> bool) -> Miniml.ml_structure -> bool

type do_ref = Names.GlobRef.t -> unit

val type_iter_references : do_ref -> Miniml.ml_type -> unit
val ast_iter_references : do_ref -> do_ref -> do_ref -> Miniml.ml_ast -> unit
val decl_iter_references : do_ref -> do_ref -> do_ref -> Miniml.ml_decl -> unit
val spec_iter_references : do_ref -> do_ref -> do_ref -> Miniml.ml_spec -> unit

val signature_of_structure : Miniml.ml_structure -> Miniml.ml_signature

val mtyp_of_mexpr : Miniml.ml_module_expr -> Miniml.ml_module_type

val msid_of_mt : Miniml.ml_module_type -> Names.ModPath.t

val get_decl_in_structure : Names.GlobRef.t -> Miniml.ml_structure -> Miniml.ml_decl

(* Some transformations of ML terms. [optimize_struct] simplify
   all beta redexes (when the argument does not occur, it is just
   thrown away; when it occurs exactly once it is substituted; otherwise
   a let-in redex is created for clarity) and iota redexes, plus some other
   optimizations. The first argument is the list of objects we want to appear.
*)

val optimize_struct : Names.GlobRef.t list * Names.ModPath.t list ->
  Miniml.ml_structure -> Miniml.ml_structure
