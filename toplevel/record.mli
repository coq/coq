(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Vernacexpr
open Topconstr
open Impargs
(*i*)

(* [declare_projections ref name coers params fields] declare projections of
   record [ref] (if allowed) using the given [name] as argument, and put them
   as coercions accordingly to [coers]; it returns the absolute names of projections *)

val declare_projections :
  inductive -> ?kind:Decl_kinds.definition_object_kind -> ?name:identifier ->
  bool list -> manual_explicitation list list -> rel_context -> 
  bool list * constant option list

val declare_structure : identifier -> identifier -> 
  manual_explicitation list -> rel_context -> (* params *)
  Term.constr -> (* arity *)
  Impargs.manual_explicitation list list -> Sign.rel_context -> (* fields *)
  ?kind:Decl_kinds.definition_object_kind -> ?name:identifier ->
  bool -> (* coercion? *)
  bool list -> (* field coercions *)
  mutual_inductive

val definition_structure :
  lident with_coercion * local_binder list *
  (local_decl_expr with_coercion) list * identifier * sorts -> kernel_name
