(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vernacexpr
open Constrexpr

module Ast : sig
  type t =
    { name : Names.lident
    ; is_coercion : coercion_flag
    ; binders: local_binder_expr list
    ; cfs : (local_decl_expr * record_field_attr) list
    ; idbuild : Id.t
    ; sort : constr_expr option
    }
end

val definition_structure
  :  universe_decl_expr option
  -> inductive_kind
  -> template:bool option
  -> cumulative:bool
  -> poly:bool
  -> Declarations.recursivity_kind
  -> Ast.t list
  -> GlobRef.t list

val declare_existing_class : GlobRef.t -> unit

(* Implementation internals, consult Coq developers before using;
   current user Elpi, see https://github.com/LPCIC/coq-elpi/pull/151 *)
module Internal : sig
  type projection_flags = {
    pf_subclass: bool;
    pf_canonical: bool;
  }

  val declare_projections
    : Names.inductive
    -> Entries.universes_entry
    -> ?kind:Decls.definition_object_kind
    -> Names.Id.t
    -> projection_flags list
    -> Impargs.manual_implicits list
    -> Constr.rel_context
    -> Recordops.proj_kind list * Names.Constant.t option list

  val declare_structure_entry : Recordops.struc_typ -> unit

end
