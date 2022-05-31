(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Extraction from Coq terms to Miniml. *)

val extract_constant : Environ.env -> Names.Constant.t -> Declarations.constant_body -> Miniml.ml_decl

val extract_constant_spec : Environ.env -> Names.Constant.t -> 'a Declarations.pconstant_body -> Miniml.ml_spec

(** For extracting "module ... with ..." declaration *)

val extract_with_type :
Environ.env -> Evd.evar_map -> EConstr.t -> ( Names.Id.t list * Miniml.ml_type ) option

val extract_fixpoint :
Environ.env -> Evd.evar_map -> Names.Constant.t array ->
    (EConstr.t, EConstr.types) Constr.prec_declaration -> Miniml.ml_decl

val extract_inductive : Environ.env -> Names.MutInd.t -> Miniml.ml_ind

(** For Extraction Compute and Show Extraction *)

val extract_constr : Environ.env -> Evd.evar_map -> EConstr.t -> Miniml.ml_ast * Miniml.ml_type

(*s Is a [ml_decl] or a [ml_spec] logical ? *)

val logical_decl : Miniml.ml_decl -> bool
val logical_spec : Miniml.ml_spec -> bool
