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

open Names
open Declarations
open Environ
open Evd
open Miniml

val extract_constant : Global.indirect_accessor -> env -> Constant.t -> constant_body -> ml_decl

val extract_constant_spec : env -> Constant.t -> ('a, 'b) pconstant_body -> ml_spec

(** For extracting "module ... with ..." declaration *)

val extract_with_type :
  env -> evar_map -> EConstr.t -> ( Id.t list * ml_type ) option

val extract_fixpoint :
  env -> evar_map -> Constant.t array -> EConstr.rec_declaration -> ml_decl

val extract_inductive : env -> MutInd.t -> ml_ind

(** For Extraction Compute and Show Extraction *)

val extract_constr : env -> evar_map -> EConstr.t -> ml_ast * ml_type

(*s Is a [ml_decl] or a [ml_spec] logical ? *)

val logical_decl : ml_decl -> bool
val logical_spec : ml_spec -> bool
