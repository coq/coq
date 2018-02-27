(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Extraction from Coq terms to Miniml. *)

open Names
open Constr
open Declarations
open Environ
open Miniml

val extract_constant : env -> Constant.t -> constant_body -> ml_decl

val extract_constant_spec : env -> Constant.t -> constant_body -> ml_spec

(** For extracting "module ... with ..." declaration *)

val extract_with_type : env -> constr -> ( Id.t list * ml_type ) option

val extract_fixpoint :
  env -> Constant.t array -> (constr, types) prec_declaration -> ml_decl

val extract_inductive : env -> MutInd.t -> ml_ind

(** For extraction compute *)

val extract_constr : env -> constr -> ml_ast * ml_type

(*s Is a [ml_decl] or a [ml_spec] logical ? *)

val logical_decl : ml_decl -> bool
val logical_spec : ml_spec -> bool
