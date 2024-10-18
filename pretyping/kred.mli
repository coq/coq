(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open RedFlags

(** Global and local constant cache *)
type clos_infos
type clos_tab

val create_clos_infos :
  ?univs:UGraph.t -> ?evars:CClosure.evar_handler -> reds -> env -> clos_infos

val create_tab : unit -> clos_tab

(** Reduction function *)

val norm_term : clos_infos -> clos_tab -> Constr.constr -> Constr.constr
val whd_term : clos_infos -> clos_tab -> Constr.constr -> Constr.constr

val norm : reds -> Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr
val whd : reds -> Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr
