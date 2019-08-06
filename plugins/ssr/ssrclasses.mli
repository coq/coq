(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Clone of [Rewrite.get_reflexive_proof],
    using [Coq.ssr.ssrclasses.Reflexive]
    instead of [Coq.Classes.RelationClasses.Reflexive] *)
val get_reflexive_proof_ssr :
  Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr -> Evd.evar_map * EConstr.constr
