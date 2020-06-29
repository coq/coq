(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type mutual_info =
  | NonMutual of EConstr.t Declare.CInfo.t
  | Mutual of
      { mutual_info : Declare.Proof.mutual_info
      ; cinfo : EConstr.t Declare.CInfo.t list
      ; possible_guards : int list
      }

val look_for_possibly_mutual_statements
  :  Evd.evar_map
  -> EConstr.t Declare.CInfo.t list
  -> mutual_info
