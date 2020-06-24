(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files implements typeclasses eauto *)

open Names
open EConstr

val typeclasses_db : string

val set_typeclasses_debug : bool -> unit

val set_typeclasses_depth : int option -> unit

type search_strategy = Dfs | Bfs

val set_typeclasses_strategy : search_strategy -> unit

val typeclasses_eauto :
  ?only_classes:bool
  (** Should non-class goals be shelved and resolved at the end *)
  -> ?st:TransparentState.t
  (** The transparent_state used when working with local hypotheses  *)
  -> ?strategy:search_strategy
  (** Is a traversing-strategy specified? *)
  -> depth:(Int.t option)
  (** Bounded or unbounded search *)
  -> Hints.hint_db_name list
  (** The list of hint databases to use *)
  -> unit Proofview.tactic

val head_of_constr : Id.t -> constr -> unit Proofview.tactic

val not_evar : constr -> unit Proofview.tactic

val is_ground : constr -> unit Proofview.tactic

val autoapply : constr -> Hints.hint_db_name -> unit Proofview.tactic

module Search : sig
  val eauto_tac :
    Hints.hint_mode array list GlobRef.Map.t * TransparentState.t
    (** The transparent_state and modes used when working with local hypotheses  *)
    -> ?unique:bool
    (** Should we force a unique solution *)
    -> only_classes:bool
    (** Should non-class goals be shelved and resolved at the end *)
    -> ?strategy:search_strategy
    (** Is a traversing-strategy specified? *)
    -> depth:Int.t option
    (** Bounded or unbounded search *)
    -> dep:bool
    (** Should the tactic be made backtracking on the initial goals,
        whatever their internal dependencies are. *)
    -> Hints.hint_db list
    (** The list of hint databases to use *)
    -> unit Proofview.tactic
    (** Note: there might be stuck goals due to mode declarations
      remaining even in case of success of the tactic. *)
end
