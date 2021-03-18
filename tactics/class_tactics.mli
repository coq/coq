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
  (** Should non-class goals be shelved and resolved at the end. Default: false *)
  -> ?keep_stuck_failures:bool
  (** Default: false. All stuck goals to remain in the result. We explore the
    whole search space to find a complete solution but if that fails,
    we return the first solution (if any) with only stuck constraints:
    the remaining constraints eithre do not validate the modes declared
    for their heads in the database, or they do but have no solution.
    This is useful to debug eauto calls. *)
  -> ?st:TransparentState.t
  (** Default: full. The transparent_state used when working with local hypotheses  *)
  -> ?strategy:search_strategy
  (** Default: governed by a global flag, which itself defaults to depth-first search.
    Is a traversing-strategy specified? *)
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
    -> keep_stuck_failures:bool
    (** If true, when considering a proof search problem with stuck goals
        (at the toplevel of the proof search only), we perform proof search
        on the rest of the goals and report these stuck goals
        (if they remaing unsolved) at the end.
        Stuck goals are constraints that do not match the mode declared
        for their head (i.e. a class), so we cannot even try to solve them,
        or that match it but have no solution (for a single run of the resolution).
        This is an approximation: there might in general be other, different runs
        of resolution fail too and generate different instantiations of the stuck goals.
        However it is still sound: providing instances for the reported stuck constraints
        would provide a solution to the whole proof search problem. *)
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
