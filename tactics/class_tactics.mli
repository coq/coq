(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This files implements typeclasses eauto *)

open Names
open EConstr

val catchable : exn -> bool

val set_typeclasses_debug : bool -> unit
val get_typeclasses_debug : unit -> bool

val set_typeclasses_depth : int option -> unit
val get_typeclasses_depth : unit -> int option

type search_strategy = Dfs | Bfs

val set_typeclasses_strategy : search_strategy -> unit

val typeclasses_eauto : ?only_classes:bool -> ?st:transparent_state -> ?strategy:search_strategy ->
                        depth:(Int.t option) ->
                        Hints.hint_db_name list -> unit Proofview.tactic

val head_of_constr : Id.t -> constr -> unit Proofview.tactic

val not_evar : constr -> unit Proofview.tactic

val is_ground : constr -> unit Proofview.tactic

val autoapply : constr -> Hints.hint_db_name -> unit Proofview.tactic

module Search : sig
  val eauto_tac :
    ?st:Names.transparent_state ->
    (** The transparent_state used when working with local hypotheses  *)
    ?unique:bool ->
    (** Should we force a unique solution *)
    only_classes:bool ->
    (** Should non-class goals be shelved and resolved at the end *)
    ?strategy:search_strategy ->
    (** Is a traversing-strategy specified? *)
    depth:Int.t option ->
    (** Bounded or unbounded search *)
    dep:bool ->
    (** Should the tactic be made backtracking on the initial goals,
       whatever their internal dependencies are. *)
    Hints.hint_db list ->
    (** The list of hint databases to use *)
    unit Proofview.tactic
end
