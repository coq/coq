(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This files implements typeclasses eauto *)

open Names
open Constr
open EConstr
open Tacmach

val catchable : exn -> bool

val set_typeclasses_debug : bool -> unit
val get_typeclasses_debug : unit -> bool

val set_typeclasses_depth : int option -> unit
val get_typeclasses_depth : unit -> int option

val typeclasses_eauto : ?only_classes:bool -> ?st:transparent_state ->
                        depth:(Int.t option) ->
                        Hints.hint_db_name list -> unit Proofview.tactic

val head_of_constr : Id.t -> constr -> unit Proofview.tactic

val not_evar : constr -> unit Proofview.tactic

val is_ground : constr -> tactic

val autoapply : constr -> Hints.hint_db_name -> unit Proofview.tactic

module Search : sig
  val eauto_tac :
    ?st:Names.transparent_state ->
    (** The transparent_state used when working with local hypotheses  *)
    only_classes:bool ->
    (** Should non-class goals be shelved and resolved at the end *)
    depth:Int.t option ->
    (** Bounded or unbounded search *)
    dep:bool ->
    (** Should the tactic be made backtracking on the initial goals,
       whatever their internal dependencies are. *)
    Hints.hint_db list ->
    (** The list of hint databases to use *)
    unit Proofview.tactic
end
