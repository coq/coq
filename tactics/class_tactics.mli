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
open Tacmach

val catchable : exn -> bool

val set_typeclasses_debug : bool -> unit
val get_typeclasses_debug : unit -> bool

val set_typeclasses_depth : int option -> unit
val get_typeclasses_depth : unit -> int option

val progress_evars : unit Proofview.tactic -> unit Proofview.tactic

val typeclasses_eauto : ?only_classes:bool -> ?st:transparent_state ->
  Hints.hint_db_name list -> tactic

val head_of_constr : Id.t -> Term.constr -> unit Proofview.tactic

val not_evar : constr -> unit Proofview.tactic

val is_ground : constr -> tactic

val autoapply : constr -> Hints.hint_db_name -> tactic
       
type newautoinfo =
  { search_depth : int list;
    last_tac : Pp.std_ppcmds Lazy.t;
    search_dep : bool;
    search_cut : Hints.hints_path;
    search_hints : Hints.Hint_db.t }

val new_hints_tac : bool -> Hints.hint_db list ->
                    newautoinfo ->
                    (newautoinfo -> unit Proofview.tactic) -> unit Proofview.tactic

val make_autogoal' : ?st:Names.transparent_state ->
           bool -> bool ->
           Hints.hints_path -> int -> ([ `NF ], 'c) Proofview.Goal.t -> newautoinfo

val new_eauto_tac : ?st:Names.transparent_state ->
           bool -> ?limit:Int.t -> 
           Hints.hint_db list -> unit Proofview.tactic

