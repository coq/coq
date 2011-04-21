(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Coq : Interaction with the Coq toplevel *)

(** * Version and date *)

val short_version : unit -> string
val version : unit -> string

(** * Initial checks by launching test coqtop processes *)

val filter_coq_opts : string list -> bool * string list

(** A mock coqtop launch, checking in particular that initial.coq is found *)
val check_connection : string list -> unit

(** Same, with less checks, but returning coqlib *)
val check_coqlib : string list -> string

(** * The structure describing a coqtop sub-process *)

type coqtop

(** * Count of all active coqtops *)

val coqtop_zombies : unit -> int

(** * Starting / signaling / ending a real coqtop sub-process *)

val spawn_coqtop : string list -> coqtop
val kill_coqtop : coqtop -> unit
val break_coqtop : coqtop -> unit
val reset_coqtop : coqtop -> coqtop

val process_exn : exn -> Ide_intf.location * string

(** In win32, we'll use a different kill function than Unix.kill *)

val killer : (int -> unit) ref

(** * Calls to Coqtop, cf [Ide_intf] for more details *)

val interp : coqtop -> bool -> string -> unit Ide_intf.value
val raw_interp : coqtop -> string -> unit Ide_intf.value
val read_stdout : coqtop -> string Ide_intf.value
val rewind : coqtop -> int -> unit Ide_intf.value
val is_in_loadpath : coqtop -> string -> bool Ide_intf.value
val make_cases : coqtop -> string -> string list list Ide_intf.value
val current_status : coqtop -> string Ide_intf.value
val current_goals : coqtop -> Ide_intf.goals Ide_intf.value

(** A specialized version of [raw_interp] dedicated to
    set/unset options. *)

module PrintOpt :
sig
  type t
  val implicit : t
  val coercions : t
  val raw_matching : t
  val notations : t
  val all_basic : t
  val existential : t
  val universes : t

  val set : coqtop -> t -> bool -> unit Ide_intf.value
end
