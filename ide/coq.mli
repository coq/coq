(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val short_version : unit -> string
val version : unit -> string
val filter_coq_opts : string list -> bool * string list
val check_connection : string list -> unit

type coqtop

val spawn_coqtop : string list -> coqtop

val kill_coqtop : coqtop -> unit

val break_coqtop : coqtop -> unit

val coqtop_zombies : unit -> int

val reset_coqtop : coqtop -> unit

val process_exn : exn -> Ide_intf.location * string

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

val raw_interp : coqtop -> string -> unit Ide_intf.value

val interp : coqtop -> bool -> string -> int Ide_intf.value

val rewind : coqtop -> int -> int Ide_intf.value

val read_stdout : coqtop -> string Ide_intf.value

val is_in_loadpath : coqtop -> string -> bool Ide_intf.value

val make_cases : coqtop -> string -> string list list Ide_intf.value

(* Message to display in lower status bar. *)

val current_status : coqtop -> string Ide_intf.value

val goals : coqtop -> Ide_intf.goals Ide_intf.value

val msgnl : Pp.std_ppcmds -> string
