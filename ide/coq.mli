(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Evd
open Ide_blob

val short_version : unit -> string
val version : unit -> string
val filter_coq_opts : string list -> bool * string list

type coqtop

val dummy_coqtop : coqtop

val spawn_coqtop : string -> coqtop

val kill_coqtop : coqtop -> unit

val coqtop_zombies : unit -> int

val reset_coqtop : coqtop -> unit

val process_exn : exn -> string*(Util.loc option)

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

  val set : coqtop -> t -> bool -> unit Ide_blob.value
end

val raw_interp : coqtop -> string -> unit Ide_blob.value

val interp : coqtop -> bool -> string -> int Ide_blob.value

val rewind : coqtop -> int -> int Ide_blob.value

val read_stdout : coqtop -> string Ide_blob.value

val is_in_loadpath : coqtop -> string -> bool Ide_blob.value

val make_cases : coqtop -> string -> string list list Ide_blob.value

(* Message to display in lower status bar. *)

val current_status : coqtop -> string Ide_blob.value

val goals : coqtop -> goals Ide_blob.value

val msgnl : Pp.std_ppcmds -> string
