(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Evd

val short_version : unit -> string
val version : unit -> string

type coqtop

val dummy_coqtop : coqtop

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

  val set : coqtop -> t -> bool -> unit
end

val reset_initial : coqtop -> unit

val init : unit -> string list
val interp : coqtop -> bool -> string -> int

val rewind : coqtop -> int -> int

val process_exn : exn -> string*(Util.loc option)

val is_in_loadpath : coqtop -> string -> bool

val make_cases : coqtop -> string -> string list list

type tried_tactic =
  | Interrupted
  | Success of int (* nb of goals after *)
  | Failed

(* Message to display in lower status bar. *)

val current_status : coqtop -> string

type 'a menu = 'a * (string * string) list

type goals =
  | Message of string
  | Goals of ((string menu) list * string menu) list

val goals : coqtop -> goals
