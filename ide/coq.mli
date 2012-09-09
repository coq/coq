(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Coq : Interaction with the Coq toplevel *)

(** * Version and date *)

val short_version : unit -> string
val version : unit -> string

(** * Launch a test coqtop processes, ask for a correct coqtop if it fails.
    @return the list of arguments that coqtop did not understand
    (the files probably ..). This command may terminate coqide in
    case of trouble.  *)
val filter_coq_opts : string list -> string list

(** Launch a coqtop with the user args in order to be sure that it works,
    checking in particular that Prelude.vo is found. This command
    may terminate coqide in case of trouble *)
val check_connection : string list -> unit

(** * The structure describing a coqtop sub-process *)

(** Liveness management of coqtop is automatic. Whenever a Coqtop dies abruptly,
    this module is responsible for relaunching the whole process. The hook 
    passed as an argument in coqtop construction will be called after such an
    abrupt failure. In particular, it is NOT called when explicitely requesting 
    coqtop to close or to reset. *)

type coqtop
type handle

(** Count of all active coqtops *)
val coqtop_zombies : unit -> int

(** * Starting / signaling / ending a real coqtop sub-process *)

(** Create a coqtop process out of a hook and some command-line arguments.
    The hook SHALL NOT use [grab] or its variants, otherwise you'll deadlock! *)
val spawn_coqtop : (handle -> unit) -> string list -> coqtop

(** Interrupt the current computation of coqtop. Asynchronous. *)
val break_coqtop : coqtop -> unit

(** Close coqtop. Subsequent requests will be discarded. Hook ignored. *)
val close_coqtop : coqtop -> unit

(** Reset coqtop. Pending requests will be discarded. Default hook ignored, 
    provided one used instead. *)
val reset_coqtop : coqtop -> (handle -> unit) -> unit

(** Last resort against a reluctant coqtop (a.k.a. chainsaw massacre). 
    Asynchronous. *)
val kill_coqtop : coqtop -> unit

(** * Coqtop commmunication *)

(** Start a coqtop dialogue and ensure that there is no interfering process.
    - If coqtop ever dies during the computation, this function restarts coqtop 
      and calls the restart hook with the fresh coqtop.
    - If the argument function raises an exception, it is propagated.
    - The request may be discarded if a [close_coqtop] or [reset_coqtop] occurs
      before its completion.
*)
val grab : coqtop -> (handle -> unit) -> unit

(** As [grab], but applies the second callback if coqtop is already busy. Please
    consider using [try_grab] instead of [grab] except if you REALLY want 
    something to happen. *)
val try_grab : coqtop -> (handle -> unit) -> (unit -> unit) -> unit

(** Check if coqtop is computing. Does not take any lock. *)
val is_computing : coqtop -> bool

(** Check if coqtop is closed. Does not take any lock. *)
val is_closed : coqtop -> bool

(** In win32, we'll use a different kill function than Unix.kill *)

val killer : (int -> unit) ref
val interrupter : (int -> unit) ref

(** * Calls to Coqtop, cf [Serialize] for more details *)

type logger = Interface.message_level -> string -> unit
(** Except for interp, we use the default logger for any call. *)

val interp :
  handle -> logger -> ?raw:bool -> ?verbose:bool -> string -> string Interface.value
val rewind : handle -> int -> int Interface.value
val status : handle -> Interface.status Interface.value
val goals : handle -> Interface.goals option Interface.value
val evars : handle -> Interface.evar list option Interface.value
val hints : handle -> (Interface.hint list * Interface.hint) option Interface.value
val inloadpath : handle -> string -> bool Interface.value
val mkcases : handle -> string -> string list list Interface.value
val search : handle -> Interface.search_flags -> string Interface.coq_object list Interface.value

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

  val set_printing_width : int -> unit
  val set : handle -> (t * bool) list -> unit
end
