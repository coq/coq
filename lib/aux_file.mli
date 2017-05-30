(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type aux_file

val load_aux_file_for : string -> aux_file
val get : aux_file -> Loc.t -> string -> string
val empty_aux_file : aux_file
val set : aux_file -> Loc.t -> string -> string -> aux_file

module H : Map.S with type key = int * int
module M : Map.S with type key = string
val contents : aux_file -> string M.t H.t

val aux_file_name_for : string -> string
val start_aux_file : aux_file:string -> v_file:string -> unit
val stop_aux_file : unit -> unit 
val recording : unit -> bool

val record_in_aux_at : Loc.t -> string -> string -> unit
val record_in_aux : string -> string -> unit
val record_in_aux_set_at : Loc.t -> unit
