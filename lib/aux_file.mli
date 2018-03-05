(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type aux_file

val load_aux_file_for : string -> aux_file
val empty_aux_file : aux_file
val get : ?loc:Loc.t -> aux_file -> string -> string
val set : ?loc:Loc.t -> aux_file -> string -> string -> aux_file

module H : Map.S with type key = int * int
module M : Map.S with type key = string
val contents : aux_file -> string M.t H.t

val aux_file_name_for : string -> string
val start_aux_file : aux_file:string -> v_file:string -> unit
val stop_aux_file : unit -> unit 
val recording : unit -> bool

val record_in_aux_at : ?loc:Loc.t -> string -> string -> unit
val record_in_aux : string -> string -> unit
val record_in_aux_set_at : ?loc:Loc.t -> unit -> unit
