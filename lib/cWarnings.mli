(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type status =
  Disabled | Enabled | AsError

(*
type 'a repr = {
  print : 'a -> Pp.std_ppcmds;
  kind : string;
  enabled : bool;
}
 *)

val set_current_loc : Loc.t -> unit

val create : name:string -> category:string -> ?default:status ->
             ('a -> Pp.std_ppcmds) -> ?loc:Loc.t -> 'a -> unit

(*
val emit : 'a t -> 'a -> unit

type any = Any : string * string * 'a repr -> any

val dump : unit -> any list
 *)

val get_flags : unit -> string
val set_flags : string -> unit
