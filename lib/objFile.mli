(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val magic_number : int32

type segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type in_handle
type out_handle

val open_in : file:string -> in_handle
val close_in : in_handle -> unit
val marshal_in_segment : in_handle -> segment:string -> 'a * Digest.t
val get_segment : in_handle -> segment:string -> segment
val segments : in_handle -> segment CString.Map.t

val open_out : file:string -> out_handle
val close_out : out_handle -> unit
val marshal_out_segment : out_handle -> segment:string -> 'a -> unit
val marshal_out_binary : out_handle -> segment:string -> out_channel * (unit -> unit)
(** Low-level API. This function returns a channel and a closure. The channel
    should only be written to, and once done, the closure should be invoked. *)
