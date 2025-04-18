(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val magic_number : int32

type 'a segment = private {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type 'a id = private { id : string }
(** Private to ensure the phantom tag is injective *)

type in_handle
type out_handle

val make_id : string -> 'a id

val open_in : file:string -> in_handle
val close_in : in_handle -> unit
val marshal_in_segment : in_handle -> segment:'a id -> 'a * Digest.t
val get_segment : in_handle -> segment:'a id -> 'a segment
val segments : in_handle -> Obj.t segment CString.Map.t

val open_out : file:string -> out_handle
val close_out : out_handle -> unit
val marshal_out_segment : out_handle -> segment:'a id -> 'a -> unit
val marshal_out_binary : out_handle -> segment:'a id -> out_channel * (unit -> unit)
(** [marshal_out_binary oh segment] is a low level, stateful, API returning
    [oc, stop]. Once called no other API can be used on the same [oh] and only
    [Stdlib.output_*] APIs should be used on [oc]. [stop ()] must be invoked in
    order to signal that all data was written to [oc] (which should not be used
    afterwards). Only after calling [stop] the other API can be used on [oh]. *)

module Delayed : sig
  type 'a t
  (** Serialized objects loaded on-the-fly *)

  val make : file:string -> what:string option -> whatfor:string -> in_handle -> segment:'a id -> 'a t
  (** [whatfor] is expected to be the dirpath of the file.
      If [what] is [Some str] we print "Fetching str ..." when forced. *)

  val return : 'a -> 'a t

  val eval : verbose:bool -> 'a t -> 'a
  (** Fetches the value. If the digest changed since the [in_delayed]
      call, raises an error.

      With [verbose:true], if the value has not been previously
      fetched, print a message to msg_info.

      Calling [eval] multiple times on a given ['a t] value only does
      the work once (like Lazy.force). *)
end
