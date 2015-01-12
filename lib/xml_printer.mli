(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type xml = Xml_datatype.xml

type t
type target = TChannel of out_channel | TBuffer of Buffer.t

val make : target -> t

(** Print the xml data structure to a source into a compact xml string (without
 any user-readable formating ). *)
val print : t -> xml -> unit

(** Print the xml data structure into a compact xml string (without
 any user-readable formating ). *)
val to_string : xml -> string

(** Print the xml data structure into an user-readable string with
 tabs and lines break between different nodes. *)
val to_string_fmt : xml -> string

(** Print PCDATA as a string by escaping XML entities. *)
val pcdata_to_string : string -> string
