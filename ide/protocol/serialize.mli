(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Xml_datatype

exception Marshal_error of string * xml

val massoc: string -> (string * string) list -> string
val constructor: string -> string -> xml list -> xml
val do_match: string -> (string -> xml list -> 'b) -> xml -> 'b
val singleton: 'a list -> 'a
val raw_string: xml list -> string
val of_unit: unit -> xml
val to_unit: xml -> unit
val of_bool: bool -> xml
val to_bool: xml -> bool
val of_list: ('a -> xml) -> 'a list -> xml
val to_list: (xml -> 'a) -> xml -> 'a list
val of_option: ('a -> xml) -> 'a option -> xml
val to_option: (xml -> 'a) -> xml -> 'a option
val of_string: string -> xml
val to_string: xml -> string
val of_int: int -> xml
val to_int: xml -> int
val of_pair: ('a -> xml) -> ('b -> xml) -> 'a * 'b -> xml
val to_pair: (xml -> 'a) -> (xml -> 'b) -> xml -> 'a * 'b
val of_union: ('a -> xml) -> ('b -> xml) -> ('a, 'b) CSig.union -> xml
val to_union: (xml -> 'a) -> (xml -> 'b) -> xml -> ('a, 'b) CSig.union
val of_edit_id: int -> xml
val to_edit_id: xml -> int
val of_loc : Loc.t -> xml
val to_loc : xml -> Loc.t
val of_xml : xml -> xml
val to_xml : xml -> xml
