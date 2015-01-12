(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module offers semi-structured pretty-printing. *)

(** Each annotation of the semi-structured document refers to the
    substring it annotates. *)
type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

(** [rich_pp get_annotations ppcmds] returns the interpretation
    of [ppcmds] as a string as well as a semi-structured document
    that represents (located) annotations of this string.
    The [get_annotations] function is used to convert tags into the desired
    annotation. If this function returns [None], then no annotation is put. *)
val rich_pp :
  (Pp.Tag.t -> 'annotation option) -> Pp.std_ppcmds ->
  string * 'annotation located Xml_datatype.gxml

(** [annotations_positions ssdoc] returns a list associating each
    annotations with its position in the string from which [ssdoc] is
    built. *)
val annotations_positions :
  'annotation located Xml_datatype.gxml ->
  ('annotation * (int * int)) list

(** [xml_of_rich_pp ssdoc] returns an XML representation of the
    semi-structured document [ssdoc]. *)
val xml_of_rich_pp :
  ('annotation -> string) ->
  ('annotation -> (string * string) list) ->
  'annotation located Xml_datatype.gxml ->
  Xml_datatype.xml
