(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module offers semi-structured pretty-printing. *)

(** Each annotation of the semi-structured document refers to the
    substring it annotates. *)
type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

(* XXX: The width parameter should be moved to a `formatter_property`
   record shared with Topfmt *)

(** [rich_pp width ppcmds] returns the interpretation
    of [ppcmds] as a semi-structured document
    that represents (located) annotations of this string.
    The [get_annotations] function is used to convert tags into the desired
    annotation. [width] sets the printing witdh of the formatter. *)
val rich_pp : int -> Pp.t -> Pp.pp_tag located Xml_datatype.gxml

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

(** {5 Enriched text} *)

type richpp = Xml_datatype.xml

(** Type of text with style annotations *)

val richpp_of_pp : int -> Pp.t -> richpp
(** Extract style information from formatted text *)
