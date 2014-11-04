(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module produces semi-structured pretty-printing. *)

(** A pretty printer module must use an instance of the following
    functor to index annotations. The index must be used as Format.tag
    during the pretty-printing. *)

(** The indices are Format.tags. *)
type index = Format.tag (* = string *)

module Indexer (Annotation : sig type t end) : sig

  (** [index annotation] returns a fresh index for the [annotation]. *)
  val index : Annotation.t -> index

  (** [get_annotations ()] returns a function to retrieve annotations
      from indices after pretty-printing. *)
  val get_annotations : unit -> (index -> Annotation.t)

end

(** Each annotation of the semi-structures document refers to the
    substring it annotates. *)
type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

(** [rich_pp get_annotations ppcmds] returns the interpretation
    of [ppcmds] as a string as well as a semi-structured document
    that represents (located) annotations of this string. *)
val rich_pp :
  (unit -> (index -> 'annotation)) ->
  (unit -> Pp.std_ppcmds) ->
  string * ('annotation located) Xml_datatype.gxml

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

