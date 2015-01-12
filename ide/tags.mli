(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Script :
sig
  val table : GText.tag_table
  val comment : GText.tag
  val error : GText.tag
  val error_bg : GText.tag
  val to_process : GText.tag
  val processed : GText.tag
  val incomplete : GText.tag
  val unjustified : GText.tag
  val found : GText.tag
  val sentence : GText.tag
  val tooltip : GText.tag
  val edit_zone : GText.tag (* for debugging *)
  val all : GText.tag list

  (* Not part of the all list. Special tags! *)
  val read_only : GText.tag
end

module Proof :
sig
  val table : GText.tag_table
  val highlight : GText.tag
  val hypothesis : GText.tag
  val goal : GText.tag
end

module Message :
sig
  val table : GText.tag_table
  val error : GText.tag
  val warning : GText.tag
  val item : GText.tag
end

val string_of_color : Gdk.color -> string
val color_of_string : string -> Gdk.color

val get_processed_color : unit -> Gdk.color
val set_processed_color : Gdk.color -> unit

val get_processing_color : unit -> Gdk.color
val set_processing_color : Gdk.color -> unit

val get_error_color : unit -> Gdk.color
val set_error_color : Gdk.color -> unit
