(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Script :
sig
  val table : GText.tag_table
  val comment : GText.tag
  val error : GText.tag
  val warning : GText.tag
  val error_bg : GText.tag
  val to_process : GText.tag
  val processed : GText.tag
  val breakpoint : GText.tag
  val debugging : GText.tag
  val incomplete : GText.tag
  val unjustified : GText.tag
  val sentence : GText.tag
  val tooltip : GText.tag
  val edit_zone : GText.tag (* for debugging *)
  val ephemere : GText.tag list
  val all_but_bpt : GText.tag list
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
