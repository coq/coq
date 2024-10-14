(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type button_contents =
| ButtonWithStock of GtkStock.id
| ButtonWithLabel of string

val question_box :
  ?parent:GWindow.window -> ?icon:#GObj.widget -> title:string ->
  ?buttons:button_contents list -> ?default:int -> string -> int

val message_box :
  ?parent:GWindow.window -> ?icon:#GObj.widget -> title:string ->
  ?ok:button_contents -> string -> unit
