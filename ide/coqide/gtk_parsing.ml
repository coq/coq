(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let underscore = Glib.Utf8.to_unichar "_" ~pos:(ref 0)
let prime = Glib.Utf8.to_unichar "'" ~pos:(ref 0)
let dot = Glib.Utf8.to_unichar "." ~pos:(ref 0)

let find_word_start (it:GText.iter) =
  let rec aux it good =
    if it#is_start then good
    else
      let it = it#backward_char in
      let c = it#char in
      if Glib.Unichar.isalpha c || c = underscore then aux it it
      else if Glib.Unichar.isalnum c || c = prime || c = dot then aux it good
      else good in
  aux it it

let find_word_end (it:GText.iter) =
  let rec aux it good =
    if it#is_end then good
    else
      let c = it#char in
      let it = it#forward_char in
      if Glib.Unichar.isalnum c || c = prime || c = underscore then aux it it
      else if c = dot then aux it good
      else good in
  aux it it

let starts_word (it:GText.iter) =
  if it#is_start then true
  else
    let it = it#backward_char in
    let c = it#char in
    if Glib.Unichar.isalpha c || c = underscore then
      it#equal (find_word_start it)
    else false

let ends_word (it:GText.iter) =
  if it#is_end then true
  else
    let c = it#char in
    let it = it#forward_char in
    if Glib.Unichar.isalnum c || c = prime || c = underscore then
      it#equal (find_word_end it)
    else false

let get_word_around (it:GText.iter) =
  let start = find_word_start it in
  let stop =  find_word_end it in
    start,stop

(** On double-click on a view, select the whole word. This is a workaround for
    a deficient word handling in TextView. *)
let fix_double_click self =
  let callback ev = match GdkEvent.get_type ev with
  | `TWO_BUTTON_PRESS ->
    let iter = self#buffer#get_iter `INSERT in
    let start, stop = get_word_around iter in
    let () = self#buffer#move_mark `INSERT ~where:start in
    let () = self#buffer#move_mark `SEL_BOUND ~where:stop in
    true
  | _ -> false
  in
  ignore (self#event#connect#button_press ~callback)
