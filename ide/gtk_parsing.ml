(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let underscore = Glib.Utf8.to_unichar "_" ~pos:(ref 0)
let prime = Glib.Utf8.to_unichar "'" ~pos:(ref 0)


(* TODO: avoid num and prime at the head of a word *)
let is_word_char c =
  Glib.Unichar.isalnum c || c = underscore || c = prime


let starts_word (it:GText.iter) =
  (it#is_start ||
    (let c = it#backward_char#char in
      not (is_word_char c)))

let ends_word (it:GText.iter) =
  (it#is_end ||
     let c = it#forward_char#char in
       not (is_word_char c)
  )

let find_word_start (it:GText.iter) =
  let rec step_to_start it =
    Minilib.log "Find word start";
    if not it#nocopy#backward_char then
      (Minilib.log "find_word_start: cannot backward"; it)
    else if is_word_char it#char
    then step_to_start it
    else begin
      ignore(it#nocopy#forward_char);
      Minilib.log ("Word start at: "^(string_of_int it#offset));
      it
    end
  in
    step_to_start it#copy

let find_word_end (it:GText.iter) =
  let rec step_to_end (it:GText.iter) =
    Minilib.log "Find word end";
    let c = it#char in
    if c<>0 && is_word_char c then (
      ignore (it#nocopy#forward_char);
      step_to_end it
    ) else (
      Minilib.log ("Word end at: "^(string_of_int it#offset));
      it)
  in
    step_to_end it#copy


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
