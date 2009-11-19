(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: coqide.ml 11952 2009-03-02 15:29:08Z vgross $ *)

open Ideutils


let underscore = Glib.Utf8.to_unichar "_" (ref 0)
let arobase = Glib.Utf8.to_unichar "@" (ref 0)
let prime = Glib.Utf8.to_unichar "'" (ref 0)
let bn = Glib.Utf8.to_unichar "\n" (ref 0)
let space = Glib.Utf8.to_unichar " " (ref 0)
let tab = Glib.Utf8.to_unichar "\t" (ref 0)


(* TODO: avoid num and prime at the head of a word *)
let is_word_char c =
  Glib.Unichar.isalnum c || c = underscore || c = prime


let starts_word (it:GText.iter) =
  prerr_endline ("Starts word ? '"^(Glib.Utf8.from_unichar it#char)^"'");
  (not it#copy#nocopy#backward_char ||
     (let c = it#backward_char#char in
	not (is_word_char c)))


let ends_word (it:GText.iter) =
  (not it#copy#nocopy#forward_char ||
     let c = it#forward_char#char in
       not (is_word_char c)
  )


let inside_word (it:GText.iter) =
  let c = it#char in
    not (starts_word it) &&
      not (ends_word it) &&
      is_word_char c


let is_on_word_limit (it:GText.iter) = inside_word it || ends_word it


let find_word_start (it:GText.iter) =
  let rec step_to_start it =
    prerr_endline "Find word start";
    if not it#nocopy#backward_char then
      (prerr_endline "find_word_start: cannot backward"; it)
    else if is_word_char it#char
    then step_to_start it
    else (it#nocopy#forward_char;
	prerr_endline ("Word start at: "^(string_of_int it#offset));it)
  in
    step_to_start it#copy


let find_word_end (it:GText.iter) =
  let rec step_to_end (it:GText.iter) =
    prerr_endline "Find word end";
    let c = it#char in
    if c<>0 && is_word_char c then (
      ignore (it#nocopy#forward_char);
      step_to_end it
    ) else (
      prerr_endline ("Word end at: "^(string_of_int it#offset));
      it)
  in
    step_to_end it#copy


let get_word_around (it:GText.iter) =
  let start = find_word_start it in
  let stop =  find_word_end it in
    start,stop


let rec complete_backward w (it:GText.iter) =
  prerr_endline "Complete backward...";
  match it#backward_search w with
    | None -> (prerr_endline "backward_search failed";None)
    | Some (start,stop) ->
	prerr_endline ("complete_backward got a match:"^(string_of_int start#offset)^(string_of_int stop#offset));
	if starts_word start then
	  let ne = find_word_end stop in
	    if ne#compare stop = 0
	    then complete_backward w start
	    else Some (start,stop,ne)
	else complete_backward w start


let rec complete_forward w (it:GText.iter) =
  prerr_endline "Complete forward...";
  match it#forward_search w with
    | None -> None
    | Some (start,stop) ->
	if starts_word start then
	  let ne = find_word_end stop in
	    if ne#compare stop = 0 then
	      complete_forward w stop
	    else Some (stop,stop,ne)
	else complete_forward w stop

