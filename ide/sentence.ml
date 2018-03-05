(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {1 Sentences in coqide buffers } *)

(** Cut a part of the buffer in sentences and tag them.
    Invariant: either this slice ends the buffer, or it ends with ".".
    May raise [Coq_lex.Unterminated] when the zone ends with
    an unterminated sentence. *)

let split_slice_lax (buffer:GText.buffer) start stop =
  buffer#remove_tag ~start ~stop Tags.Script.sentence;
  buffer#remove_tag ~start ~stop Tags.Script.error;
  buffer#remove_tag ~start ~stop Tags.Script.warning;
  buffer#remove_tag ~start ~stop Tags.Script.error_bg;
  let slice = buffer#get_text ~start ~stop () in
  let apply_tag off tag =
    (* off is now a utf8-compliant char offset, cf Coq_lex.utf8_adjust *)
    let iter = start#forward_chars off in
    buffer#apply_tag ~start:iter ~stop:iter#forward_char tag
  in
  Coq_lex.delimit_sentences apply_tag slice

(** Searching forward and backward a position fulfilling some condition *)

let rec forward_search cond (iter:GText.iter) =
  if iter#is_end || cond iter then iter
  else forward_search cond iter#forward_char

let rec backward_search cond (iter:GText.iter) =
  if iter#is_start || cond iter then iter
  else backward_search cond iter#backward_char

let is_sentence_end s =
  s#has_tag Tags.Script.sentence

let is_char s c = s#char = Char.code c

(** Search backward the first character of a sentence, starting at [iter]
    and going at most up to [soi] (meant to be the end of the locked zone).
    Raise [StartError] when no proper sentence start has been found.
    A character following a ending "." is considered as a sentence start
    only if this character is a blank. In particular, when a final "."
    at the end of the locked zone isn't followed by a blank, then this
    non-blank character will be signaled as erroneous in [tag_on_insert] below.
*)

exception StartError

let grab_sentence_start (iter:GText.iter) soi =
  let cond iter =
    if iter#compare soi < 0 then raise StartError;
    let prev = iter#backward_char in
    is_sentence_end prev &&
      (not (is_char prev '.') ||
       List.exists (is_char iter) [' ';'\n';'\r';'\t'])
  in
  backward_search cond iter

(** Search forward the first character immediately after a sentence end *)

let grab_sentence_stop (start:GText.iter) =
  (forward_search is_sentence_end start)#forward_char

(** Search forward the first character immediately after a "." sentence end
    (and not just a "\{" or "\}" or comment end *)

let grab_ending_dot (start:GText.iter) =
  let is_ending_dot s = is_sentence_end s && s#char = Char.code '.' in
  (forward_search is_ending_dot start)#forward_char

(** Retag a zone that has been edited *)

let tag_on_insert buffer =
  (* the start of the non-locked zone *)
  let soi = buffer#get_iter_at_mark (`NAME "start_of_input") in
  (* the inserted zone is between [prev_insert] and [insert] *)
  let insert = buffer#get_iter_at_mark `INSERT in
  let prev = buffer#get_iter_at_mark (`NAME "prev_insert") in
  (* [prev] is normally always before [insert] even when deleting.
     Let's check this nonetheless *)
  let prev, insert =
    if insert#compare prev < 0 then insert, prev else prev, insert
  in
  try
    let start = grab_sentence_start prev soi in
    (** The status of "{" "}" as sentence delimiters is too fragile.
        We retag up to the next "." instead. *)
    let stop = grab_ending_dot insert in
    try split_slice_lax buffer start#backward_char stop
    with Coq_lex.Unterminated ->
      (* This shouldn't happen frequently. Either:
         - we are at eof, with indeed an unfinished sentence.
         - we have just inserted an opening of comment or string.
         - the inserted text ends with a "." that interacts with the "."
           found by [grab_ending_dot] to form a non-ending "..".
         In any case, we retag up to eof, since this isn't that costly. *)
      if not stop#is_end then
        let eoi = buffer#get_iter_at_mark (`NAME "stop_of_input") in
        try split_slice_lax buffer start eoi
        with Coq_lex.Unterminated -> ()
  with StartError ->
    buffer#apply_tag ~start:soi ~stop:soi#forward_char Tags.Script.error

let tag_all buffer =
  let soi = buffer#get_iter_at_mark (`NAME "start_of_input") in
  let eoi = buffer#get_iter_at_mark (`NAME "stop_of_input") in
  try split_slice_lax buffer soi eoi
  with Coq_lex.Unterminated -> ()

(** Search a sentence around some position *)

let find buffer (start:GText.iter) =
  let soi = buffer#get_iter_at_mark (`NAME "start_of_input") in
  try
    let start = grab_sentence_start start soi in
    let stop = grab_sentence_stop start in
    (* Is this phrase non-empty and complete ? *)
    if stop#compare start > 0 && is_sentence_end stop#backward_char
    then Some (start,stop)
    else None
  with StartError -> None
