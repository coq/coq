(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let underscore = Glib.Utf8.to_unichar "_" ~pos:(ref 0)
let arobase = Glib.Utf8.to_unichar "@" ~pos:(ref 0)
let prime = Glib.Utf8.to_unichar "'" ~pos:(ref 0)
let bn = Glib.Utf8.to_unichar "\n" ~pos:(ref 0)
let space = Glib.Utf8.to_unichar " " ~pos:(ref 0)
let tab = Glib.Utf8.to_unichar "\t" ~pos:(ref 0)


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


let inside_word (it:GText.iter) =
  let c = it#char in
    not (starts_word it) &&
      not (ends_word it) &&
      is_word_char c


let is_on_word_limit (it:GText.iter) = inside_word it || ends_word it


let find_word_start (it:GText.iter) =
  let rec step_to_start it =
    Minilib.log "Find word start";
    if not it#nocopy#backward_char then
      (Minilib.log "find_word_start: cannot backward"; it)
    else if is_word_char it#char
    then step_to_start it
    else (it#nocopy#forward_char;
	Minilib.log ("Word start at: "^(string_of_int it#offset));it)
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


let rec complete_backward w (it:GText.iter) =
  Minilib.log "Complete backward...";
  match it#backward_search w with
    | None -> (Minilib.log "backward_search failed";None)
    | Some (start,stop) ->
	Minilib.log ("complete_backward got a match:"^(string_of_int start#offset)^(string_of_int stop#offset));
	if starts_word start then
	  let ne = find_word_end stop in
	    if ne#compare stop = 0
	    then complete_backward w start
	    else Some (start,stop,ne)
	else complete_backward w start


let rec complete_forward w (it:GText.iter) =
  Minilib.log "Complete forward...";
  match it#forward_search w with
    | None -> None
    | Some (start,stop) ->
	if starts_word start then
	  let ne = find_word_end stop in
	    if ne#compare stop = 0 then
	      complete_forward w stop
	    else Some (stop,stop,ne)
	else complete_forward w stop


let find_comment_end (start:GText.iter) =
  let rec find_nested_comment (search_start:GText.iter) (search_end:GText.iter) (comment_end:GText.iter) =
    match (search_start#forward_search ~limit:search_end "(*"),(comment_end#forward_search "*)") with
      | None,_ -> comment_end
      | Some _, None -> raise Not_found
      | Some (_,next_search_start),Some (next_search_end,next_comment_end) ->
          find_nested_comment next_search_start next_search_end next_comment_end
  in
    match start#forward_search "*)" with
      | None -> raise Not_found
      | Some (search_end,comment_end) -> find_nested_comment start search_end comment_end


let rec find_string_end (start:GText.iter) =
  let dblquote = int_of_char '"' in
  let rec escaped_dblquote c =
    (c#char = dblquote) && not (escaped_dblquote c#backward_char)
  in
    match start#forward_search "\"" with
      | None -> raise Not_found
      | Some (stop,next_start) ->
          if escaped_dblquote stop#backward_char
          then find_string_end next_start
          else next_start


let rec find_next_sentence (from:GText.iter) =
  match (from#forward_search ".") with
    | None -> raise Not_found
    | Some (non_vernac_search_end,next_sentence) ->
        match from#forward_search ~limit:non_vernac_search_end "(*",from#forward_search ~limit:non_vernac_search_end "\"" with
          | None,None ->
              if Glib.Unichar.isspace next_sentence#char || next_sentence#compare next_sentence#forward_char == 0
              then next_sentence else find_next_sentence next_sentence
          | None,Some (_,string_search_start) -> find_next_sentence (find_string_end string_search_start)
          | Some (_,comment_search_start),None -> find_next_sentence (find_comment_end comment_search_start)
          | Some (_,comment_search_start),Some (_,string_search_start) ->
              find_next_sentence (
                if comment_search_start#compare string_search_start < 0
                then find_comment_end comment_search_start
                else find_string_end string_search_start)


let find_nearest_forward (cursor:GText.iter) targets =
  let fold_targets acc target =
    match cursor#forward_search target,acc with
      | Some (t_start,_),Some nearest when (t_start#compare nearest < 0) -> Some t_start
      | Some (t_start,_),None -> Some t_start
      | _ -> acc
  in
    match List.fold_left fold_targets None targets with
      | None -> raise Not_found
      | Some nearest -> nearest


let find_nearest_backward (cursor:GText.iter) targets =
  let fold_targets acc target =
    match cursor#backward_search target,acc with
      | Some (t_start,_),Some nearest when (t_start#compare nearest > 0) -> Some t_start
      | Some (t_start,_),None -> Some t_start
      | _ -> acc
  in
    match List.fold_left fold_targets None targets with
      | None -> raise Not_found
      | Some nearest -> nearest

