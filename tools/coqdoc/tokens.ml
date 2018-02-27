(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Application of printing rules based on a dictionary specific to the
   target language *)

(*s Dictionaries: trees annotated with string options, each node being a map
    from chars to dictionaries (the subtrees). A trie, in other words.

    (code copied from parsing/lexer.ml4 for the use of coqdoc, Apr 2010)
*)

module CharMap = Map.Make (struct
  type t = char
  let compare (x : t) (y : t) = compare x y
end)

type ttree = {
  node : string option;
  branch : ttree CharMap.t }

let empty_ttree = { node = None; branch = CharMap.empty }

let ttree_add ttree str translated =
  let rec insert tt i =
    if i == String.length str then
      {node = Some translated; branch = tt.branch}
    else
      let c = str.[i] in
      let br =
        match try Some (CharMap.find c tt.branch) with Not_found -> None with
          | Some tt' ->
              CharMap.add c (insert tt' (i + 1)) (CharMap.remove c tt.branch)
          | None ->
              let tt' = {node = None; branch = CharMap.empty} in
              CharMap.add c (insert tt' (i + 1)) tt.branch
      in
      { node = tt.node; branch = br }
  in
  insert ttree 0

(* Removes a string from a dictionary: returns an equal dictionary
   if the word not present. *)
let ttree_remove ttree str =
  let rec remove tt i =
    if i == String.length str then
      {node = None; branch = tt.branch}
    else
      let c = str.[i] in
      let br =
        match try Some (CharMap.find c tt.branch) with Not_found -> None with
          | Some tt' ->
              CharMap.add c (remove tt' (i + 1)) (CharMap.remove c tt.branch)
          | None -> tt.branch
      in
      { node = tt.node; branch = br }
  in
  remove ttree 0

let ttree_descend ttree c = CharMap.find c ttree.branch

let ttree_find ttree str =
  let rec proc_rec tt i =
    if i == String.length str then tt
    else proc_rec (CharMap.find str.[i] tt.branch) (i+1)
  in
  proc_rec ttree 0

(*s Parameters of the translation automaton *)

type out_function = bool -> bool -> Index.index_entry option -> string -> unit

let token_tree = ref (ref empty_ttree)
let outfun = ref (fun _ _ _ _ -> failwith "outfun not initialized")

(*s Translation automaton *)

let buff = Buffer.create 4

let flush_buffer was_symbolchar tag tok =
  let hastr = String.length tok <> 0 in
  if hastr then !outfun false was_symbolchar tag tok;
  if Buffer.length buff <> 0 then
    !outfun true (if hastr then not was_symbolchar else was_symbolchar)
      tag (Buffer.contents buff);
  Buffer.clear buff

type sublexer_state =
  | Neutral
  | Buffering of bool * Index.index_entry option * string * ttree

let translation_state = ref Neutral

let buffer_char is_symbolchar ctag c =
  let rec aux = function
  | Neutral ->
      restart_buffering ()
  | Buffering (was_symbolchar,tag,translated,tt) ->
      if tag <> ctag then
	(* A strong tag comes from Coq; if different Coq tags *)
	(* hence, we don't try to see the chars as part of a single token *)
	let translated =
	  match tt.node with
	  | Some tok -> Buffer.clear buff; tok
	  | None -> translated in
	flush_buffer was_symbolchar tag translated;
	restart_buffering ()
      else
	begin
	(* If we change the category of characters (symbol vs ident) *)
	(* we accept this as a possible token cut point and remember the *)
	(* translated token up to that point *)
	let translated =
	  if is_symbolchar <> was_symbolchar then
	    match tt.node with
	    | Some tok -> Buffer.clear buff; tok
	    | None -> translated
	  else translated in
	(* We try to make a significant token from the current *)
	(* buffer and the new character *)
	try
	  let tt = ttree_descend tt c in
	  Buffer.add_char buff c;
	  Buffering (is_symbolchar,ctag,translated,tt)
	with Not_found ->
	(* No existing translation for the given set of chars *)
	if is_symbolchar <> was_symbolchar then
	  (* If we changed the category of character read, we accept it *)
	  (* as a possible cut point and restart looking for a translation *)
	  (flush_buffer was_symbolchar tag translated;
	   restart_buffering ())
	else
	  (* If we did not change the category of character read, we do *)
	  (* not want to cut arbitrarily in the middle of the sequence of *)
	  (*  symbol characters or identifier characters *)
	  (Buffer.add_char buff c;
	   Buffering (is_symbolchar,tag,translated,empty_ttree))
	end

  and restart_buffering () =
    let tt = try ttree_descend !(!token_tree) c with Not_found -> empty_ttree in
    Buffer.add_char buff c;
    Buffering (is_symbolchar,ctag,"",tt)

  in
  translation_state := aux !translation_state

let output_tagged_ident_string s =
  for i = 0 to String.length s - 1 do buffer_char false None s.[i] done

let output_tagged_symbol_char tag c =
  buffer_char true tag c

let flush_sublexer () =
  match !translation_state with
  | Neutral -> ()
  | Buffering (was_symbolchar,tag,translated,tt) ->
      let translated =
	match tt.node with
	| Some tok -> Buffer.clear buff; tok
	| None -> translated in
      flush_buffer was_symbolchar tag translated;
      translation_state := Neutral

(* Translation not using the automaton *)
let translate s =
  try (ttree_find !(!token_tree) s).node with Not_found -> None
