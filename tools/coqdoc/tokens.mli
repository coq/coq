(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Type of dictionaries *)

type ttree

val empty_ttree : ttree

(* Add a string with some translation in dictionary *)
val ttree_add : ttree -> string -> string -> ttree

(* Remove a translation from a dictionary: returns an equal dictionary
   if the word not present *)
val ttree_remove : ttree -> string -> ttree

(* Translate a string *)
val translate : string -> string option

(* Sublexer automaton *)

(* The sublexer buffers the chars it receives; if after some time, it
   recognizes that a sequence of chars has a translation in the
   current dictionary, it replaces the buffer by the translation *)

(* Received chars can come with a "tag" (usually made from
   informations from the globalization file). A sequence of chars can
   be considered a word only, if all chars have the same "tag". Rules
   for cutting words are the following:

   - in a sequence like "**" where * is in the dictionary but not **,
     "**" is not translated; otherwise said, to be translated, a sequence
     must not be surrounded by other symbol-like chars

   - in a sequence like "<>_h*", where <>_h is in the dictionary, the
     translation is done because the switch from a letter to a symbol char
     is an acceptable cutting point

   - in a sequence like "<>_ha", where <>_h is in the dictionary, the
     translation is not done because it is considered that h and a are
     not separable (however, if h and a have different tags, and h has
     the same tags as <, > and _, the translation happens)

   - in a sequence like "<>_ha", where <> but not <>_h is in the
     dictionary, the translation is done for <> and _ha is considered
     independently because  the switch from a symbol char to a letter
     is considered to be an acceptable cutting point

   - the longest-word rule applies: if both <> and <>_h are in the
     dictionary, "<>_h" is one word and gets translated
*)

(* Warning: do not output anything on output channel inbetween a call
   to [output_tagged_*] and [flush_sublexer]!! *)

type out_function =
  bool (* needs escape *) ->
  bool (* it is a symbol, not a pure ident *) ->
  Index.index_entry option (* the index type of the token if any *) ->
  string -> unit

(* This must be initialized before calling the sublexer *)
val token_tree : ttree ref ref
val outfun : out_function ref

(* Process an ident part that might be a symbol part *)
val output_tagged_ident_string : string -> unit

(* Process a non-ident char (possibly equipped with a tag) *)
val output_tagged_symbol_char : Index.index_entry option -> char -> unit

(* Flush the buffered content of the lexer using [outfun] *)
val flush_sublexer : unit -> unit
