(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)


let make_tag (tt:GText.tag_table) ~name prop =
  let new_tag = GText.tag ~name () in
  new_tag#set_properties prop;
  tt#add new_tag#as_tag;
  new_tag

module Script =
struct
  let table = GText.tag_table ()
  let kwd = make_tag table ~name:"kwd" [`FOREGROUND "blue"]
  let qed = make_tag table ~name:"qed" [`FOREGROUND "blue"]
  let decl = make_tag table ~name:"decl" [`FOREGROUND "orange red"]
  let proof_decl = make_tag table ~name:"proof_decl" [`FOREGROUND "orange red"]
  let comment = make_tag table ~name:"comment" [`FOREGROUND "brown"]
  let reserved = make_tag table ~name:"reserved" [`FOREGROUND "dark red"]
  let error = make_tag table ~name:"error" [`UNDERLINE `DOUBLE ; `FOREGROUND "red"]
  let to_process = make_tag table ~name:"to_process" [`BACKGROUND "light blue" ;`EDITABLE false]
  let processed = make_tag table ~name:"processed" [`BACKGROUND "light green" ;`EDITABLE false]
  let unjustified = make_tag table ~name:"unjustified" [`UNDERLINE `SINGLE; `FOREGROUND "red"; `BACKGROUND "gold";`EDITABLE false]
  let found = make_tag table ~name:"found" [`BACKGROUND "blue"; `FOREGROUND "white"]
  let hidden = make_tag table ~name:"hidden" [`INVISIBLE true; `EDITABLE false]
  let folded = make_tag table ~name:"locked" [`EDITABLE false; `BACKGROUND "light grey"]
  let paren = make_tag table ~name:"paren" [`BACKGROUND "purple"]
  let lax_end = make_tag table ~name:"sentence_end" []
end
module Proof =
struct
  let table = GText.tag_table ()
  let highlight = make_tag table ~name:"highlight" [`BACKGROUND "light green"]
  let hypothesis = make_tag table ~name:"hypothesis" []
  let goal = make_tag table ~name:"goal" []
end
module Message =
struct
  let table = GText.tag_table ()
  let error = make_tag table ~name:"error" [`FOREGROUND "red"]
end

