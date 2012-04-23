(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


let make_tag (tt:GText.tag_table) ~name prop =
  let new_tag = GText.tag ~name () in
  new_tag#set_properties prop;
  tt#add new_tag#as_tag;
  new_tag

let processed_color = ref "light green"
let processing_color = ref "light blue"

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
  let to_process = make_tag table ~name:"to_process" [`BACKGROUND !processing_color ;`EDITABLE false]
  let processed = make_tag table ~name:"processed" [`BACKGROUND !processed_color;`EDITABLE false]
  let unjustified = make_tag table ~name:"unjustified" [`UNDERLINE `SINGLE; `FOREGROUND "red"; `BACKGROUND "gold";`EDITABLE false]
  let found = make_tag table ~name:"found" [`BACKGROUND "blue"; `FOREGROUND "white"]
  let hidden = make_tag table ~name:"hidden" [`INVISIBLE true; `EDITABLE false]
  let folded = make_tag table ~name:"locked" [`EDITABLE false; `BACKGROUND "light grey"]
  let paren = make_tag table ~name:"paren" [`BACKGROUND "purple"]
  let sentence = make_tag table ~name:"sentence" []
  let replaced = make_tag table ~name:"replaced" [`BACKGROUND "green"]
end
module Proof =
struct
  let table = GText.tag_table ()
  let highlight = make_tag table ~name:"highlight" [`BACKGROUND !processed_color]
  let hypothesis = make_tag table ~name:"hypothesis" []
  let goal = make_tag table ~name:"goal" []
end
module Message =
struct
  let table = GText.tag_table ()
  let error = make_tag table ~name:"error" [`FOREGROUND "red"]
end

let string_of_color clr =
  let r = Gdk.Color.red clr in
  let g = Gdk.Color.green clr in
  let b = Gdk.Color.blue clr in
  Printf.sprintf "#%04X%04X%04X" r g b

let color_of_string s =
  let colormap = Gdk.Color.get_system_colormap () in
  Gdk.Color.alloc ~colormap (`NAME s)

let get_processed_color () = color_of_string !processed_color

let set_processed_color clr =
  let s = string_of_color clr in
  processed_color := s;
  Script.processed#set_property (`BACKGROUND s);
  Proof.highlight#set_property (`BACKGROUND s)

let get_processing_color () = color_of_string !processing_color

let set_processing_color clr =
  let s = string_of_color clr in
  processing_color := s;
  Script.to_process#set_property (`BACKGROUND s)
