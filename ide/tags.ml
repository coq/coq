(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


let make_tag (tt:GText.tag_table) ~name prop =
  let new_tag = GText.tag ~name () in
  new_tag#set_properties prop;
  tt#add new_tag#as_tag;
  new_tag

module Script =
struct
  let table = GText.tag_table ()
  let comment = make_tag table ~name:"comment" []
  let error = make_tag table ~name:"error" [`UNDERLINE `SINGLE]
  let error_bg = make_tag table ~name:"error_bg" []
  let to_process = make_tag table ~name:"to_process" []
  let processed = make_tag table ~name:"processed" []
  let incomplete = make_tag table ~name:"incomplete" [
          `BACKGROUND_STIPPLE_SET true;
  ]
  let unjustified = make_tag table ~name:"unjustified" [`BACKGROUND "gold"]
  let found = make_tag table ~name:"found" [`BACKGROUND "blue"; `FOREGROUND "white"]
  let sentence = make_tag table ~name:"sentence" []
  let tooltip = make_tag table ~name:"tooltip" [] (* debug:`BACKGROUND "blue" *)

  let all =
    [comment; error; error_bg; to_process; processed; incomplete; unjustified;
     found; sentence; tooltip]

  let edit_zone =
    let t = make_tag table ~name:"edit_zone" [`UNDERLINE `SINGLE] in
    t#set_priority (List.length all);
    t
  let all = edit_zone :: all
  
end
module Proof =
struct
  let table = GText.tag_table ()
  let highlight = make_tag table ~name:"highlight" []
  let hypothesis = make_tag table ~name:"hypothesis" []
  let goal = make_tag table ~name:"goal" []
end
module Message =
struct
  let table = GText.tag_table ()
  let error = make_tag table ~name:"error" [`FOREGROUND "red"]
  let warning = make_tag table ~name:"warning" [`FOREGROUND "orange"]
  let item = make_tag table ~name:"item" [`WEIGHT `BOLD]
end

let string_of_color clr =
  let r = Gdk.Color.red clr in
  let g = Gdk.Color.green clr in
  let b = Gdk.Color.blue clr in
  Printf.sprintf "#%04X%04X%04X" r g b

let color_of_string s =
  let colormap = Gdk.Color.get_system_colormap () in
  Gdk.Color.alloc ~colormap (`NAME s)
