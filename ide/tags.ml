(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


let make_tag (tt:GText.tag_table) ~name prop =
  let new_tag = GText.tag ~name () in
  new_tag#set_properties prop;
  tt#add new_tag#as_tag;
  new_tag

module Script =
struct
  (* More recently defined tags have highest priority in case of overlapping *)
  let table = GText.tag_table ()
  let warning = make_tag table ~name:"warning" [`UNDERLINE `SINGLE; `FOREGROUND "blue"]
  let error = make_tag table ~name:"error" [`UNDERLINE `SINGLE]
  let error_bg = make_tag table ~name:"error_bg" []
  let to_process = make_tag table ~name:"to_process" []
  let processed = make_tag table ~name:"processed" []
  let incomplete = make_tag table ~name:"incomplete" [`BACKGROUND_STIPPLE_SET true]
  let unjustified = make_tag table ~name:"unjustified" [`BACKGROUND "gold"]
  let tooltip = make_tag table ~name:"tooltip" [] (* debug:`BACKGROUND "blue" *)
  let ephemere =
    [error; warning; error_bg; tooltip; processed; to_process; incomplete; unjustified]
  let comment = make_tag table ~name:"comment" []
  let sentence = make_tag table ~name:"sentence" []
  let edit_zone = make_tag table ~name:"edit_zone" [`UNDERLINE `SINGLE] (* for debugging *)
  let all = edit_zone :: comment :: sentence :: ephemere
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
