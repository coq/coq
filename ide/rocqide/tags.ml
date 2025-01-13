(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  let to_process = make_tag table ~name:"to_process" [`EDITABLE false]
  let processed = make_tag table ~name:"processed" []
  let debugging = make_tag table ~name:"debugging" []
  let incomplete = make_tag table ~name:"incomplete" [`EDITABLE false]
  let unjustified = make_tag table ~name:"unjustified" []
  let tooltip = make_tag table ~name:"tooltip" [] (* debug:`BACKGROUND "blue" *)
  let ephemere =
    [warning; error; error_bg; to_process; processed; debugging;
     incomplete; unjustified; tooltip]
  let comment = make_tag table ~name:"comment" []
  let sentence = make_tag table ~name:"sentence" []
  let breakpoint = make_tag table ~name:"breakpoint" []
  let edit_zone = make_tag table ~name:"edit_zone" [`UNDERLINE `SINGLE] (* for debugging *)
  let all_but_bpt = comment :: sentence :: edit_zone :: ephemere (* omit breakpoint marks *)
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
