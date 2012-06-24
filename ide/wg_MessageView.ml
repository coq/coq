(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type message_view =
  object
    inherit GObj.widget
    method add_selection_clipboard : GData.clipboard -> unit
    method clear : unit -> unit
    method push : Interface.message_level -> string -> unit
  end

let message_view () : message_view =
  let buffer = GText.buffer ~tag_table:Tags.Message.table () in
  let view = GText.view ~buffer
    ~editable:false ~cursor_visible:false ~wrap_mode:`WORD ()
  in
  let () = view#set_left_margin 2 in
  object
    inherit GObj.widget view#as_widget

    method clear () =
      buffer#set_text ""

    method push level msg =
      let tags = match level with
      | Interface.Error -> [Tags.Message.error]
      | _ -> []
      in
      buffer#insert ~tags msg

    method add_selection_clipboard cb =
      buffer#add_selection_clipboard cb

  end
