(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type message_view =
  object
    inherit GObj.widget
    method clear : unit
    method add : string -> unit
    method set : string -> unit
    method push : Pp.message_level -> string -> unit
      (** same as [add], but with an explicit level instead of [Notice] *)
    method buffer : GText.buffer
      (** for more advanced text edition *)
    method modify_font : Pango.font_description -> unit
  end

let message_view () : message_view =
  let buffer = GSourceView2.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Message.table ()
  in
  let text_buffer = new GText.buffer buffer#as_buffer in
  let box = GPack.vbox () in
  let scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(box#pack ~expand:true) () in
  let view = GSourceView2.source_view
    ~source_buffer:buffer ~packing:scroll#add
    ~editable:false ~cursor_visible:false ~wrap_mode:`WORD ()
  in
  let default_clipboard = GData.clipboard Gdk.Atom.primary in
  let _ = buffer#add_selection_clipboard default_clipboard in
  let () = view#set_left_margin 2 in
  object (self)
    inherit GObj.widget box#as_widget

    method clear =
      buffer#set_text ""

    method push level msg =
      let tags = match level with
      | Pp.Error -> [Tags.Message.error]
      | Pp.Warning -> [Tags.Message.warning]
      | _ -> []
      in
      if msg <> "" then begin
        buffer#insert ~tags msg;
        buffer#insert ~tags "\n"
      end

    method add msg = self#push Pp.Notice msg

    method set msg = self#clear; self#add msg

    method buffer = text_buffer

    method modify_font fd = view#misc#modify_font fd

  end
