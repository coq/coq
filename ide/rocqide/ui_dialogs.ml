(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type button_contents =
| ButtonWithStock of GtkStock.id
| ButtonWithLabel of string

let question_box ?parent ?icon ~title ?(buttons = []) ?(default = 1) message =
  let button_nb = ref 0 in
  let window = GWindow.dialog ~position:`CENTER ~modal:true ?parent ~type_hint:`DIALOG ~title () in
  let hbox = GPack.hbox ~border_width:15 ~packing:window#vbox#add () in
  let bbox = window#action_area in
  Option.iter (fun icon -> hbox#pack icon#coerce ~padding:4) icon;
  ignore (GMisc.label ~text:message ~packing:hbox#add ());
  (* the function called to create each button by iterating *)
  let rec iter_buttons pos = function
  | but_content :: others ->
      let label, stock =
        match but_content with
        | ButtonWithLabel label -> Some label, None
        | ButtonWithStock stock -> None, Some stock
      in
      let but = GButton.button ?label ?stock ~packing:(bbox#pack ~expand:true) () in
      ignore (but#connect#clicked ~callback:(fun () -> button_nb := pos; window#destroy ()));
      (* If it's the default button then give it the focus *)
      if pos = default then
        but#grab_default ();
      iter_buttons (pos + 1) others;
  | [] -> ()
  in
  iter_buttons 1 buttons;
  ignore (window#connect#destroy ~callback:GMain.Main.quit);
  window#set_position `CENTER;
  window#show ();
  GMain.Main.main ();
  !button_nb

let message_box ?parent ?icon ~title ?(ok = ButtonWithStock `OK) message =
  ignore (question_box ?parent ?icon ~title ~buttons:[ ok ] message)
