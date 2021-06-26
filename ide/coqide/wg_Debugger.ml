(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type stack_t = (string * (string * int list) option) list

class type debugger_view =
  object
    method coerce : GObj.widget
    method set_stack : stack_t -> unit
    method hide : unit -> unit
    method show : unit -> unit
    method set_forward_highlight_code : (string * int * int -> unit) -> unit
  end

let debugger () =
  let stack_widget = GText.view ~editable:false ~cursor_visible:false ~wrap_mode:`NONE () in
  let stack_buffer = stack_widget#buffer in
  let stack = ref [] in

  let debugger_detachable = Wg_Detachable.detachable ~title:"Debugger" () in
  let vb = GPack.vbox ~packing:(debugger_detachable#pack ~expand:true (*~fill:true*)) () in
  let _ = GMisc.label ~text:"Call Stack" ~xalign:0.02 (* todo: use padding instead of xalign *)
    ~packing:(vb#pack ~expand:false ~fill:true ~padding:3) () in
(*      should be resizable*)
(*      does ~expand do anything?*)
  let stack_scroll = GBin.scrolled_window (*~height:125*)
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(vb#pack ~expand:true) () in

  stack_scroll#add stack_widget#coerce;

  (* todo: makes widget not resizable *)
  (* unit is 1/100 inch *)
(*
  debugger_detachable#misc#set_size_request ~height:125 ();
  let _ = GMisc.label ~text:"Variables" ~xalign:1.0
    ~packing:(hb#pack ~expand:false ~fill:true ~padding:3) () in
*)
  (* todo: should be detachable or not? *)
  let callback _ = debugger_detachable#show;
                   debugger_detachable#coerce#misc#set_size_request ~width:0 ~height:0 ()
  in
  let () = debugger_detachable#connect#attached ~callback in

  let callback _ =
    let open Gtk in
    let open GtkBase in
    let alloc = Widget.allocation debugger_detachable#as_widget in
    debugger_detachable#frame#coerce#misc#set_size_request ~width:(alloc.width/2) ~height:alloc.height ()
  in
  let () = debugger_detachable#connect#detached ~callback in

  let highlighted_line = ref None in
  let forward_highlight_code = ref ((fun x -> failwith "forward_highlight_code")
    : (string * int * int) -> unit) in

  (* todo: better to share with Tags.Script.debugging, but it isn't set for GText *)
  let debugging_tag = stack_buffer#create_tag
    [ `BACKGROUND_SET true; `BACKGROUND Preferences.db_stopping_point_color#get;
      `FOREGROUND_SET true; `FOREGROUND "white"] in

  let clear_highlight () =
    let start = stack_buffer#get_iter `START in
    let stop = stack_buffer#get_iter `END in
    stack_buffer#remove_tag debugging_tag ~start ~stop;
    highlighted_line := None
  in

  let highlight line =
    if line < List.length !stack then begin
      let start = stack_buffer#get_iter_at_char ~line 0 in
      let stop = stack_buffer#get_iter_at_char ~line:(line+1) 0 in
      stack_buffer#apply_tag debugging_tag ~start ~stop;
      highlighted_line := Some line;
      let (_, loc) = List.nth !stack line in
      match loc with
      | Some (file, bp :: ep :: _) ->
        !forward_highlight_code (file, bp, ep)
      (* todo: show not-found dialog instead? *)
      | _ -> failwith "wg_debugger.highlight: stack entry without location"
    end
  in

  let (up, _) = GtkData.AccelGroup.parse "Up" in
  let (down, _) = GtkData.AccelGroup.parse "Down" in

  (* Keypress handler *)
  let keypress_cb ev =
    let move dir =
      match !highlighted_line with
      | Some l ->
        let line = l+dir in
        if line >= 0 && line < List.length !stack then
          (clear_highlight (); highlight line)
      | None -> ()
    in

    let ev_key = GdkEvent.Key.keyval ev in
    if ev_key = up then
      (move (-1); true)
    else if ev_key = down then
      (move 1; true)
    else
      false
  in
  let _ = stack_widget#event#connect#key_press ~callback:keypress_cb in

  (* click handler *)
  let click_cb ev =
    let open GdkEvent.Button in
    let y = y ev in
    let button = button ev in
    let metrics = stack_widget#coerce#misc#pango_context#get_metrics () in
    let line_height = GPango.to_pixels (metrics#ascent+metrics#descent) in
    let line = (truncate y)/line_height in
    if button = 1 && line < List.length !stack then
      (clear_highlight (); highlight line);
    false (* let the panel get the focus *)
  in
  let _ = stack_widget#event#connect#button_press ~callback:click_cb in

  let debugger = object (self)

    method coerce = debugger_detachable#coerce
    method set_stack (stack_v : stack_t) =
      stack := stack_v;
      stack_buffer#set_text
        (String.concat "\n" (List.map (fun i -> let (tacn, loc) = i in tacn) stack_v));
      clear_highlight ();
      if stack_v <> [] then
        highlight 0

    method hide () = debugger_detachable#hide  (* todo: give up focus *)
    method show () = debugger_detachable#show  (* todo: take focus? *)
    method set_forward_highlight_code f = forward_highlight_code := f
  end
  in
  debugger
