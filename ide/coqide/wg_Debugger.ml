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
type vars_t = (string * Pp.t) list

class type debugger_view =
  object
    method coerce : GObj.widget
    method set_stack : stack_t -> unit
    method set_vars : vars_t -> unit
    method hide : unit -> unit
    method show : unit -> unit
    method set_forward_highlight_code : (string * int * int -> unit) -> unit
    method set_forward_db_vars : (int -> unit) -> unit
    method set_forward_paned_pos : (int -> unit) -> unit
  end

let forward_keystroke = ref ((fun x -> failwith "forward_keystroke (db)")
    : Gdk.keysym * Gdk.Tags.modifier list -> bool)

let debugger title =
  let forward_set_paned_pos = ref ((fun x -> failwith "forward_set_paned_pos")
    : int -> unit) in

  let debugger_detachable = Wg_Detachable.detachable ~title () in
  debugger_detachable#close_button#misc#show ();
  ignore(debugger_detachable#close_button#connect#clicked
    ~callback:(fun _ -> !forward_set_paned_pos 1000000));

  let paned = GPack.paned `HORIZONTAL ~packing:(debugger_detachable#pack ~expand:true) () in

  let stack_view = GText.view ~editable:false ~cursor_visible:false ~wrap_mode:`NONE () in
  let stack_buffer = stack_view#buffer in
  let stack = ref [] in

  let vb_stack = GPack.vbox ~packing:(paned#pack1 ~shrink:false ~resize:true) () in
  let _ = GMisc.label ~text:"Call Stack" ~xalign:0.02 (* todo: use padding instead of xalign *)
    ~packing:(vb_stack#pack ~expand:false ~fill:true ~padding:3) () in
  let stack_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(vb_stack#pack ~expand:true) () in
  stack_scroll#add stack_view#coerce;

  let vars_view = GText.view ~editable:false ~cursor_visible:false ~wrap_mode:`NONE () in
  let cb view ft = view#misc#modify_font (GPango.font_description_from_string ft) in
  Preferences.(stick text_font vars_view (cb vars_view));
  Preferences.(stick text_font stack_view (cb stack_view));

  let vars_buffer = vars_view#buffer in
  let vars = ref [] in

  let vb_vars = GPack.vbox ~packing:(paned#pack2 ~shrink:false ~resize:true) () in
  let _ = GMisc.label ~text:"Variables" ~xalign:0.02 (* todo: use padding instead of xalign *)
    ~packing:(vb_vars#pack ~expand:false ~fill:true ~padding:3) () in
  let vars_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(vb_vars#pack ~expand:true) () in
  vars_scroll#add vars_view#coerce;

(* doesn't help, not getting the correct widths
  ignore @@ Glib.Idle.add (fun _ ->
    let open Gtk in
    let open GtkBase in
    let dwidth = (Widget.allocation debugger_detachable#as_widget).width in
    let bwidth = (Widget.allocation debugger_detachable#close_button#as_widget).width in
    Printf.printf "dwidth = %d bwidth = %d\n%!" dwidth bwidth;
    paned #set_position (dwidth/2 - bwidth);
    false);
*)

  let highlighted_line = ref None in
  let forward_highlight_code = ref ((fun x -> failwith "forward_highlight_code")
    : (string * int * int) -> unit) in
  let forward_db_vars = ref ((fun x -> failwith "forward_db_vars")
    : int -> unit) in

  (* workaround *)
  let relayout () =
    paned#remove vb_stack#coerce; (* appears not to be destroyed *)
    paned#remove vb_vars#coerce;
    paned#pack1 ~shrink:false ~resize:true vb_stack#coerce;
    paned#pack2 ~shrink:false ~resize:true vb_vars#coerce;
  in

  let attach_cb _ =
    debugger_detachable#show;
    relayout ()
  in
  let () = debugger_detachable#connect#attached ~callback:attach_cb in

  let detach_cb _ =
    let open Gtk in
    let open GtkBase in
    let alloc = Widget.allocation debugger_detachable#as_widget in
    debugger_detachable#frame#coerce#misc#set_size_request ~width:alloc.width ~height:alloc.height ();
    relayout ();
    !forward_set_paned_pos 1000000;  (* looks OK but debugger_paned in main window is still resizable *)
  in
  let () = debugger_detachable#connect#detached ~callback:detach_cb in

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
      !forward_db_vars line;
      match loc with
      | Some (file, bp :: ep :: _) ->
        !forward_highlight_code (file, bp, ep)
      | _ -> ()  (* e.g. for simple tactic call *)
    end
  in

  let up = GtkData.AccelGroup.parse "Up" in
  let down = GtkData.AccelGroup.parse "Down" in

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

    let key_ev = Ideutils.filter_key ev in
    if key_ev = up then
      (move (-1); true)
    else if key_ev = down then
      (move 1; true)
    else if !forward_keystroke key_ev then
      true (* support some function keys when Debugger is detached *)
    else
      false
  in
  let _ = stack_view#event#connect#key_press ~callback:keypress_cb in

  (* click handler *)
  let click_cb ev =
    let open GdkEvent.Button in
    let y = y ev in
    let button = button ev in
    let metrics = stack_view#coerce#misc#pango_context#get_metrics () in
    let line_height = GPango.to_pixels (metrics#ascent+metrics#descent) in
    let line = (truncate y)/line_height in
    if button = 1 && line < List.length !stack then
      (clear_highlight (); highlight line);
    false (* let the panel get the focus *)
  in
  let _ = stack_view#event#connect#button_press ~callback:click_cb in

  let debugger = object (self)

    method coerce = debugger_detachable#coerce
    method set_stack (stack_v : stack_t) =
      stack := stack_v;
      stack_buffer#set_text
        (String.concat "\n" (List.map (fun i -> let (tacn, loc) = i in tacn) stack_v));
      clear_highlight ();
      if stack_v <> [] then
        highlight 0

    method set_vars (vars_v : vars_t) =
      vars := vars_v;
      vars_buffer#set_text "";
      let cwidth () =
        let open Gtk in
        let open GtkBase in
        (* window width less paned position *)
        let pixel_width = (Widget.allocation debugger_detachable#as_widget).width - paned#position in
        let metrics = vars_view#misc#pango_context#get_metrics ()  in
        let char_width = GPango.to_pixels metrics#approx_char_width in
        pixel_width / char_width
      in
      let width = cwidth () in
      let insert_xml msg =
        Ideutils.insert_xml vars_buffer (Richpp.richpp_of_pp width msg);
      in
      List.iter (fun (n, value) ->
          insert_xml Pp.(str n ++ str " =" ++ (spc()) ++ value ++ (fnl()))
        ) vars_v;
      ()

    method hide () = debugger_detachable#hide  (* todo: give up focus *)
    method show () = debugger_detachable#show  (* todo: take focus? *)
    method set_forward_highlight_code f = forward_highlight_code := f
    method set_forward_db_vars f = forward_db_vars := f
    method set_forward_paned_pos f = forward_set_paned_pos := f
  end
  in
  debugger
