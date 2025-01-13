(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
    method set_forward_clear_db_highlight : (unit -> unit) -> unit
    method set_forward_db_vars : (int -> unit) -> unit
    method set_forward_paned_pos : (int -> unit) -> unit
    method set_forward_get_basename : (unit -> string) -> unit
    method select_all : unit -> unit
  end

let forward_keystroke = ref ((fun x -> failwith "forward_keystroke (db)")
    : Gdk.keysym * Gdk.Tags.modifier list -> int -> bool)

let find_string_col s l =
  match List.assoc s l with `StringC c -> c | _ -> assert false

let make_table_widget cd cb =
  let frame = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC () in
  let columns, store =
    let cols = new GTree.column_list in
    let columns = List.map (function
      | (`Int,n,_)    -> n, `IntC (cols#add Gobject.Data.int)
      | (`String,n,_) -> n, `StringC (cols#add Gobject.Data.string))
    cd in
    columns, GTree.tree_store cols in
  let data = GTree.view  (* todo: call "view" *)
      ~vadjustment:frame#vadjustment ~hadjustment:frame#hadjustment
      ~rules_hint:true ~headers_visible:false
      ~model:store ~packing:frame#add () in

  let selection = data#selection in
  selection#set_mode `MULTIPLE;
  let copy = GtkData.AccelGroup.parse "<Ctrl>C" in

  let vars_keypress_cb ev =
    let key_ev = Ideutils.filter_key ev in
    if key_ev = copy then begin
      let rows = selection#get_selected_rows in
      let get_value iter = store#get ~row:iter ~column:(find_string_col "Var" columns) in
      let buf = Buffer.create 100 in
      List.iter (fun row ->
          let iter = store#get_iter row in
          let depth = store#iter_depth iter in
          let top_iter = Option.default iter (store#iter_parent iter) in
          if depth = 0 || not (selection#iter_is_selected top_iter) then begin
            let value =
              if store#iter_has_child top_iter then
                (get_value top_iter) ^ "\n" ^
                (get_value (store#iter_children (Some top_iter)))
              else
                get_value top_iter
            in
            Buffer.add_string buf (value ^ "\n\n");
          end
        ) rows;
      (GData.clipboard Gdk.Atom.clipboard)#set_text (Buffer.contents buf);
      true
    end else
      false
  in
  let _ = data#event#connect#key_press ~callback:vars_keypress_cb in

(* FIXME: handle this using CSS *)
(*   let refresh clr = data#misc#modify_bg [`NORMAL, `NAME clr] in *)
(*   let _ = background_color#connect#changed ~callback:refresh in *)
(*   let _ = data#misc#connect#realize ~callback:(fun () -> refresh background_color#get) in *)
  let mk_rend c = GTree.cell_renderer_text [], ["text",c] in
  let cols =
    List.map2 (fun (_,c) (_,n,v) ->
      let c = match c with
        | `IntC c -> GTree.view_column ~renderer:(mk_rend c) ()
        | `StringC c -> GTree.view_column ~renderer:(mk_rend c) () in
      c#set_title n;
      c#set_visible v;
      c#set_sizing `AUTOSIZE;
      c)
    columns cd in
  List.iter (fun c -> ignore(data#append_column c)) cols;
  ignore @@ data#connect#row_activated ~callback:(fun tp vc -> cb columns store tp vc);
  let cb view ft = view#misc#modify_font (GPango.font_description_from_string ft) in
  Preferences.(stick text_font data (cb data));
  frame, (fun f -> f columns store), store

let debugger title sid =
  let forward_set_paned_pos = ref ((fun x -> failwith "forward_set_paned_pos")
    : int -> unit) in

  let forward_get_basename = ref ((fun x -> failwith "forward_get_basename")
    : unit -> string) in

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

  let tree, access, store =
    make_table_widget
      [`String, "Var", true]
      (fun columns store tp vc ->
        let row = store#get_iter tp in
        let _ = store#get ~row ~column:(find_string_col "Var" columns) in ()) in

  let vars_view = GText.view ~editable:false ~cursor_visible:false ~wrap_mode:`NONE () in
  let cb view ft = view#misc#modify_font (GPango.font_description_from_string ft) in
  Preferences.(stick text_font vars_view (cb vars_view));
  Preferences.(stick text_font stack_view (cb stack_view));

  let vars = ref [] in

  let vb_vars = GPack.vbox ~packing:(paned#pack2 ~shrink:false ~resize:true) () in
  let _ = GMisc.label ~text:"Variables" ~xalign:0.02 (* todo: use padding instead of xalign *)
    ~packing:(vb_vars#pack ~expand:false ~fill:true ~padding:3) () in
  let () = vb_vars#pack ~expand:true tree#coerce in

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
  let forward_clear_db_highlight = ref ((fun x -> failwith "forward_clear_db_highlight")
    : unit -> unit) in
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
    ignore @@ Glib.Idle.add (fun _ ->
      debugger_detachable#win#resize ~width:alloc.width ~height:alloc.height;
      false);
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
      let start = stack_buffer#get_iter (`LINE line) in
      let stop = stack_buffer#get_iter (`LINE (line+1)) in
      stack_buffer#apply_tag debugging_tag ~start ~stop;
      highlighted_line := Some line;
      let (_, loc) = List.nth !stack line in
      !forward_db_vars line;
      match loc with
      | Some (file, bp :: ep :: _) ->
        !forward_highlight_code (file, bp, ep)
      | _ -> !forward_clear_db_highlight ()  (* e.g. for simple tactic call *)
    end
  in

  let up = GtkData.AccelGroup.parse "Up" in
  let down = GtkData.AccelGroup.parse "Down" in

  let stack_keypress_cb ev =
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
    else
      !forward_keystroke key_ev sid (* support some function keys when Debugger is detached *)
  in
  let _ = stack_view#event#connect#key_press ~callback:stack_keypress_cb in

  let keypress_cb2 ev =
    let key_ev = Ideutils.filter_key ev in
    !forward_keystroke key_ev sid (* support some function keys when Debugger is detached *)
  in
  let _ = paned#event#connect#key_press ~callback:keypress_cb2 in

  (* click handler *)
  let click_cb ev =
    let open GdkEvent.Button in
    let y = y ev in
    let button = button ev in
    let scroll_pos = stack_scroll#vadjustment#value in
    let metrics = stack_view#coerce#misc#pango_context#get_metrics () in
    let line_height = GPango.to_pixels (metrics#ascent+metrics#descent) in
    let line = (truncate (y +. scroll_pos))/line_height in
    if button = 1 && line < List.length !stack then
      (clear_highlight (); highlight line);
    false (* let the panel get the focus *)
  in
  let _ = stack_view#event#connect#button_press ~callback:click_cb in

  let debugger = object (self)

    method coerce = debugger_detachable#coerce
    method set_stack (stack_v : stack_t) =
      stack := if stack_v = [] then [] else begin
        (* adjust text in the bottom frame of the stack *)
        let rs = List.rev stack_v in
        let (text, loc) = List.hd rs in
        match loc with
          | Some (_, locs) ->
            let basename = !forward_get_basename () in
            let basename = if basename = "*scratch*" then "Top" else basename in
            let s = Printf.sprintf "%s, %s" text basename in
            List.rev ((s, loc) :: (List.tl rs))
          | _ -> stack_v
      end;
      stack_buffer#set_text
        (String.concat "\n" (List.map (fun i -> let (tacn, loc) = i in tacn) !stack));
      clear_highlight ();
      if !stack <> [] then
        highlight 0

    method set_vars (vars_v : vars_t) =
      (* workaround: zero entries may show stale data GTK! :-( *)
      vars := if vars_v = [] then [("", Pp.mt ())] else vars_v;
      store#clear ();
      let cwidth () =
        let open Gtk in
        let open GtkBase in
        let pixel_width = (Widget.allocation tree#as_widget).width in
        let metrics = vars_view#misc#pango_context#get_metrics ()  in
        let char_width = GPango.to_pixels metrics#approx_char_width in
        (pixel_width - 100) / char_width
      in
      let print_pp width pp =
        let pp_buffer = Buffer.create 180 in
        let open Format in
        let ft = formatter_of_buffer pp_buffer in
        pp_set_margin ft width;
        pp_set_max_indent ft width;
      (*  pp_set_max_boxes ft 50 ;*)
      (*  pp_set_ellipsis_text ft "..."*)
        Pp.pp_with ft pp;
        pp_print_flush ft ();
        Buffer.contents pp_buffer
      in
      let show width =
        let insert = store#get_iter_first = None in
        let path = GtkTree.TreePath.from_string "0" in
        List.iter (fun (name, value) ->
            let width = max width 30 in
            let value = print_pp width value in
            access (fun columns store ->
                let column = (find_string_col "Var" columns) in
                let row = if insert then store#append () else store#get_iter path in
                GtkTree.TreePath.next path;
                if String.length value < width && (not (String.contains value '\n')) then begin
                  let text = if name = "" then " " else (name ^ " = " ^ value) in
                  store#set ~row ~column text;
                  if store#iter_has_child row then
                    ignore @@ store#remove (store#iter_children (Some row));
                end else begin
                  store#set ~row ~column (name ^ " = ");
                  let row2 = if insert || (not (store#iter_has_child row)) then
                    store#append ~parent:row ()
                  else
                    store#iter_children (Some row) in
                  store#set ~row:row2 ~column:(find_string_col "Var" columns) value
                end
              )
          ) !vars
      in
      let width = cwidth () in
      let pwidth = ref width in (* initially negative if not allocated *)
      if paned#position > 0 then show width;

      let w_cb (_ : Gtk.rectangle) =
        let width = cwidth () in
        if width <> !pwidth then begin
          pwidth := width;
          show width
        end
      in
      ignore (paned#misc#connect#size_allocate ~callback:w_cb)

    method hide () = debugger_detachable#hide  (* todo: give up focus *)
    method show () = debugger_detachable#show  (* todo: take focus? *)
    method set_forward_highlight_code f = forward_highlight_code := f
    method set_forward_clear_db_highlight f = forward_clear_db_highlight := f
    method set_forward_db_vars f = forward_db_vars := f
    method set_forward_paned_pos f = forward_set_paned_pos := f
    method set_forward_get_basename f = forward_get_basename := f

    method select_all () =
      if stack_view#is_focus then
        stack_buffer#select_range stack_buffer#start_iter stack_buffer#end_iter
  end
  in
  debugger
