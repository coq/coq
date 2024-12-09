(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Preferences

(** A session is a script buffer + proof + messages,
    interacting with a rocqtop, and a few other elements around *)

class type ['a] page =
  object
    inherit GObj.widget
    method update : 'a -> unit
    method on_update : callback:('a -> unit) -> unit
    method data : 'a
  end

class type control =
  object
    method detach : unit -> unit
  end

type errpage = (int * string) list page
type jobpage = string CString.Map.t page
type breakpoint = {
  mark_id : string;
  mutable prev_byte_offset : int; (* UTF-8 byte offset for Rocq *)
  (* prev_uni_offset may differ from mark#offset as the script is edited *)
  mutable prev_uni_offset : int;  (* unicode offset for GTK *)
}

type session = {
  buffer : GText.buffer;
  script : Wg_ScriptView.script_view;
  proof : Wg_ProofView.proof_view;   (* the proof context panel *)
  messages : Wg_RoutedMessageViews.message_views_router;
  segment : Wg_Segment.segment; (* color coded status bar near bottom of the screen *)
  fileops : FileOps.ops;
  rocqops : RocqOps.ops;
  rocqtop : RocqDriver.rocqtop;
  command : Wg_Command.command_window; (* aka the Query Pane *)
  finder : Wg_Find.finder; (* Find / Replace panel *)
  debugger : Wg_Debugger.debugger_view;
  tab_label : GMisc.label;
  errpage : errpage;
  warnpage : errpage;
  jobpage : jobpage;
  sid : int;
  basename : string;
  mutable control : control;
  mutable abs_file_name : string option;
  mutable debug_stop_pt : (session * int * int) option;
  mutable breakpoints : breakpoint list;
  mutable last_db_goals : Pp.t
}

let next_sid = ref 0

let create_buffer () =
  let buffer = GSourceView3.source_buffer
    ~tag_table:Tags.Script.table
    ~highlight_matching_brackets:true
    ?language:(lang_manager#language source_language#get)
    ?style_scheme:(style_manager#style_scheme source_style#get)
    ()
  in
  let _ = buffer#create_mark ~name:"start_of_input" buffer#start_iter in
  let _ = buffer#create_mark
    ~left_gravity:false ~name:"stop_of_input" buffer#end_iter in
  let _ = buffer#create_mark ~name:"prev_insert" buffer#start_iter in
  let _ = buffer#place_cursor ~where:buffer#start_iter in
  let _ = buffer#add_selection_clipboard Ideutils.cb in
  buffer

let create_script rocqtop source_buffer =
  let script = Wg_ScriptView.script_view rocqtop ~source_buffer
    ~show_line_numbers:true ~wrap_mode:`NONE ()
    (* todo: line numbers don't appear *)
  in
  let _ = script#misc#set_name "ScriptWindow"
  in
  script

(** NB: Events during text edition:

    - [begin_user_action]
    - [insert_text] (or [delete_range] when deleting)
    - [changed]
    - [end_user_action]

   When pasting a text containing tags (e.g. the sentence terminators),
   there is actually many [insert_text] and [changed]. For instance,
   for "a. b.":

    - [begin_user_action]
    - [insert_text] (for "a")
    - [changed]
    - [insert_text] (for ".")
    - [changed]
    - [apply_tag] (for the tag of ".")
    - [insert_text] (for " b")
    - [changed]
    - [insert_text] (for ".")
    - [changed]
    - [apply_tag] (for the tag of ".")
    - [end_user_action]

  Since these copy-pasted tags may interact badly with the retag mechanism,
  we now don't monitor the "changed" event, but rather the "begin_user_action"
  and "end_user_action". We begin by setting a mark at the initial cursor
  point. At the end, the zone between the mark and the cursor is to be
  untagged and then retagged. *)

let misc () = CDebug.(get_flag misc)

type action_stack_entry = Mark of Gtk.text_mark | Begin

type action_stack = action_stack_entry list option

let call_rocq_or_cancel_action rocqtop rocqops (buffer : GText.buffer) it =
  let () = try buffer#delete_mark (`NAME "target") with GText.No_such_mark _ -> () in
  let mark = buffer#create_mark ~name:"target" it in
  let action = rocqops#go_to_mark (`MARK mark) in
  ignore @@ RocqDriver.try_grab rocqtop action (fun () -> ())

let init_user_action (stack : action_stack ref) = match !stack with
| None -> stack := Some []
| Some _ -> assert false

let close_user_action (stack : action_stack ref) = match !stack with
| None -> assert false
| Some marks ->
  let () = stack := None in
  marks

let handle_iter rocqtop rocqops (buffer : GText.buffer) it (stack : action_stack ref) =
  match it with
  | None -> ()
  | Some it ->
    match !stack with
    | Some marks ->
      (* We are inside an user action, deferring to its end *)
      let ent = if it#offset > 0 then Mark (buffer#create_mark it) else Begin in
      stack := Some (ent :: marks)
    | None ->
      (* Otherwise we move to the mark now *)
      call_rocq_or_cancel_action rocqtop rocqops buffer it

let set_buffer_handlers
  (buffer : GText.buffer) script (rocqops : RocqOps.ops) rocqtop
=
  let action_stack : action_stack ref = ref None in
  let get_start () = buffer#get_iter_at_mark (`NAME "start_of_input") in
  let get_stop () = buffer#get_iter_at_mark (`NAME "stop_of_input") in
  let ensure_marks_exist () =
    try ignore(buffer#get_mark (`NAME "stop_of_input"))
    with GText.No_such_mark _ -> assert false in
  let get_insert () = buffer#get_iter_at_mark `INSERT in
  let update_prev it =
    let prev = buffer#get_iter_at_mark (`NAME "prev_insert") in
    if it#offset < prev#offset then
      buffer#move_mark (`NAME "prev_insert") ~where:it
  in
  let debug_edit_zone () = if false (*!Minilib.debug*) then begin
    buffer#remove_tag Tags.Script.edit_zone
      ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#apply_tag Tags.Script.edit_zone
      ~start:(get_start()) ~stop:(get_stop())
    end in
  let processed_sentence_just_before_error it =
    let rec aux old it =
      if it#is_start then None
      else if it#has_tag Tags.Script.processed then Some old
      else if it#has_tag Tags.Script.error_bg then aux it it#backward_char
      else None in
    aux it it#copy in
  let insert_cb it s = if String.length s = 0 then () else begin
    if misc () then Minilib.log ("insert_cb " ^ string_of_int it#offset);
    let () = update_prev it in
    let iter =
      if it#has_tag Tags.Script.processed then Some it
      else if it#has_tag Tags.Script.error_bg then
        processed_sentence_just_before_error it
      else None
    in
    handle_iter rocqtop rocqops buffer iter action_stack
    end
  in
  let delete_cb ~start ~stop =
    if misc () then Minilib.log (Printf.sprintf "delete_cb %d %d" start#offset stop#offset);
    let min_iter, max_iter =
      if start#compare stop < 0 then start, stop else stop, start in
    let () = update_prev min_iter in
    let rec aux iter =
      if iter#equal max_iter then None
      else if iter#has_tag Tags.Script.processed then
        Some min_iter#backward_char
      else if iter#has_tag Tags.Script.error_bg then
        processed_sentence_just_before_error iter
      else aux iter#forward_char
    in
    let iter = aux min_iter in
    handle_iter rocqtop rocqops buffer iter action_stack
  in
  let begin_action_cb () =
    let () = if misc () then Minilib.log "begin_action_cb" in
    let () = init_user_action action_stack in
    let where = get_insert () in
    buffer#move_mark (`NAME "prev_insert") ~where
  in
  let end_action_cb () =
    let () = if misc () then Minilib.log "end_action_cb" in
    let marks = close_user_action action_stack in
    let () = ensure_marks_exist () in
    if CList.is_empty marks then
      let start, stop = get_start (), get_stop () in
      let () = List.iter (fun tag -> buffer#remove_tag tag ~start ~stop) Tags.Script.ephemere in
      Sentence.tag_on_insert buffer
    else
      (* If Rocq was asked to backtrack, the cleanup must be done by the
         backtrack_until function, since it may move the stop_of_input
         to a point indicated by RocqDriver. *)
      let iters = List.map (fun mark ->
          match mark with
          | Mark mark -> buffer#get_iter_at_mark (`MARK mark)
          | Begin -> buffer#start_iter
        ) marks in
      let iter = List.hd @@ List.sort (fun it1 it2 -> it1#compare it2) iters in
      let () = List.iter (fun mark ->
        try match mark with
        | Mark mark -> buffer#delete_mark (`MARK mark)
        | Begin -> let action = RocqDriver.seq (rocqops#backtrack_to_begin ())
                                (RocqDriver.lift (fun () -> Sentence.tag_on_insert buffer)) in
          ignore @@ RocqDriver.try_grab rocqtop action (fun () -> ())
        with GText.No_such_mark _ -> ()) marks in
      call_rocq_or_cancel_action rocqtop rocqops buffer iter
  in
  let mark_deleted_cb m =
    match GtkText.Mark.get_name m with
    | Some "insert" -> ()
    | Some s -> if misc () then Minilib.log (s^" deleted")
    | None -> ()
  in
  let mark_set_cb it m =
    debug_edit_zone ();
    let ins = get_insert () in
    let () = Ideutils.display_location ins in
    match GtkText.Mark.get_name m with
    | Some "insert" -> ()
    | Some s -> if misc () then Minilib.log (s^" moved")
    | None -> ()
  in
  let set_busy b =
    let prop = `EDITABLE b in
    let tags = [Tags.Script.processed] in
    List.iter (fun tag -> tag#set_property prop) tags
  in
  (* Pluging callbacks *)
  let () = RocqDriver.setup_script_editable rocqtop set_busy in
  let _ = buffer#connect#insert_text ~callback:insert_cb in
  let _ = buffer#connect#delete_range ~callback:delete_cb in
  let _ = buffer#connect#begin_user_action ~callback:begin_action_cb in
  let _ = buffer#connect#end_user_action ~callback:end_action_cb in
  let _ = buffer#connect#after#mark_set ~callback:mark_set_cb in
  let _ = buffer#connect#after#mark_deleted ~callback:mark_deleted_cb in
  ()

let find_int_col s l =
  match List.assoc s l with `IntC c -> c | _ -> assert false

let find_string_col s l =
  match List.assoc s l with `StringC c -> c | _ -> assert false

let make_table_widget ?sort cd cb =
  let frame = GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC () in
  let columns, store =
    let cols = new GTree.column_list in
    let columns = List.map (function
      | (`Int,n,_)    -> n, `IntC (cols#add Gobject.Data.int)
      | (`String,n,_) -> n, `StringC (cols#add Gobject.Data.string))
    cd in
    columns, GTree.list_store cols in
  let data = GTree.view
      ~vadjustment:frame#vadjustment ~hadjustment:frame#hadjustment
      ~rules_hint:true ~headers_visible:false
      ~model:store ~packing:frame#add () in
  let () = data#set_headers_visible true in
  let () = data#set_headers_clickable true in
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
  let make_sorting i (_, c) =
    let sort (store : GTree.model) it1 it2 = match c with
    | `IntC c ->
      compare (store#get ~row:it1 ~column:c) (store#get ~row:it2 ~column:c)
    | `StringC c ->
      compare (store#get ~row:it1 ~column:c) (store#get ~row:it2 ~column:c)
    in
    store#set_sort_func i sort
  in
  CList.iteri make_sorting columns;
  CList.iteri (fun i c -> c#set_sort_column_id i) cols;
  List.iter (fun c -> ignore(data#append_column c)) cols;
  ignore(
    data#connect#row_activated ~callback:(fun tp vc -> cb columns store tp vc)
  );
  let () = match sort with None -> () | Some (i, t) -> store#set_sort_column_id i t in
  frame, (fun f -> f columns store)

let create_errpage ~kind (script : Wg_ScriptView.script_view) : errpage =
  let table, access =
    make_table_widget ~sort:(0, `ASCENDING)
      [`Int,"Line",true; `String, kind, true]
      (fun columns store tp vc ->
        let row = store#get_iter tp in
        let lno = store#get ~row ~column:(find_int_col "Line" columns) in
        let where = script#buffer#get_iter (`LINE (lno-1)) in
        script#buffer#place_cursor ~where;
        script#misc#grab_focus ();
        ignore (script#scroll_to_iter
                  ~use_align:false ~yalign:0.75 ~within_margin:0.25 where)) in
  let tip = GMisc.label ~text:"Double click to jump to line" () in
  let box = GPack.vbox ~homogeneous:false () in
  let () = box#pack ~expand:true table#coerce in
  let () = box#pack ~expand:false ~padding:2 tip#coerce in
  let last_update = ref [] in
  let callback = ref (fun _ -> ()) in
  object (self)
    inherit GObj.widget box#as_widget
    method update errs =
      if !last_update = errs then ()
      else begin
        last_update := errs;
        access (fun _ store -> store#clear ());
        !callback errs;
        List.iter (fun (lno, msg) -> access (fun columns store ->
          let line = store#append () in
          store#set ~row:line ~column:(find_int_col "Line" columns) lno;
          store#set ~row:line ~column:(find_string_col kind columns) msg))
          errs
      end
    method on_update ~callback:cb = callback := cb
    method data = !last_update
  end

let create_jobpage rocqtop rocqops : jobpage =
  let table, access =
    make_table_widget ~sort:(0, `ASCENDING)
      [`String,"Worker",true; `String,"Job name",true]
      (fun columns store tp vc ->
        let row = store#get_iter tp in
        let w = store#get ~row ~column:(find_string_col "Worker" columns) in
        let info () = Minilib.log ("Rocq busy, discarding query") in
        ignore @@ RocqDriver.try_grab rocqtop (rocqops#stop_worker w) info
      ) in
  let tip = GMisc.label ~text:"Double click to interrupt worker" () in
  let box = GPack.vbox ~homogeneous:false () in
  let () = box#pack ~expand:true table#coerce in
  let () = box#pack ~expand:false ~padding:2 tip#coerce in
  let last_update = ref CString.Map.empty in
  let callback = ref (fun _ -> ()) in
  object (self)
    inherit GObj.widget box#as_widget
    method update jobs =
      if !last_update = jobs then ()
      else begin
        last_update := jobs;
        access (fun _ store -> store#clear ());
        !callback jobs;
        CString.Map.iter (fun id job -> access (fun columns store ->
          let column = find_string_col "Worker" columns in
          if job = "Dead" then
            store#foreach (fun _ row ->
              if store#get ~row ~column = id then store#remove row || true
              else false)
          else
            let line = store#append () in
            store#set ~row:line ~column id;
            store#set ~row:line ~column:(find_string_col "Job name" columns) job))
          jobs
      end
    method on_update ~callback:cb = callback := cb
    method data = !last_update
  end

let create_proof () =
  let proof = Wg_ProofView.proof_view () in
  let _ = proof#misc#set_can_focus true in
  let _ = GtkBase.Widget.add_events proof#as_widget
    [`ENTER_NOTIFY;`POINTER_MOTION]
  in
  proof

let dummy_control : control =
  object
    method detach () = ()
  end

let to_abs_file_name f =
  if Filename.is_relative f then Filename.concat (Unix.getcwd ()) f else f

let create file rocqtop_args =
  let (basename, abs_file_name) = match file with
    | None -> ("*scratch*", None)
    | Some f -> (Glib.Convert.filename_to_utf8 Filename.(remove_extension (basename f)),
        Some (to_abs_file_name f))
  in
  let rocqtop = RocqDriver.spawn_rocqtop basename rocqtop_args in
  let reset () = RocqDriver.reset_rocqtop rocqtop in
  let buffer = create_buffer () in
  let script = create_script rocqtop buffer in
  let proof = create_proof () in
  incr next_sid;
  let sid = !next_sid in
  let create_messages () =
    let messages = Wg_MessageView.message_view sid in
    let _ = messages#misc#set_can_focus true in
    Wg_RoutedMessageViews.message_views ~route_0:messages
  in
  let messages = create_messages () in
  let segment = new Wg_Segment.segment () in
  let finder = new Wg_Find.finder basename (script :> GText.view) in
  let debugger = Wg_Debugger.debugger (Printf.sprintf "Debugger (%s)" basename) sid in
  let fops = new FileOps.fileops (buffer :> GText.buffer) file reset in
  let _ = fops#update_stats in
  let rops =
    new RocqOps.rocqops script proof messages segment rocqtop (fun () -> fops#filename) in
  let command = new Wg_Command.command_window basename rocqtop rops messages sid in
  let errpage = create_errpage ~kind:"Error" script in
  let warnpage = create_errpage ~kind:"Warning" script in
  let jobpage = create_jobpage rocqtop rops in
  let _ = set_buffer_handlers (buffer :> GText.buffer) script rops rocqtop in
  let _ = RocqDriver.set_reset_handler rocqtop rops#handle_reset_initial in
  let _ = RocqDriver.init_rocqtop rocqtop rops#initialize in
  let tab_label = GMisc.label ~text:basename () in
(*  todo: ugly custom tooltips...*)
(*
  tab_label#misc#set_size_request ~height:100 ~width:200 ();
  tab_label#misc#modify_bg [`NORMAL, `NAME "#FF0000"];
  (match abs_file_name with
  | Some f ->
    GtkBase.Widget.Tooltip.set_markup tab_label#as_widget
      ("<span background=\"yellow\" foreground=\"black\">" ^ f ^ "</span>");
    let label2 = GMisc.label ~text:"hello?" () in
    GtkBase.Tooltip.set_custom (label2#coerce : Gtk.tooltip) label
  | None -> ());
*)
  {
    buffer = (buffer :> GText.buffer);
    script=script;
    proof=proof;
    messages=messages;
    segment=segment;
    fileops=fops;
    rocqops=rops;
    rocqtop=rocqtop;
    command=command;
    finder=finder;
    debugger=debugger;
    tab_label= tab_label;
    errpage;
    warnpage;
    jobpage=jobpage;
    sid=sid;
    basename = basename;
    control = dummy_control;
    abs_file_name = abs_file_name;
    debug_stop_pt = None;
    breakpoints = [];
    last_db_goals = Pp.mt ()
  }

let kill (sn:session) =
  (* To close the detached views of this script, we call manually
     [destroy] on it, triggering some callbacks in [detach_view].
     In a more modern lablgtk, rather use the page-removed signal ? *)
  sn.rocqops#destroy ();
  sn.script#destroy ();
  RocqDriver.close_rocqtop sn.rocqtop

let window_size = ref (window_width#get, window_height#get)

let build_layout (sn:session) =
  let debugger_paned = GPack.paned `VERTICAL () in
  let debugger_box =
    GPack.vbox ~packing:(debugger_paned#pack2 ~shrink:false ~resize:true) ()
  in

  let session_paned = GPack.paned `VERTICAL
    ~packing:(debugger_paned#pack1 ~shrink:false ~resize:true) () in
  let session_box =
    GPack.vbox ~packing:(session_paned#pack1 ~shrink:false ~resize:true) ()
  in

  (* Left part of the window. *)

  let eval_paned = GPack.paned `HORIZONTAL ~border_width:5
    ~packing:(session_box#pack ~expand:true) () in
  let script_frame = GBin.frame ~shadow_type:`IN
    ~packing:(eval_paned#pack1 ~shrink:false) () in
  let script_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:script_frame#add () in

  (* Right part of the window *)

  let state_paned = GPack.paned `VERTICAL
    ~packing:(eval_paned#pack2 ~shrink:true) () in

  (* Proof buffer. *)

  let title = Printf.sprintf "Proof (%s)" sn.tab_label#text in
  let proof_detachable = Wg_Detachable.detachable ~title () in
  let () = proof_detachable#button#misc#hide () in
  let () = proof_detachable#frame#set_shadow_type `IN in
  let () = state_paned#pack1 ~shrink:true proof_detachable#coerce in
  let proof_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:proof_detachable#pack () in
  let callback _ = proof_detachable#show;
                   proof_scroll#coerce#misc#set_size_request ~width:0 ~height:0 ()
  in
  let () = proof_detachable#connect#attached ~callback in
  let callback _ =
    proof_scroll#coerce#misc#set_size_request ~width:500 ~height:400 ()
  in
  let () = proof_detachable#connect#detached ~callback in

  (* Message buffer. *)

  let message_frame = GPack.notebook ~packing:(state_paned#pack2 ~shrink:true) () in
  let add_msg_page pos name text (w : GObj.widget) =
    let detachable =
      Wg_Detachable.detachable ~title:(text^" ("^name^")") () in
    detachable#add w#coerce;
    let label = GPack.hbox ~spacing:5 () in
    let lbl = GMisc.label ~text ~packing:label#add () in
    let but = GButton.button () in
    but#add (GMisc.label ~markup:"<small>↗</small>" ())#coerce;
    label#add but#coerce;
    ignore(message_frame#insert_page ~pos
      ~tab_label:label#coerce detachable#coerce);
    ignore(but#connect#clicked ~callback:(fun _ ->
      message_frame#remove_page (message_frame#page_num detachable#coerce);
      detachable#button#clicked ()));
    detachable#connect#detached ~callback:(fun _ ->
      if message_frame#all_children = [] then message_frame#misc#hide ();
      w#misc#set_size_request  ~width:500 ~height:400 ());
    detachable#connect#attached ~callback:(fun _ ->
      w#misc#set_size_request  ~width:1 ~height:1 (); (* force resize *)
      ignore(message_frame#insert_page ~pos
        ~tab_label:label#coerce detachable#coerce);
      message_frame#misc#show ();
      detachable#show);
    detachable#button#misc#hide ();
    detachable, lbl in
  let session_tab = GPack.hbox ~homogeneous:false () in
  let img = GMisc.image ~icon_size:`SMALL_TOOLBAR
    ~packing:session_tab#pack () in
  let _ =
    sn.buffer#connect#modified_changed
      ~callback:(fun () -> if sn.buffer#modified
        then img#set_stock `SAVE
        else img#set_stock `YES) in
  (* There was an issue in the previous implementation for setting the
     position of the handle. It was using the size_allocate event but
     there is an issue with size_allocate. G. Melquiond analyzed that
     at starting time, the size_allocate event is only issued in
     Layout phase of the gtk loop so that it is actually processed
     only in the next iteration of the event-update-layout-paint loop,
     after the user does something and trigger an effective new event
     (see #10578). So we preventively enforce an estimated position
     for the handles to be used in the very first initializing
     iteration of the loop *)
  let () =
    (* 14 is the estimated size for vertical borders *)
    let estimated_vertical_handle_position = (fst !window_size - 14) / 2 in
    (* 169 is the estimated size for menus, command line, horizontal border *)
    let estimated_horizontal_handle_position = (snd !window_size - 169) / 2 in
    if estimated_vertical_handle_position > 0 then
      eval_paned#set_position estimated_vertical_handle_position;
    if estimated_horizontal_handle_position > 0 then
      state_paned#set_position estimated_horizontal_handle_position in
  session_box#pack sn.finder#coerce;
  debugger_box#add sn.debugger#coerce;
  sn.debugger#hide ();
  (sn.messages#route 0)#set_forward_show_debugger sn.debugger#show;
  sn.debugger#set_forward_paned_pos (fun pos -> debugger_paned#set_position pos);
  (* segment should not be in the debugger box *)
  debugger_box#pack ~expand:false ~fill:false sn.segment#coerce;
  debugger_paned#set_position 1000000;
  sn.command#pack_in (session_paned#pack2 ~shrink:false ~resize:false);
  script_scroll#add sn.script#coerce;
  proof_scroll#add sn.proof#coerce;
  let detach, _ = add_msg_page 0 sn.tab_label#text "Messages" sn.messages#default_route#coerce in
  let _, errlabel = add_msg_page 1 sn.tab_label#text "Errors" sn.errpage#coerce in
  let _, warnlabel = add_msg_page 2 sn.tab_label#text "Warnings" sn.warnpage#coerce in
  let _, _ = add_msg_page 3 sn.tab_label#text "Jobs" sn.jobpage#coerce in
  (* When a message is received, focus on the message pane *)
  let _ =
    sn.messages#default_route#connect#pushed ~callback:(fun _ _ ->
      let num = message_frame#page_num detach#coerce in
      if 0 <= num then message_frame#goto_page num
    )
  in
  let set_label_color_on_update color page label =
    let txt = label#text in
    let red s = Printf.sprintf "<span foreground=\"%s\">%s</span>" color s in
    page#on_update ~callback:(fun l ->
      if l = [] then (label#set_use_markup false; label#set_text txt)
      else (label#set_text (red txt);label#set_use_markup true));
  in
  (* When an error occurs, paint the error label in red *)
  let () = set_label_color_on_update "#FF0000" sn.errpage errlabel in
  (* When a warning occurs, paint the warning label in orange *)
  let () = set_label_color_on_update "#FFA500" sn.warnpage warnlabel in
  session_tab#pack sn.tab_label#coerce;
  img#set_stock `YES;
  let control =
    object
      method detach () = proof_detachable#detach ()
    end
  in
  let () = sn.control <- control in
  (Some session_tab#coerce,None,debugger_paned#coerce)
