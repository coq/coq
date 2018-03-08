(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Preferences

(** A session is a script buffer + proof + messages,
    interacting with a coqtop, and a few other elements around *)

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

type session = {
  buffer : GText.buffer;
  script : Wg_ScriptView.script_view;
  proof : Wg_ProofView.proof_view;
  messages : Wg_RoutedMessageViews.message_views_router;
  segment : Wg_Segment.segment;
  fileops : FileOps.ops;
  coqops : CoqOps.ops;
  coqtop : Coq.coqtop;
  command : Wg_Command.command_window;
  finder : Wg_Find.finder;
  tab_label : GMisc.label;
  errpage : errpage;
  jobpage : jobpage;
  mutable control : control;
}

let create_buffer () =
  let buffer = GSourceView2.source_buffer
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

let create_script coqtop source_buffer =
  let script = Wg_ScriptView.script_view coqtop ~source_buffer
    ~show_line_numbers:true ~wrap_mode:`NONE ()
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

let set_buffer_handlers
  (buffer : GText.buffer) script (coqops : CoqOps.ops) coqtop
=
  let action_was_cancelled = ref true in
  let no_coq_action_required = ref true in
  let cur_action = ref 0 in
  let new_action_id =
    let id = ref 0 in
    fun () -> incr id; !id in
  let running_action = ref None in
  let cancel_signal ?(stop_emit=true) reason =
    Minilib.log ("user_action cancelled: "^reason);
    action_was_cancelled := true;
    if stop_emit then GtkSignal.stop_emit () in
  let del_mark () =
    try buffer#delete_mark (`NAME "target")
    with GText.No_such_mark _ -> () in
  let add_mark it = del_mark (); buffer#create_mark ~name:"target" it in
  let call_coq_or_cancel_action f =
    no_coq_action_required := false;
    let action = !cur_action in
    let action, fallback =
      Coq.seq (Coq.lift (fun () -> running_action := Some action)) f,
      fun () -> (* If Coq is busy due to the current action, we don't cancel *)
        match !running_action with
        | Some aid when aid = action -> ()
        | _ -> cancel_signal ~stop_emit:false "Coq busy" in
    Coq.try_grab coqtop action fallback in
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
  let backto_before_error it =
    let rec aux old it =
      if it#is_start || not(it#has_tag Tags.Script.error_bg) then old
      else aux it it#backward_char in
    aux it it in
  let insert_cb it s = if String.length s = 0 then () else begin
    Minilib.log ("insert_cb " ^ string_of_int it#offset);
    let text_mark = add_mark it in
    let () = update_prev it in
    if it#has_tag Tags.Script.to_process then
      cancel_signal "Altering the script being processed in not implemented"
    else if it#has_tag Tags.Script.processed then
      call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
    else if it#has_tag Tags.Script.error_bg then begin
      let prev_sentence_end = backto_before_error it in
      let text_mark = add_mark prev_sentence_end in
      call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
    end end in
  let delete_cb ~start ~stop =
    Minilib.log (Printf.sprintf "delete_cb %d %d" start#offset stop#offset);
    let min_iter, max_iter =
      if start#compare stop < 0 then start, stop else stop, start in
    let () = update_prev min_iter in
    let text_mark = add_mark min_iter in
    let rec aux min_iter =
      if min_iter#equal max_iter then ()
      else if min_iter#has_tag Tags.Script.to_process then
        cancel_signal "Altering the script being processed in not implemented"
      else if min_iter#has_tag Tags.Script.processed then
        call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
      else if min_iter#has_tag Tags.Script.error_bg then
        let prev_sentence_end = backto_before_error min_iter in
        let text_mark = add_mark prev_sentence_end in
        call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
      else aux min_iter#forward_char in
    aux min_iter in
  let begin_action_cb () =
    Minilib.log "begin_action_cb";
    action_was_cancelled := false;
    no_coq_action_required := true;
    cur_action := new_action_id ();
    let where = get_insert () in
    buffer#move_mark (`NAME "prev_insert") ~where in
  let end_action_cb () =
    Minilib.log "end_action_cb";
    ensure_marks_exist ();
    if not !action_was_cancelled then begin
      (* If coq was asked to backtrack, the clenup must be done by the
         backtrack_until function, since it may move the stop_of_input
         to a point indicated by coq. *)
      if !no_coq_action_required then begin
        let start, stop = get_start (), get_stop () in
	List.iter (fun tag -> buffer#remove_tag tag ~start ~stop)
		  Tags.Script.ephemere;
        Sentence.tag_on_insert buffer
      end;
    end in
  let mark_deleted_cb m =
    match GtkText.Mark.get_name m with
    | Some "insert" -> ()
    | Some s -> Minilib.log (s^" deleted")
    | None -> ()
  in
  let mark_set_cb it m =
    debug_edit_zone ();
    let ins = get_insert () in
    let () = Ideutils.display_location ins in
    match GtkText.Mark.get_name m with
    | Some "insert" -> ()
    | Some s -> Minilib.log (s^" moved")
    | None -> ()
  in
  (** Pluging callbacks *)
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
  let refresh clr = data#misc#modify_base [`NORMAL, `NAME clr] in
  let _ = background_color#connect#changed ~callback:refresh in
  let _ = data#misc#connect#realize ~callback:(fun () -> refresh background_color#get) in
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
      Pervasives.compare (store#get ~row:it1 ~column:c) (store#get ~row:it2 ~column:c)
    | `StringC c ->
      Pervasives.compare (store#get ~row:it1 ~column:c) (store#get ~row:it2 ~column:c)
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

let create_errpage (script : Wg_ScriptView.script_view) : errpage =
  let table, access =
    make_table_widget ~sort:(0, `ASCENDING)
      [`Int,"Line",true; `String,"Error message",true]
      (fun columns store tp vc ->
        let row = store#get_iter tp in
        let lno = store#get ~row ~column:(find_int_col "Line" columns) in
        let where = script#buffer#get_iter (`LINE (lno-1)) in
        script#buffer#place_cursor ~where;
        script#misc#grab_focus ();
        ignore (script#scroll_to_iter
		  ~use_align:false ~yalign:0.75 ~within_margin:0.25 where)) in
  let tip = GMisc.label ~text:"Double click to jump to error line" () in
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
          store#set ~row:line ~column:(find_string_col "Error message" columns) msg))
          errs
      end
    method on_update ~callback:cb = callback := cb
    method data = !last_update
  end

let create_jobpage coqtop coqops : jobpage =
  let table, access =
    make_table_widget ~sort:(0, `ASCENDING)
      [`String,"Worker",true; `String,"Job name",true]
      (fun columns store tp vc ->
        let row = store#get_iter tp in
        let w = store#get ~row ~column:(find_string_col "Worker" columns) in
	let info () = Minilib.log ("Coq busy, discarding query") in
	Coq.try_grab coqtop (coqops#stop_worker w) info
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

let create_messages () =
  let messages = Wg_MessageView.message_view () in
  let _ = messages#misc#set_can_focus true in
  Wg_RoutedMessageViews.message_views ~route_0:messages

let dummy_control : control =
  object
    method detach () = ()
  end

let create file coqtop_args =
  let basename = match file with
    |None -> "*scratch*"
    |Some f -> Glib.Convert.filename_to_utf8 (Filename.basename f)
  in
  let coqtop = Coq.spawn_coqtop coqtop_args in
  let reset () = Coq.reset_coqtop coqtop in
  let buffer = create_buffer () in
  let script = create_script coqtop buffer in
  let proof = create_proof () in
  let messages = create_messages () in
  let segment = new Wg_Segment.segment () in
  let finder = new Wg_Find.finder basename (script :> GText.view) in
  let fops = new FileOps.fileops (buffer :> GText.buffer) file reset in
  let _ = fops#update_stats in
  let cops =
    new CoqOps.coqops script proof messages segment coqtop (fun () -> fops#filename) in
  let command = new Wg_Command.command_window basename coqtop cops messages in
  let errpage = create_errpage script in
  let jobpage = create_jobpage coqtop cops in
  let _ = set_buffer_handlers (buffer :> GText.buffer) script cops coqtop in
  let _ = Coq.set_reset_handler coqtop cops#handle_reset_initial in
  let _ = Coq.init_coqtop coqtop cops#initialize in
  {
    buffer = (buffer :> GText.buffer);
    script=script;
    proof=proof;
    messages=messages;
    segment=segment;
    fileops=fops;
    coqops=cops;
    coqtop=coqtop;
    command=command;
    finder=finder;
    tab_label= GMisc.label ~text:basename ();
    errpage=errpage;
    jobpage=jobpage;
    control = dummy_control;
  }

let kill (sn:session) =
  (* To close the detached views of this script, we call manually
     [destroy] on it, triggering some callbacks in [detach_view].
     In a more modern lablgtk, rather use the page-removed signal ? *)
  sn.coqops#destroy ();
  sn.script#destroy ();
  Coq.close_coqtop sn.coqtop

let build_layout (sn:session) =
  let session_paned = GPack.paned `VERTICAL () in
  let session_box =
    GPack.vbox ~packing:(session_paned#pack1 ~shrink:false ~resize:true) ()
  in

  (** Right part of the window. *)

  let eval_paned = GPack.paned `HORIZONTAL ~border_width:5
    ~packing:(session_box#pack ~expand:true) () in
  let script_frame = GBin.frame ~shadow_type:`IN
    ~packing:eval_paned#add1 () in
  let script_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:script_frame#add () in
  let state_paned = GPack.paned `VERTICAL
    ~packing:eval_paned#add2 () in

  (** Proof buffer. *)

  let title = Printf.sprintf "Proof (%s)" sn.tab_label#text in
  let proof_detachable = Wg_Detachable.detachable ~title () in
  let () = proof_detachable#button#misc#hide () in
  let () = proof_detachable#frame#set_shadow_type `IN in
  let () = state_paned#add1 proof_detachable#coerce in
  let callback _ = proof_detachable#show in
  let () = proof_detachable#connect#attached ~callback in
  let callback _ =
    sn.proof#coerce#misc#set_size_request ~width:500 ~height:400 ()
  in
  let () = proof_detachable#connect#detached ~callback in
  let proof_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:proof_detachable#pack () in

  (** Message buffer. *)

  let message_frame = GPack.notebook ~packing:state_paned#add () in
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
  let _ =
    eval_paned#misc#connect#size_allocate
      ~callback:
      (let old_paned_width = ref 2 in
       let old_paned_height = ref 2 in
       fun {Gtk.width=paned_width;Gtk.height=paned_height} ->
         if !old_paned_width <> paned_width ||
            !old_paned_height <> paned_height
         then begin
           eval_paned#set_position
             (eval_paned#position * paned_width / !old_paned_width);
           state_paned#set_position
             (state_paned#position * paned_height / !old_paned_height);
           old_paned_width := paned_width;
           old_paned_height := paned_height;
	 end)
  in
  session_box#pack sn.finder#coerce;
  session_box#pack sn.segment#coerce;
  sn.command#pack_in (session_paned#pack2 ~shrink:false ~resize:false);
  script_scroll#add sn.script#coerce;
  proof_scroll#add sn.proof#coerce;
  let detach, _ = add_msg_page 0 sn.tab_label#text "Messages" sn.messages#default_route#coerce in
  let _, label = add_msg_page 1 sn.tab_label#text "Errors" sn.errpage#coerce in
  let _, _ = add_msg_page 2 sn.tab_label#text "Jobs" sn.jobpage#coerce in
  (** When a message is received, focus on the message pane *)
  let _ =
    sn.messages#default_route#connect#pushed ~callback:(fun _ _ ->
      let num = message_frame#page_num detach#coerce in
      if 0 <= num then message_frame#goto_page num
    )
  in
  (** When an error occurs, paint the error label in red *)
  let txt = label#text in
  let red s = "<span foreground=\"#FF0000\">" ^ s ^ "</span>" in
  sn.errpage#on_update ~callback:(fun l ->
    if l = [] then (label#set_use_markup false; label#set_text txt)
    else (label#set_text (red txt);label#set_use_markup true));
  session_tab#pack sn.tab_label#coerce;
  img#set_stock `YES;
  eval_paned#set_position 1;
  state_paned#set_position 1;
  let control =
    object
      method detach () = proof_detachable#detach ()
    end
  in
  let () = sn.control <- control in
  (Some session_tab#coerce,None,session_paned#coerce)
