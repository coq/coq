(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences
open Gtk_parsing
open Ideutils

type ide_info = {
  start : GText.mark;
  stop : GText.mark;
}

(** Have we used admit or declarative mode's daimon ?
    If yes, we color differently *)

type safety = Safe | Unsafe

let safety_tag = function
  | Safe -> Tags.Script.processed
  | Unsafe -> Tags.Script.unjustified

class type analyzed_views=
object
  val mutable act_id : GtkSignal.id option
  val mutable deact_id : GtkSignal.id option
  val input_buffer : GText.buffer
  val input_view : Undo.undoable_view
  val last_array : string array
  val mutable last_index : bool
  val message_buffer : GText.buffer
  val message_view : GText.view
  val proof_buffer : GText.buffer
  val proof_view : GText.view
  val cmd_stack : ide_info Stack.t
  val mycoqtop : Coq.coqtop ref
  val mutable is_active : bool
  val mutable read_only : bool
  val mutable filename : string option
  val mutable stats : Unix.stats option
  val mutable detached_views : GWindow.window list
  method without_auto_complete : 'a 'b. ('a -> 'b) -> 'a -> 'b
  method set_auto_complete : bool -> unit

  method kill_detached_views : unit -> unit
  method add_detached_view : GWindow.window -> unit
  method remove_detached_view : GWindow.window -> unit

  method filename : string option
  method stats :  Unix.stats option
  method set_filename : string option -> unit
  method update_stats : unit
  method revert : unit
  method auto_save : unit
  method save : string -> bool
  method save_as : string -> bool
  method read_only : bool
  method set_read_only : bool -> unit
  method is_active : bool
  method activate : unit -> unit
  method active_keypress_handler : GdkEvent.Key.t -> bool
  method backtrack_to : GText.iter -> unit
  method backtrack_to_no_lock : GText.iter -> unit
  method clear_message : unit
  method disconnected_keypress_handler : GdkEvent.Key.t -> bool
  method electric_handler : GtkSignal.id
  method find_phrase_starting_at :
    GText.iter -> (GText.iter * GText.iter) option
  method get_insert : GText.iter
  method get_start_of_input : GText.iter
  method go_to_insert : unit
  method indent_current_line : unit
  method go_to_next_occ_of_cur_word : unit
  method go_to_prev_occ_of_cur_word : unit
  method insert_command : string -> string -> unit
  method tactic_wizard : string list -> unit
  method insert_message : string -> unit
  method process_next_phrase : bool -> bool -> bool -> bool
  method process_until_iter_or_error : GText.iter -> unit
  method process_until_end_or_error : unit
  method recenter_insert : unit
  method reset_initial : bool -> unit
  method set_message : string -> unit
  method show_goals : unit
  method show_goals_full : unit
  method undo_last_step : unit
  method help_for_keyword : unit -> unit
  method complete_at_offset : int -> bool
end


type viewable_script =
    {script : Undo.undoable_view;
     tab_label : GMisc.label;
     mutable filename : string;
     mutable encoding : string;
     proof_view : GText.view;
     message_view : GText.view;
     analyzed_view : analyzed_views;
     toplvl : Coq.coqtop ref;
     command : Command_windows.command_window;
    }

let kill_session s =
  s.analyzed_view#kill_detached_views ();
  Coq.kill_coqtop !(s.toplvl)

let build_session s =
  let session_paned = GPack.paned `VERTICAL () in
  let eval_paned = GPack.paned `HORIZONTAL ~border_width:5
    ~packing:(session_paned#pack1 ~shrink:false ~resize:true) () in
  let script_frame = GBin.frame ~shadow_type:`IN
    ~packing:eval_paned#add1 () in
  let script_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:script_frame#add () in
  let state_paned = GPack.paned `VERTICAL
    ~packing:eval_paned#add2 () in
  let proof_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add1 () in
  let proof_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:proof_frame#add () in
  let message_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add2 () in
  let message_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:message_frame#add () in
  let session_tab = GPack.hbox ~homogeneous:false () in
  let img = GMisc.image ~icon_size:`SMALL_TOOLBAR
    ~packing:session_tab#pack () in
  let _ =
    s.script#buffer#connect#modified_changed
      ~callback:(fun () -> if s.script#buffer#modified
        then img#set_stock `SAVE
        else img#set_stock `YES) in
  let _ =
    eval_paned#misc#connect#size_allocate
      ~callback:
      (let old_paned_width = ref 2 in
       let old_paned_height = ref 2 in
       (fun {Gtk.width=paned_width;Gtk.height=paned_height} ->
	 if !old_paned_width <> paned_width || !old_paned_height <> paned_height then (
	   eval_paned#set_position (eval_paned#position * paned_width / !old_paned_width);
	   state_paned#set_position (state_paned#position * paned_height / !old_paned_height);
	   old_paned_width := paned_width;
	   old_paned_height := paned_height;
	 )))
  in
  session_paned#pack2 ~shrink:false ~resize:false (s.command#frame#coerce);
  script_scroll#add s.script#coerce;
  proof_scroll#add s.proof_view#coerce;
  message_scroll#add s.message_view#coerce;
  session_tab#pack s.tab_label#coerce;
  img#set_stock `YES;
  eval_paned#set_position 1;
  state_paned#set_position 1;
  (Some session_tab#coerce,None,session_paned#coerce)

let session_notebook =
  Typed_notebook.create build_session kill_session
    ~border_width:2 ~show_border:false ~scrollable:true ()

let cb = GData.clipboard Gdk.Atom.primary

let last_cb_content = ref ""

let update_notebook_pos () =
  let pos =
    match !current.vertical_tabs, !current.opposite_tabs with
      | false, false -> `TOP
      | false, true  -> `BOTTOM
      | true , false -> `LEFT
      | true , true  -> `RIGHT
  in
  session_notebook#set_tab_pos pos

let to_do_on_page_switch = ref []


(** * Coqide's handling of signals *)

(** We ignore Ctrl-C, and for most of the other catchable signals
    we launch an emergency save of opened files and then exit *)

let signals_to_crash = [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup;
			Sys.sigill; Sys.sigpipe; Sys.sigquit;
			(* Sys.sigsegv; Sys.sigterm;*) Sys.sigusr2]

let crash_save i =
  (*  ignore (Unix.sigprocmask Unix.SIG_BLOCK signals_to_crash);*)
  safe_prerr_endline "Trying to save all buffers in .crashcoqide files";
  let count = ref 0 in
  List.iter
    (function {script=view; analyzed_view = av } ->
      (let filename = match av#filename with
	| None ->
	  incr count;
	  "Unnamed_coqscript_"^(string_of_int !count)^".crashcoqide"
	| Some f -> f^".crashcoqide"
       in
       try
	 if try_export filename (view#buffer#get_text ()) then
	   safe_prerr_endline ("Saved "^filename)
	 else safe_prerr_endline ("Could not save "^filename)
       with _ -> safe_prerr_endline ("Could not save "^filename))
    )
    session_notebook#pages;
  safe_prerr_endline "Done. Please report.";
  if i <> 127 then exit i

let ignore_break () =
  List.iter
    (fun i ->
      try Sys.set_signal i (Sys.Signal_handle crash_save)
      with _ -> prerr_endline "Signal ignored (normal if Win32)")
    signals_to_crash;
  Sys.set_signal Sys.sigint Sys.Signal_ignore


(** * Locks *)

(* Locking machinery for Coq kernel *)
let coq_computing = Mutex.create ()

(* To prevent Coq from interrupting during undoing...*)
let coq_may_stop = Mutex.create ()

let break () =
  prerr_endline "User break received";
  Coq.break_coqtop !(session_notebook#current_term.toplvl)

let force_reset_initial () =
  prerr_endline "Reset Initial";
  session_notebook#current_term.analyzed_view#reset_initial true

let do_if_not_computing text f x =
  let threaded_task () =
    if Mutex.try_lock coq_computing then
      begin
	prerr_endline "Getting lock";
	List.iter
          (fun elt -> try f elt with
            | Sys_error str ->
              elt.analyzed_view#reset_initial false;
              elt.analyzed_view#set_message
                ("Unable to communicate with coqtop, restarting coqtop.\n"^
		    "Error was: "^str)
            | e ->
              Mutex.unlock coq_computing;
              elt.analyzed_view#set_message
                ("Unknown error, please report:\n"^(Printexc.to_string e)))
          x;
	prerr_endline "Releasing lock";
	Mutex.unlock coq_computing;
      end
    else
      prerr_endline "Discarded order (computations are ongoing)"
  in
  prerr_endline ("Launching thread " ^ text);
  ignore (Glib.Timeout.add ~ms:300 ~callback:
            (fun () -> if Mutex.try_lock coq_computing
              then (Mutex.unlock coq_computing; false)
              else (pbar#pulse (); true)));
  ignore (Thread.create threaded_task ())

let warning msg =
  GToolbox.message_box ~title:"Warning"
    ~icon:(let img = GMisc.image () in
	   img#set_stock `DIALOG_WARNING;
	   img#set_icon_size `DIALOG;
	   img#coerce)
    msg

let remove_current_view_page () =
  let do_remove () =
    let c = session_notebook#current_page in
    session_notebook#remove_page c
  in
  let current = session_notebook#current_term in
  if current.script#buffer#modified then
    match GToolbox.question_box ~title:"Close"
      ~buttons:["Save Buffer and Close";
                "Close without Saving";
                "Don't Close"]
      ~default:0
      ~icon:(let img = GMisc.image () in
             img#set_stock `DIALOG_WARNING;
             img#set_icon_size `DIALOG;
             img#coerce)
      "This buffer has unsaved modifications"
    with
      | 1 ->
        begin match current.analyzed_view#filename with
          | None ->
            begin match select_file_for_save ~title:"Save file" () with
              | None -> ()
              | Some f ->
                if current.analyzed_view#save_as f then begin
                  flash_info ("File " ^ f ^ " saved") ;
                  do_remove ()
                end else
                  warning  ("Save Failed (check if " ^ f ^ " is writable)")
            end
          | Some f ->
            if current.analyzed_view#save f then begin
              flash_info ("File " ^ f ^ " saved") ;
              do_remove ()
            end else
              warning  ("Save Failed (check if " ^ f ^ " is writable)")
        end
      | 2 -> do_remove ()
      | _ -> ()

module Opt = Coq.PrintOpt

let print_items = [
  ([Opt.implicit],"Display _implicit arguments",GdkKeysyms._i,false);
  ([Opt.coercions],"Display _coercions",GdkKeysyms._c,false);
  ([Opt.raw_matching],"Display raw _matching expressions",GdkKeysyms._m,true);
  ([Opt.notations],"Display _notations",GdkKeysyms._n,true);
  ([Opt.all_basic],"Display _all basic low-level contents",GdkKeysyms._a,false);
  ([Opt.existential],"Display _existential variable instances",GdkKeysyms._e,false);
  ([Opt.universes],"Display _universe levels",GdkKeysyms._u,false);
  ([Opt.all_basic;Opt.existential;Opt.universes],
   "Display all _low-level contents",GdkKeysyms._l,false)
]

let setopts ct opts v =
  List.fold_left
    (fun acc o ->
      match Coq.PrintOpt.set ct o v with
        | Ide_intf.Good () -> acc
        | Ide_intf.Fail lstr -> Ide_intf.Fail lstr
    ) (Ide_intf.Good ()) opts

(* Reset this to None on page change ! *)
let (last_completion:(string*int*int*bool) option ref) = ref None

let () = to_do_on_page_switch :=
  (fun i -> last_completion := None)::!to_do_on_page_switch

let rec complete input_buffer w (offset:int) =
  match !last_completion with
    | Some (lw,loffset,lpos,backward)
	when lw=w && loffset=offset ->
      begin
	let iter = input_buffer#get_iter (`OFFSET lpos) in
	if backward then
	  match complete_backward w iter with
	    | None ->
	      last_completion :=
		Some (lw,loffset,
		      (find_word_end
			 (input_buffer#get_iter (`OFFSET loffset)))#offset ,
		      false);
	      None
	    | Some (ss,start,stop) as result ->
	      last_completion :=
		Some (w,offset,ss#offset,true);
	      result
	else
	  match complete_forward w iter with
	    | None ->
	      last_completion := None;
	      None
	    | Some (ss,start,stop) as result ->
	      last_completion :=
		Some (w,offset,ss#offset,false);
	      result
      end
    | _ -> begin
      match complete_backward w (input_buffer#get_iter (`OFFSET offset)) with
	| None ->
	  last_completion :=
	    Some (w,offset,(find_word_end (input_buffer#get_iter
					     (`OFFSET offset)))#offset,false);
	  complete input_buffer w offset
	| Some (ss,start,stop) as result ->
	  last_completion := Some (w,offset,ss#offset,true);
	  result
    end

let get_current_word () =
  match session_notebook#current_term,cb#text with
    | {script=script; analyzed_view=av;},None ->
      prerr_endline "None selected";
      let it = av#get_insert in
      let start = find_word_start it in
      let stop = find_word_end start in
      script#buffer#move_mark `SEL_BOUND ~where:start;
      script#buffer#move_mark `INSERT ~where:stop;
      script#buffer#get_text ~slice:true ~start ~stop ()
    | _,Some t ->
      prerr_endline "Some selected";
      prerr_endline t;
      t


let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
  while len := input ic buf 0 1024; !len > 0 do
    Buffer.add_substring b buf 0 !len
  done

let with_file handler name ~f =
  try
    let ic = open_in_gen [Open_rdonly;Open_creat] 0o644 name in
    try f ic; close_in ic with e -> close_in ic; raise e
  with Sys_error s -> handler s


(* For electric handlers *)
exception Found

(* For find_phrase_starting_at *)
exception Stop of int

let tag_of_sort = function
  | Coq_lex.Comment -> Tags.Script.comment
  | Coq_lex.Keyword -> Tags.Script.kwd
  | Coq_lex.Declaration -> Tags.Script.decl
  | Coq_lex.ProofDeclaration -> Tags.Script.proof_decl
  | Coq_lex.Qed -> Tags.Script.qed
  | Coq_lex.String -> failwith "No tag"

let apply_tag (buffer:GText.buffer) orig off_conv from upto sort =
  try
    let tag = tag_of_sort sort in
    let start = orig#forward_chars (off_conv from) in
    let stop = orig#forward_chars (off_conv upto) in
    buffer#apply_tag ~start ~stop tag
  with _ -> ()

let remove_tags (buffer:GText.buffer) from upto =
  List.iter (buffer#remove_tag ~start:from ~stop:upto)
    [ Tags.Script.comment; Tags.Script.kwd; Tags.Script.decl;
      Tags.Script.proof_decl; Tags.Script.qed ]

let split_slice_lax (buffer:GText.buffer) from upto =
  remove_tags buffer from upto;
  buffer#remove_tag ~start:from ~stop:upto Tags.Script.sentence;
  let slice = buffer#get_text ~start:from ~stop:upto () in
  let slice = slice ^ " " in
  let rec split_substring str =
    let off_conv = byte_offset_to_char_offset str in
    let slice_len = String.length str in
    let start_off,end_off = Coq_lex.find_end_offset (apply_tag buffer from off_conv) str in

    let _ = from#forward_chars (off_conv start_off) in
    let stop = from#forward_chars (pred (off_conv end_off)) in
    let start = stop#backward_char in
    buffer#apply_tag ~start ~stop Tags.Script.sentence;

    if 1 < slice_len - end_off then begin (* remember that we added a trailing space *)
      ignore (from#nocopy#forward_chars (off_conv end_off));
      split_substring (String.sub str end_off (slice_len - end_off))
    end
  in
  split_substring slice

let rec grab_safe_sentence_start (iter:GText.iter) soi =
  let lax_back = iter#backward_char#has_tag Tags.Script.sentence in
  let on_space = List.mem iter#char [0x09;0x0A;0x20;0x0D] in
  let full_ending = iter#is_start || (lax_back & on_space) in
  if full_ending then iter
  else if iter#compare soi <= 0 then raise Not_found
  else
    let prev = iter#backward_to_tag_toggle (Some Tags.Script.sentence) in
    (if prev#has_tag Tags.Script.sentence then
	ignore (prev#nocopy#backward_to_tag_toggle (Some Tags.Script.sentence)));
    grab_safe_sentence_start prev soi

let grab_sentence_end_from (start:GText.iter) =
  let stop = start#forward_to_tag_toggle (Some Tags.Script.sentence) in
  stop#forward_char

(* XXX - a activer plus tard
   let get_curr_sentence (iter:GText.iter) =
   let start = iter#backward_to_tag_toggle (Some Tags.Script.sentence) in
   if not (start#has_tag Tags.Script.sentence) then
   ignore (start#nocopy#backward_to_tag_toggle (Some Tags.Script.sentence));
   let stop = start#forward_to_tag_toggle (Some Tags.Script.sentence) in
   start,stop

   let get_next_sentence ?(check=false) (iter:GText.iter) =
   let start = iter#forward_to_tag_toggle (Some Tags.Script.sentence) in
   if iter#has_tag Tags.Script.sentence then
   ignore (start#nocopy#forward_to_tag_toggle (Some Tags.Script.sentence));
   if check && (not (start#has_tag Tags.Script.sentence)) then
   raise Not_found;
   let stop = start#forward_to_tag_toggle (Some Tags.Script.sentence) in
   start,stop
*)

let tag_on_insert =
  (* possible race condition here : editing two buffers with a timedelta smaller
   * than 1.5s might break the error recovery mechanism. *)
  let skip_last = ref (ref true) in (* ref to the mutable flag created on last call *)
  fun buffer ->
    try
      let insert = buffer#get_iter_at_mark `INSERT in
      let start = grab_safe_sentence_start insert
        (buffer#get_iter_at_mark (`NAME "start_of_input")) in
      let stop = grab_sentence_end_from insert in
      let skip_curr = ref true in (* shall the callback be skipped ? by default yes*)
      (!skip_last) := true; (* skip the previously created callback *)
      skip_last := skip_curr;
      try split_slice_lax buffer start stop
      with Not_found ->
        skip_curr := false;
        ignore (Glib.Timeout.add ~ms:1500
                  ~callback:(fun () -> if not !skip_curr then (
                    try split_slice_lax buffer start buffer#end_iter with _ -> ()); false))
    with Not_found ->
      let err_pos = buffer#get_iter_at_mark (`NAME "start_of_input") in
      buffer#apply_tag Tags.Script.error ~start:err_pos ~stop:err_pos#forward_char

let force_retag buffer =
  try split_slice_lax buffer buffer#start_iter buffer#end_iter with _ -> ()

let toggle_proof_visibility (buffer:GText.buffer) (cursor:GText.iter) =
  (* move back twice if not into proof_decl,
   * once if into proof_decl and back_char into_proof_decl,
   * don't move if into proof_decl and back_char not into proof_decl *)
  if not (cursor#has_tag Tags.Script.proof_decl) then
    ignore (cursor#nocopy#backward_to_tag_toggle (Some Tags.Script.proof_decl));
  if cursor#backward_char#has_tag Tags.Script.proof_decl then
    ignore (cursor#nocopy#backward_to_tag_toggle (Some Tags.Script.proof_decl));
  let decl_start = cursor in
  let prf_end = decl_start#forward_to_tag_toggle (Some Tags.Script.qed) in
  let decl_end = grab_sentence_end_from decl_start in
  let prf_end = grab_sentence_end_from prf_end in
  let prf_end = prf_end#forward_char in
  if decl_start#has_tag Tags.Script.folded then (
    buffer#remove_tag ~start:decl_start ~stop:decl_end Tags.Script.folded;
    buffer#remove_tag ~start:decl_end ~stop:prf_end Tags.Script.hidden)
  else (
    buffer#apply_tag ~start:decl_start ~stop:decl_end Tags.Script.folded;
    buffer#apply_tag ~start:decl_end ~stop:prf_end Tags.Script.hidden)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
let sup_args = ref []

class analyzed_view (_script:Undo.undoable_view) (_pv:GText.view) (_mv:GText.view) _cs _ct =
object(self)
  val input_view = _script
  val input_buffer = _script#buffer
  val proof_view = _pv
  val proof_buffer = _pv#buffer
  val message_view = _mv
  val message_buffer = _mv#buffer
  val cmd_stack = _cs
  val mycoqtop = _ct
  val mutable is_active = false
  val mutable read_only = false
  val mutable filename = None
  val mutable stats = None
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.
  val mutable detached_views = []
  val mutable find_forward_instead_of_backward = false

  val mutable auto_complete_on = !current.auto_complete
  val hidden_proofs = Hashtbl.create 32

  method private toggle_auto_complete =
    auto_complete_on <- not auto_complete_on
  method set_auto_complete t = auto_complete_on <- t
  method without_auto_complete : 'a 'b. ('a -> 'b) -> 'a -> 'b = fun f x ->
    let old = auto_complete_on in
    self#set_auto_complete false;
    let y = f x in
    self#set_auto_complete old;
    y
  method add_detached_view (w:GWindow.window) =
    detached_views <- w::detached_views
  method remove_detached_view (w:GWindow.window) =
    detached_views <- List.filter (fun e -> w#misc#get_oid<>e#misc#get_oid) detached_views

  method kill_detached_views () =
    List.iter (fun w -> w#destroy ()) detached_views;
    detached_views <- []

  method filename = filename
  method stats = stats
  method set_filename f =
    filename <- f;
    match f with
      | Some f -> stats <- my_stat f
      | None -> ()

  method update_stats =
    match filename with
      | Some f -> stats <- my_stat f
      | _ -> ()

  method revert =
    match filename with
      | Some f -> begin
        let do_revert () = begin
          push_info "Reverting buffer";
          try
            if is_active then self#reset_initial false;
            let b = Buffer.create 1024 in
            with_file flash_info f ~f:(input_channel b);
            let s = try_convert (Buffer.contents b) in
            input_buffer#set_text s;
            self#update_stats;
            input_buffer#place_cursor ~where:input_buffer#start_iter;
            input_buffer#set_modified false;
            pop_info ();
            flash_info "Buffer reverted";
            force_retag input_buffer;
          with _  ->
            pop_info ();
            flash_info "Warning: could not revert buffer";
        end
        in
        if input_buffer#modified then
          match (GToolbox.question_box
                   ~title:"Modified buffer changed on disk"
                   ~buttons:["Revert from File";
                             "Overwrite File";
                             "Disable Auto Revert"]
                   ~default:0
                   ~icon:(stock_to_widget `DIALOG_WARNING)
                   "Some unsaved buffers changed on disk"
          )
          with 1 -> do_revert ()
            | 2 -> if self#save f then flash_info "Overwritten" else
                flash_info "Could not overwrite file"
            | _ ->
              prerr_endline "Auto revert set to false";
              !current.global_auto_revert <- false;
              disconnect_revert_timer ()
        else do_revert ()
      end
      | None -> ()

  method save f =
    if try_export f (input_buffer#get_text ()) then begin
      filename <- Some f;
      input_buffer#set_modified false;
      stats <- my_stat f;
      (match self#auto_save_name with
        | None -> ()
        | Some fn -> try Sys.remove fn with _ -> ());
      true
    end
    else false

  method private auto_save_name =
    match filename with
      | None -> None
      | Some f ->
        let dir = Filename.dirname f in
        let base = (fst !current.auto_save_name) ^
          (Filename.basename f) ^
          (snd !current.auto_save_name)
        in Some (Filename.concat dir base)

  method private need_auto_save =
    input_buffer#modified &&
      last_modification_time > last_auto_save_time

  method auto_save =
    if self#need_auto_save then begin
      match self#auto_save_name with
        | None -> ()
        | Some fn ->
          try
            last_auto_save_time <- Unix.time();
            prerr_endline ("Autosave time : "^(string_of_float (Unix.time())));
            if try_export fn (input_buffer#get_text ()) then begin
              flash_info ~delay:1000 "Autosaved"
            end
            else warning
              ("Autosave failed (check if " ^ fn ^ " is writable)")
          with _ ->
            warning ("Autosave: unexpected error while writing "^fn)
    end

  method save_as f =
    if Sys.file_exists f then
      match (GToolbox.question_box ~title:"File exists on disk"
               ~buttons:["Overwrite";
                         "Cancel";]
               ~default:1
               ~icon:
               (let img = GMisc.image () in
                img#set_stock `DIALOG_WARNING;
                img#set_icon_size `DIALOG;
                img#coerce)
               ("File "^f^"already exists")
      )
      with 1 -> self#save f
        | _ -> false
    else self#save f

  method set_read_only b = read_only<-b
  method read_only = read_only
  method is_active = is_active
  method insert_message s =
    message_buffer#insert s;
    message_view#misc#draw None

  method set_message s =
    message_buffer#set_text s;
    message_view#misc#draw None

  method clear_message = message_buffer#set_text ""
  val mutable last_index = true
  val last_array = [|"";""|]
  method get_start_of_input =  input_buffer#get_iter_at_mark (`NAME "start_of_input")

  method get_insert = get_insert input_buffer

  method recenter_insert =
    (* BUG : to investigate further:
       FIXED : Never call  GMain.* in thread !
       PLUS : GTK BUG ??? Cannot be called from a thread...
       ADDITION: using sync instead of async causes deadlock...*)
    ignore (GtkThread.async (
      input_view#scroll_to_mark
        ~use_align:false
        ~yalign:0.75
        ~within_margin:0.25)
              `INSERT)


  method indent_current_line =
    let get_nb_space it =
      let it = it#copy in
      let nb_sep = ref 0 in
      let continue = ref true in
      while !continue do
        if it#char = space then begin
          incr nb_sep;
          if not it#nocopy#forward_char then continue := false;
        end else continue := false
      done;
      !nb_sep
    in
    let previous_line = self#get_insert in
    if previous_line#nocopy#backward_line then begin
      let previous_line_spaces = get_nb_space previous_line in
      let current_line_start = self#get_insert#set_line_offset 0 in
      let current_line_spaces = get_nb_space current_line_start in
      if input_buffer#delete_interactive
        ~start:current_line_start
        ~stop:(current_line_start#forward_chars current_line_spaces)
        ()
      then
        let current_line_start = self#get_insert#set_line_offset 0 in
        input_buffer#insert
          ~iter:current_line_start
          (String.make previous_line_spaces ' ')
    end


  method go_to_next_occ_of_cur_word =
    let cv = session_notebook#current_term in
    let av = cv.analyzed_view in
    let b = (cv.script)#buffer in
    let start = find_word_start (av#get_insert) in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    match stop#forward_search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  method go_to_prev_occ_of_cur_word =
    let cv = session_notebook#current_term in
    let av = cv.analyzed_view in
    let b = (cv.script)#buffer in
    let start = find_word_start (av#get_insert) in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    match start#backward_search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  val mutable full_goal_done = true

  method show_goals_full =
    if not full_goal_done then
      proof_view#buffer#set_text "";
    begin
      let menu_callback = if !current.contextual_menus_on_goal then
          (fun s () -> ignore (self#insert_this_phrase_on_success
                                 true true false ("progress "^s) s))
        else
          (fun _ _ -> ()) in
      try
        match Coq.current_goals !mycoqtop with
          | Ide_intf.Fail (l,str) ->
            self#set_message ("Error in coqtop :\n"^str)
          | Ide_intf.Good goals ->
            Ideproof.display
              (Ideproof.mode_tactic menu_callback)
              proof_view goals
      with
        | e -> prerr_endline (Printexc.to_string e)
    end

  method show_goals = self#show_goals_full

  method private send_to_coq ct verbosely phrase show_output show_error localize =
    let display_output msg =
      self#insert_message (if show_output then msg else "") in
    let display_error (loc,s) =
      if show_error then begin
        if not (Glib.Utf8.validate s) then
          flash_info "This error is so nasty that I can't even display it."
        else begin
          self#insert_message s;
          message_view#misc#draw None;
          if localize then
            (match loc with
              | None -> ()
              | Some (start,stop) ->
                let convert_pos = byte_offset_to_char_offset phrase in
                let start = convert_pos start in
                let stop = convert_pos stop in
                let i = self#get_start_of_input in
                let starti = i#forward_chars start in
                let stopi = i#forward_chars stop in
                input_buffer#apply_tag Tags.Script.error
                  ~start:starti
                  ~stop:stopi;
                input_buffer#place_cursor ~where:starti)
        end
      end in
    try
      full_goal_done <- false;
      prerr_endline "Send_to_coq starting now";
      (* It's important here to work with [ct] and not [!mycoqtop], otherwise
         we could miss a restart of coqtop and continue sending it orders. *)
      match Coq.interp ct verbosely phrase with
        | Ide_intf.Fail (l,str) -> sync display_error (l,str); None
        | Ide_intf.Good () ->
	  match Coq.read_stdout ct with
            | Ide_intf.Fail (l,str) -> sync display_error (l,str); None
            | Ide_intf.Good msg ->
              sync display_output msg;
	      (** TODO: Restore someday the access to Decl_mode.get_damon_flag,
		  and also detect the use of admit, and then return Unsafe *)
              Some Safe
    with
      | e ->
        sync display_error (Coq.process_exn e); None

  method find_phrase_starting_at (start:GText.iter) =
    try
      let start = grab_safe_sentence_start start self#get_start_of_input in
      let stop = grab_sentence_end_from start in
      if (stop#backward_char#has_tag Tags.Script.sentence) then
        Some (start,stop)
      else
        None
    with Not_found -> None

  method complete_at_offset (offset:int) =
    prerr_endline ("Completion at offset : " ^ string_of_int offset);
    let it () = input_buffer#get_iter (`OFFSET offset) in
    let iit = it () in
    let start = find_word_start iit in
    if ends_word iit then
      let w = input_buffer#get_text
        ~start
        ~stop:iit
        ()
      in
      if String.length w <> 0 then begin
        prerr_endline ("Completion of prefix : '" ^ w^"'");
        match complete input_buffer w start#offset with
          | None -> false
          | Some (ss,start,stop) ->
            let completion = input_buffer#get_text ~start ~stop () in
            ignore (input_buffer#delete_selection ());
            ignore (input_buffer#insert_interactive completion);
            input_buffer#move_mark `SEL_BOUND ~where:(it())#backward_char;
            true
      end else false
    else false

  method private process_next_phrase_full ct verbosely display_goals do_highlight =
    let get_next_phrase () =
      self#clear_message;
      prerr_endline "process_next_phrase starting now";
      if do_highlight then begin
        push_info "Coq is computing";
        input_view#set_editable false;
      end;
      match self#find_phrase_starting_at self#get_start_of_input with
        | None ->
          if do_highlight then begin
            input_view#set_editable true;
            pop_info ();
          end;
          None
        | Some(start,stop) ->
          prerr_endline "process_next_phrase : to_process highlight";
          if do_highlight then begin
            input_buffer#apply_tag Tags.Script.to_process ~start ~stop;
            prerr_endline "process_next_phrase : to_process applied";
          end;
          prerr_endline "process_next_phrase : getting phrase";
          Some((start,stop),start#get_slice ~stop) in
    let remove_tag (start,stop) =
      if do_highlight then begin
        input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
        input_view#set_editable true;
        pop_info ();
      end in
    let mark_processed safe (start,stop) =
      let b = input_buffer in
      b#move_mark ~where:stop (`NAME "start_of_input");
      b#apply_tag (safety_tag safe) ~start ~stop;
      if (self#get_insert#compare) stop <= 0 then
        begin
          b#place_cursor ~where:stop;
          self#recenter_insert
        end;
      let ide_payload = { start = `MARK (b#create_mark start);
                          stop = `MARK (b#create_mark stop); } in
      Stack.push ide_payload cmd_stack;
      if display_goals then self#show_goals;
      remove_tag (start,stop) in
    begin
      match sync get_next_phrase () with
          None -> false
        | Some (loc,phrase) ->
          (match self#send_to_coq ct verbosely phrase true true true with
            | Some safe -> sync mark_processed safe loc; true
            | None -> sync remove_tag loc; false)
    end

  method process_next_phrase verbosely display_goals do_highlight =
    self#process_next_phrase_full !mycoqtop verbosely display_goals do_highlight

  method private insert_this_phrase_on_success
    show_output show_msg localize coqphrase insertphrase =
    let mark_processed safe =
      let stop = self#get_start_of_input in
      if stop#starts_line then
        input_buffer#insert ~iter:stop insertphrase
      else input_buffer#insert ~iter:stop ("\n"^insertphrase);
      let start = self#get_start_of_input in
      input_buffer#move_mark ~where:stop (`NAME "start_of_input");
      input_buffer#apply_tag (safety_tag safe) ~start ~stop;
      if (self#get_insert#compare) stop <= 0 then
        input_buffer#place_cursor ~where:stop;
      let ide_payload = { start = `MARK (input_buffer#create_mark start);
                          stop = `MARK (input_buffer#create_mark stop); } in
      Stack.push ide_payload cmd_stack;
      self#show_goals;
       (*Auto insert save on success...
	 try (match Coq.get_current_goals () with
	 | [] ->
	 (match self#send_to_coq "Save.\n" true true true with
	 | Some ast ->
	 begin
	 let stop = self#get_start_of_input in
	 if stop#starts_line then
	 input_buffer#insert ~iter:stop "Save.\n"
	 else input_buffer#insert ~iter:stop "\nSave.\n";
	 let start = self#get_start_of_input in
	 input_buffer#move_mark ~where:stop (`NAME"start_of_input");
	 input_buffer#apply_tag_by_name "processed" ~start ~stop;
	 if (self#get_insert#compare) stop <= 0 then
	 input_buffer#place_cursor stop;
	 let start_of_phrase_mark =
	 `MARK (input_buffer#create_mark start) in
	 let end_of_phrase_mark =
	 `MARK (input_buffer#create_mark stop) in
	 push_phrase
	 reset_info start_of_phrase_mark end_of_phrase_mark ast
	 end
	 | None -> ())
	 | _ -> ())
	 with _ -> ()*) in
    match self#send_to_coq !mycoqtop false coqphrase show_output show_msg localize with
      | Some safe -> sync mark_processed safe; true
      | None ->
        sync
          (fun _ -> self#insert_message ("Unsuccessfully tried: "^coqphrase))
          ();
        false

  method process_until_iter_or_error stop =
    let stop' = `OFFSET stop#offset in
    let start = self#get_start_of_input#copy in
    let start' = `OFFSET start#offset in
    sync (fun _ ->
      input_buffer#apply_tag Tags.Script.to_process ~start ~stop;
      input_view#set_editable false) ();
    push_info "Coq is computing";
    let get_current () =
      if !current.stop_before then
        match self#find_phrase_starting_at self#get_start_of_input with
          | None -> self#get_start_of_input
          | Some (_, stop2) -> stop2
      else begin
        self#get_start_of_input
      end
    in
    (* All the [process_next_phrase] below should be done with the same [ct]
       instead of accessing multiple time [mycoqtop]. Otherwise a restart of
       coqtop could go unnoticed, and the new coqtop could receive strange
       things. *)
    let ct = !mycoqtop in
    while ((stop#compare (get_current())>=0)
           && (self#process_next_phrase_full ct false false false))
    do () done;
    sync (fun _ ->
      self#show_goals;
      (* Start and stop might be invalid if an eol was added at eof *)
      let start = input_buffer#get_iter start' in
      let stop =  input_buffer#get_iter stop' in
      input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
      input_view#set_editable true) ();
    pop_info()

  method process_until_end_or_error =
    self#process_until_iter_or_error input_buffer#end_iter

  method reset_initial mustlock =
    mycoqtop := Coq.reset_coqtop !mycoqtop;
    if mustlock then Mutex.lock coq_computing;
    sync (fun _ ->
      Stack.iter
        (function inf ->
          let start = input_buffer#get_iter_at_mark inf.start in
          let stop = input_buffer#get_iter_at_mark inf.stop in
          input_buffer#move_mark ~where:start (`NAME "start_of_input");
          input_buffer#remove_tag Tags.Script.processed ~start ~stop;
          input_buffer#remove_tag Tags.Script.unjustified ~start ~stop;
          input_buffer#delete_mark inf.start;
          input_buffer#delete_mark inf.stop;
        )
        cmd_stack;
      Stack.clear cmd_stack;
      self#clear_message)();
    if mustlock then Mutex.unlock coq_computing

  (* backtrack Coq to the phrase preceding iterator [i] *)
  method backtrack_to_no_lock i =
    prerr_endline "Backtracking_to iter starts now.";
    full_goal_done <- false;
    (* pop Coq commands until we reach iterator [i] *)
    let rec n_step n =
      if Stack.is_empty cmd_stack then n else
        let ide_ri = Stack.pop cmd_stack in
        if i#compare (input_buffer#get_iter_at_mark ide_ri.stop) < 0 then
          n_step (succ n)
        else
          (Stack.push ide_ri cmd_stack; n)
    in
    begin
      try
        match Coq.rewind !mycoqtop (n_step 0) with
          | Ide_intf.Fail (l,str) ->
            sync self#set_message
              ("Error while backtracking :\n" ^ str ^ "\n" ^
	       "CoqIDE and coqtop may be out of sync," ^
	       "you may want to use Restart.")
          | Ide_intf.Good () ->
            sync (fun _ ->
              let start =
                if Stack.is_empty cmd_stack then input_buffer#start_iter
                else input_buffer#get_iter_at_mark (Stack.top cmd_stack).stop in
              prerr_endline "Removing (long) processed tag...";
              input_buffer#remove_tag
                Tags.Script.processed
                ~start
                ~stop:self#get_start_of_input;
              input_buffer#remove_tag
                Tags.Script.unjustified
                ~start
                ~stop:self#get_start_of_input;
              prerr_endline "Moving (long) start_of_input...";
              input_buffer#move_mark ~where:start (`NAME "start_of_input");
              self#show_goals;
              self#clear_message)
              ();
      with _ ->
        push_info
	  ("WARNING: undo failed badly.\n" ^
	   "Coq might be in an inconsistent state.\n" ^
	   "Please restart and report.");
    end

  method backtrack_to i =
    if Mutex.try_lock coq_may_stop then
      (push_info "Undoing...";
       self#backtrack_to_no_lock i; Mutex.unlock coq_may_stop;
       pop_info ())
    else prerr_endline "backtrack_to : discarded (lock is busy)"

  method go_to_insert =
    let point = self#get_insert in
    if point#compare self#get_start_of_input>=0
    then self#process_until_iter_or_error point
    else self#backtrack_to point

  method undo_last_step =
    full_goal_done <- false;
    if Mutex.try_lock coq_may_stop then
      (push_info "Undoing last step...";
       (try
          let ide_ri = Stack.pop cmd_stack in
          let start = input_buffer#get_iter_at_mark ide_ri.start in
          let update_input () =
            prerr_endline "Removing processed tag...";
            input_buffer#remove_tag
              Tags.Script.processed
              ~start
              ~stop:(input_buffer#get_iter_at_mark ide_ri.stop);
            input_buffer#remove_tag
              Tags.Script.unjustified
              ~start
              ~stop:(input_buffer#get_iter_at_mark ide_ri.stop);
            prerr_endline "Moving start_of_input";
            input_buffer#move_mark
              ~where:start
              (`NAME "start_of_input");
            input_buffer#place_cursor ~where:start;
            self#recenter_insert;
            self#show_goals;
            self#clear_message
          in
          ignore (Coq.rewind !mycoqtop 1);
          sync update_input ()
        with
          | Stack.Empty -> (* flash_info "Nothing to Undo"*)()
       );
       pop_info ();
       Mutex.unlock coq_may_stop)
    else prerr_endline "undo_last_step discarded"


  method insert_command cp ip =
    async(fun _ -> self#clear_message)();
    ignore (self#insert_this_phrase_on_success true false false cp ip)

  method tactic_wizard l =
    async(fun _ -> self#clear_message)();
    ignore
      (List.exists
         (fun p ->
           self#insert_this_phrase_on_success true false false
             ("progress "^p^".\n") (p^".\n")) l)

  method active_keypress_handler k =
    let state = GdkEvent.Key.state k in
    begin
      match  state with
        | l when List.mem `MOD1 l ->
          let k = GdkEvent.Key.keyval k in
          if GdkKeysyms._Return=k
          then ignore(
            if (input_buffer#insert_interactive "\n") then
              begin
                let i= self#get_insert#backward_word_start in
                prerr_endline "active_kp_hf: Placing cursor";
                self#process_until_iter_or_error i
              end);
          true
        | l when List.mem `CONTROL l ->
          let k = GdkEvent.Key.keyval k in
          if GdkKeysyms._Break=k
          then break ();
          false
        | l ->
          if GdkEvent.Key.keyval k = GdkKeysyms._Tab then begin
            prerr_endline "active_kp_handler for Tab";
            self#indent_current_line;
            true
          end else false
    end


  method disconnected_keypress_handler k =
    match GdkEvent.Key.state k with
      | l when List.mem `CONTROL l ->
        let k = GdkEvent.Key.keyval k in
        if GdkKeysyms._c=k
        then break ();
        false
      | l -> false


  val mutable deact_id = None
  val mutable act_id = None

  method activate () = if not is_active then begin
    is_active <- true;
    act_id <- Some
      (input_view#event#connect#key_press ~callback:self#active_keypress_handler);
    prerr_endline "CONNECTED active : ";
    print_id (match act_id with Some x -> x | None -> assert false);
    match
      filename
    with
      | None -> ()
      | Some f ->
	let dir = Filename.dirname f in
	let ct = !mycoqtop in
	match Coq.is_in_loadpath ct dir with
	  | Ide_intf.Fail (_,str) ->
	    self#set_message
	      ("Could not determine lodpath, this might lead to problems:\n"^str)
	  | Ide_intf.Good true -> ()
	  | Ide_intf.Good false ->
	    let cmd = Printf.sprintf "Add LoadPath \"%s\". "  dir in
	    match Coq.interp ct false cmd with
	      | Ide_intf.Fail (l,str) ->
		self#set_message ("Couln't add loadpath:\n"^str)
	      | Ide_intf.Good () -> ()
  end

  method electric_handler =
    input_buffer#connect#insert_text ~callback:
      (fun it x ->
        begin try
		if last_index then begin
		  last_array.(0)<-x;
		  if (last_array.(1) ^ last_array.(0) = ".\n") then raise Found
		end else begin
		  last_array.(1)<-x;
		  if (last_array.(0) ^ last_array.(1) = ".\n") then raise Found
		end
          with Found ->
            begin
              ignore (self#process_next_phrase false true true)
            end;
        end;
        last_index <- not last_index;)

  method private electric_paren tag =
    let oparen_code = Glib.Utf8.to_unichar "("  ~pos:(ref 0) in
    let cparen_code = Glib.Utf8.to_unichar ")"  ~pos:(ref 0) in
    ignore (input_buffer#connect#insert_text ~callback:
              (fun it x ->
                input_buffer#remove_tag
                  ~start:input_buffer#start_iter
                  ~stop:input_buffer#end_iter
                  tag;
                if x = "" then () else
                  match x.[String.length x - 1] with
                    | ')' ->
                      let hit = self#get_insert in
                      let count = ref 0 in
                      if hit#nocopy#backward_find_char
                        (fun c ->
                          if c = oparen_code && !count = 0 then true
                          else if c = cparen_code then
                            (incr count;false)
                          else if c = oparen_code then
                            (decr count;false)
                          else false
                        )
                      then
                        begin
                          prerr_endline "Found matching parenthesis";
                          input_buffer#apply_tag tag ~start:hit ~stop:hit#forward_char
                        end
                      else ()
                    | _ -> ())
  )

  method help_for_keyword () =
    browse_keyword (self#insert_message) (get_current_word ())

  initializer
    ignore (message_buffer#connect#insert_text
              ~callback:(fun it s -> ignore
                (message_view#scroll_to_mark
                   ~use_align:false
                   ~within_margin:0.49
                   `INSERT)));
    ignore (input_buffer#connect#insert_text
              ~callback:(fun it s ->
                if (it#compare self#get_start_of_input)<0
                then GtkSignal.stop_emit ();
                if String.length s > 1 then
                  (prerr_endline "insert_text: Placing cursor";input_buffer#place_cursor ~where:it)));
    ignore (input_buffer#connect#after#apply_tag
              ~callback:(fun tag ~start ~stop ->
                if (start#compare self#get_start_of_input)>=0
                then
                  begin
                    input_buffer#remove_tag
                      Tags.Script.processed
                      ~start
                      ~stop;
                    input_buffer#remove_tag
                      Tags.Script.unjustified
                      ~start
                      ~stop
                  end
              )
    );
    ignore (input_buffer#connect#after#insert_text
              ~callback:(fun it s ->
                if auto_complete_on &&
                  String.length s = 1 && s <> " " && s <> "\n"
                then
                  let v = session_notebook#current_term.analyzed_view
                  in
                  let has_completed =
                    v#complete_at_offset
                      ((input_view#buffer#get_iter `SEL_BOUND)#offset)
                  in
                  if has_completed then
                    input_buffer#move_mark `SEL_BOUND ~where:(input_buffer#get_iter `SEL_BOUND)#forward_char;


              )
    );
    ignore (input_buffer#connect#changed
              ~callback:(fun () ->
                last_modification_time <- Unix.time ();
                let r = input_view#visible_rect in
                let stop =
                  input_view#get_iter_at_location
                    ~x:(Gdk.Rectangle.x r + Gdk.Rectangle.width r)
                    ~y:(Gdk.Rectangle.y r + Gdk.Rectangle.height r)
                in
                input_buffer#remove_tag
                  Tags.Script.error
                  ~start:self#get_start_of_input
                  ~stop;
                tag_on_insert input_buffer
              )
    );
    ignore (input_buffer#add_selection_clipboard cb);
    ignore (proof_buffer#add_selection_clipboard cb);
    ignore (message_buffer#add_selection_clipboard cb);
    self#electric_paren Tags.Script.paren;
    ignore (input_buffer#connect#after#mark_set
              ~callback:(fun it (m:Gtk.text_mark) ->
                !set_location
                  (Printf.sprintf
                     "Line: %5d Char: %3d" (self#get_insert#line + 1)
                     (self#get_insert#line_offset + 1));
                match GtkText.Mark.get_name m  with
                  | Some "insert" ->
                    input_buffer#remove_tag
                      ~start:input_buffer#start_iter
                      ~stop:input_buffer#end_iter
                      Tags.Script.paren;
                  | Some s ->
                    prerr_endline (s^" moved")
                  | None -> () )
    );
    ignore (input_buffer#connect#insert_text
              ~callback:(fun it s ->
                prerr_endline "Should recenter ?";
                if String.contains s '\n' then begin
                  prerr_endline "Should recenter : yes";
                  self#recenter_insert
                end));
end

let last_make = ref "";;
let last_make_index = ref 0;;
let search_compile_error_regexp =
  Str.regexp
    "File \"\\([^\"]+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)";;

let search_next_error () =
  let _ = Str.search_forward search_compile_error_regexp !last_make !last_make_index in
  let f = Str.matched_group 1 !last_make
  and l = int_of_string (Str.matched_group 2 !last_make)
  and b = int_of_string (Str.matched_group 3 !last_make)
  and e = int_of_string (Str.matched_group 4 !last_make)
  and msg_index = Str.match_beginning ()
  in
  last_make_index := Str.group_end 4;
  (f,l,b,e,
   String.sub !last_make msg_index (String.length !last_make - msg_index))



(**********************************************************************)
(* session creation and primitive handling                            *)
(**********************************************************************)

let create_session () =
  let script =
    Undo.undoable_view
      ~buffer:(GText.buffer ~tag_table:Tags.Script.table ())
      ~wrap_mode:`NONE () in
  let proof =
    GText.view
      ~buffer:(GText.buffer ~tag_table:Tags.Proof.table ())
      ~editable:false ~wrap_mode:`CHAR () in
  let message =
    GText.view
      ~buffer:(GText.buffer ~tag_table:Tags.Message.table ())
      ~editable:false ~wrap_mode:`WORD () in
  let basename = GMisc.label ~text:"*scratch*" () in
  let stack = Stack.create () in
  let ct = ref (Coq.spawn_coqtop !sup_args) in
  let command = new Command_windows.command_window !ct in
  let legacy_av = new analyzed_view script proof message stack ct in
  let _ =
    script#buffer#create_mark ~name:"start_of_input" script#buffer#start_iter in
  let _ =
    proof#buffer#create_mark ~name:"end_of_conclusion" proof#buffer#start_iter in
  let _ =
    GtkBase.Widget.add_events proof#as_widget [`ENTER_NOTIFY;`POINTER_MOTION] in
  let _ =
    List.map (fun (opts,_,_,dflt) -> setopts !ct opts dflt) print_items in
  let _ = legacy_av#activate () in
  let _ =
    proof#event#connect#motion_notify ~callback:
      (fun e ->
        let win = match proof#get_window `WIDGET with
          | None -> assert false
          | Some w -> w in
        let x,y = Gdk.Window.get_pointer_location win in
        let b_x,b_y = proof#window_to_buffer_coords ~tag:`WIDGET ~x ~y in
        let it = proof#get_iter_at_location ~x:b_x ~y:b_y in
        let tags = it#tags in
        List.iter
          (fun t ->
            ignore (GtkText.Tag.event t#as_tag proof#as_widget e it#as_iter))
          tags;
        false) in
  script#misc#set_name "ScriptWindow";
  script#buffer#place_cursor ~where:(script#buffer#start_iter);
  proof#misc#set_can_focus true;
  message#misc#set_can_focus true;
  script#misc#modify_font !current.text_font;
  proof#misc#modify_font !current.text_font;
  message#misc#modify_font !current.text_font;
  { tab_label=basename;
    filename="";
    script=script;
    proof_view=proof;
    message_view=message;
    analyzed_view=legacy_av;
    encoding="";
    toplvl=ct;
    command=command
  }

(* XXX - to be used later
   let load_session session filename encs =
   session.encoding <- List.find (IdeIO.load filename session.script#buffer) encs;
   session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename filename));
   session.filename <- filename;
   session.script#buffer#set_modified false


   let save_session session filename encs =
   session.encoding <- List.find (IdeIO.save session.script#buffer filename) encs;
   session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename filename));
   session.filename <- filename;
   session.script#buffer#set_modified false


   let init_session session =
   session.script#buffer#set_modified false;
   session.script#clear_undo;
   session.script#buffer#place_cursor session.script#buffer#start_iter
*)




(*********************************************************************)
(* functions called by the user interface                            *)
(*********************************************************************)
(* XXX - to be used later
   let do_open session filename =
   try
   load_session session filename ["UTF-8";"ISO-8859-1";"ISO-8859-15"];
   init_session session;
   ignore (session_notebook#append_term session)
   with _ -> ()


   let do_save session =
   try
   if session.script#buffer#modified then
   save_session session session.filename [session.encoding]
   with _ -> ()


   let choose_open =
   let last_filename = ref "" in fun session ->
   let open_dialog = GWindow.file_chooser_dialog ~action:`OPEN ~title:"Open file" ~modal:true () in
   let enc_frame = GBin.frame ~label:"File encoding" ~packing:(open_dialog#vbox#pack ~fill:false) () in
   let enc_entry = GEdit.entry ~text:(String.concat " " ["UTF-8";"ISO-8859-1";"ISO-8859-15"]) ~packing:enc_frame#add () in
   let error_dialog = GWindow.message_dialog ~message_type:`ERROR ~modal:true ~buttons:GWindow.Buttons.ok
   ~message:"Invalid encoding, please indicate the encoding to use." () in
   let open_response = function
   | `OPEN -> begin
   match open_dialog#filename with
   | Some fn -> begin
   try
   load_session session fn (Util.split_string_at ' ' enc_entry#text);
   session.analyzed_view <- Some (new analyzed_view session);
   init_session session;
   session_notebook#goto_page (session_notebook#append_term session);
   last_filename := fn
   with
   | Not_found -> open_dialog#misc#hide (); error_dialog#show ()
   | _ ->
   error_dialog#set_markup "Unknown error while loading file, aborting.";
   open_dialog#destroy (); error_dialog#destroy ()
   end
   | None -> ()
   end
   | `DELETE_EVENT -> open_dialog#destroy (); error_dialog#destroy ()
   in
   let _ = open_dialog#connect#response open_response in
   let _ = error_dialog#connect#response (fun x -> error_dialog#misc#hide (); open_dialog#show ()) in
   let filter_any = GFile.filter ~name:"Any" ~patterns:["*"] () in
   let filter_coq = GFile.filter ~name:"Coq source" ~patterns:["*.v"] () in
   open_dialog#add_select_button_stock `OPEN `OPEN;
   open_dialog#add_button_stock `CANCEL `DELETE_EVENT;
   open_dialog#add_filter filter_any;
   open_dialog#add_filter filter_coq;
   ignore(open_dialog#set_filename !last_filename);
   open_dialog#show ()


   let choose_save session =
   let save_dialog = GWindow.file_chooser_dialog ~action:`SAVE ~title:"Save file" ~modal:true () in
   let enc_frame = GBin.frame ~label:"File encoding" ~packing:(save_dialog#vbox#pack ~fill:false) () in
   let enc_entry = GEdit.entry ~text:(String.concat " " [session.encoding;"UTF-8";"ISO-8859-1";"ISO-8859-15"]) ~packing:enc_frame#add () in
   let error_dialog = GWindow.message_dialog ~message_type:`ERROR ~modal:true ~buttons:GWindow.Buttons.ok
   ~message:"Invalid encoding, please indicate the encoding to use." () in
   let save_response = function
   | `SAVE -> begin
   match save_dialog#filename with
   | Some fn -> begin
   try
   save_session session fn (Util.split_string_at ' ' enc_entry#text)
   with
   | Not_found -> save_dialog#misc#hide (); error_dialog#show ()
   | _ ->
   error_dialog#set_markup "Unknown error while saving file, aborting.";
   save_dialog#destroy (); error_dialog#destroy ()
   end
   | None -> ()
   end
   | `DELETE_EVENT -> save_dialog#destroy (); error_dialog#destroy ()
   in
   let _ = save_dialog#connect#response save_response in
   let _ = error_dialog#connect#response (fun x -> error_dialog#misc#hide (); save_dialog#show ()) in
   let filter_any = GFile.filter ~name:"Any" ~patterns:["*"] () in
   let filter_coq = GFile.filter ~name:"Coq source" ~patterns:["*.v"] () in
   save_dialog#add_select_button_stock `SAVE `SAVE;
   save_dialog#add_button_stock `CANCEL `DELETE_EVENT;
   save_dialog#add_filter filter_any;
   save_dialog#add_filter filter_coq;
   ignore(save_dialog#set_filename session.filename);
   save_dialog#show ()
*)

(* Nota: using && here has the advantage of working both under win32 and unix.
   If someday we want the main command to be tried even if the "cd" has failed,
   then we should use " ; " under unix but " & " under win32 (cf. #2363).
*)

let local_cd file =
  "cd " ^ Filename.quote (Filename.dirname file) ^ " && "

let do_print session =
  let av = session.analyzed_view in
  match av#filename with
    |None ->  flash_info "Cannot print: this buffer has no name"
    |Some f_name ->  begin
      let cmd =
        local_cd f_name ^
          !current.cmd_coqdoc ^ " -ps " ^ Filename.quote (Filename.basename f_name) ^
          " | " ^ !current.cmd_print
      in
      let print_window = GWindow.window ~title:"Print" ~modal:true ~position:`CENTER ~wm_class:"CoqIDE" ~wm_name: "CoqIDE"  () in
      let vbox_print = GPack.vbox ~spacing:10 ~border_width:10 ~packing:print_window#add () in
      let _ = GMisc.label ~justify:`LEFT ~text:"Print using the following command:" ~packing:vbox_print#add () in
      let print_entry = GEdit.entry ~text:cmd ~editable:true ~width_chars:80 ~packing:vbox_print#add () in
      let hbox_print = GPack.hbox ~spacing:10 ~packing:vbox_print#add () in
      let print_cancel_button = GButton.button ~stock:`CANCEL ~label:"Cancel" ~packing:hbox_print#add () in
      let print_button  = GButton.button ~stock:`PRINT  ~label:"Print"  ~packing:hbox_print#add () in
      let callback_print () =
        let cmd = print_entry#text in
        let s,_ = run_command av#insert_message cmd in
        flash_info (cmd ^ if s = Unix.WEXITED 0 then " succeeded" else " failed");
        print_window#destroy ()
      in
      ignore (print_cancel_button#connect#clicked ~callback:print_window#destroy) ;
      ignore (print_button#connect#clicked ~callback:callback_print);
      print_window#misc#show ()
    end

let load_file handler f =
  let f = absolute_filename f in
  try
    prerr_endline "Loading file starts";
    if not (Minilib.list_fold_left_i
              (fun i found x -> if found then found else
                  let {analyzed_view=av} = x in
                  (match av#filename with
                    | None -> false
                    | Some fn ->
                      if same_file f fn
                      then (session_notebook#goto_page i; true)
                      else false))
              0 false session_notebook#pages)
    then begin
      prerr_endline "Loading: must open";
      let b = Buffer.create 1024 in
      prerr_endline "Loading: get raw content";
      with_file handler f ~f:(input_channel b);
      prerr_endline "Loading: convert content";
      let s = do_convert (Buffer.contents b) in
      prerr_endline "Loading: create view";
      let session = create_session () in
      session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename f));
      prerr_endline "Loading: adding view";
      let index = session_notebook#append_term session in
      let av = session.analyzed_view in
      prerr_endline "Loading: set filename";
      av#set_filename (Some f);
      prerr_endline "Loading: stats";
      av#update_stats;
      let input_buffer = session.script#buffer in
      prerr_endline "Loading: fill buffer";
      input_buffer#set_text s;
      input_buffer#place_cursor ~where:input_buffer#start_iter;
      prerr_endline ("Loading: switch to view "^ string_of_int index);
      session_notebook#goto_page index;
      prerr_endline "Loading: highlight";
      input_buffer#set_modified false;
      prerr_endline "Loading: clear undo";
      session.script#clear_undo;
      prerr_endline "Loading: success"
    end
  with
    | e -> handler ("Load failed: "^(Printexc.to_string e))

let do_load = load_file flash_info

let saveall_f () =
  List.iter
    (function
       | {script = view ; analyzed_view = av} ->
           begin match av#filename with
             | None -> ()
             | Some f ->
		 ignore (av#save f)
           end
    )  session_notebook#pages

let forbid_quit_to_save () =
    save_pref();
    (if List.exists
      (function
        | {script=view} -> view#buffer#modified
      )
      session_notebook#pages then
      match (GToolbox.question_box ~title:"Quit"
               ~buttons:["Save Named Buffers and Quit";
                         "Quit without Saving";
                         "Don't Quit"]
               ~default:0
               ~icon:
               (let img = GMisc.image () in
                img#set_stock `DIALOG_WARNING;
                img#set_icon_size `DIALOG;
                img#coerce)
               "There are unsaved buffers"
      )
      with 1 -> saveall_f () ; false
        | 2 -> false
        | _ -> true
    else false)||
      (let wait_window =
        GWindow.window ~modal:true ~wm_class:"CoqIde" ~wm_name:"CoqIde" ~kind:`POPUP
          ~title:"Terminating coqtops" () in
      let _ =
        GMisc.label ~text:"Terminating coqtops processes, please wait ..."
          ~packing:wait_window#add () in
      let warning_window =
        GWindow.message_dialog ~message_type:`WARNING ~buttons:GWindow.Buttons.yes_no
          ~message:
	  ("Some coqtops processes are still running.\n" ^
	     "If you quit CoqIDE right now, you may have to kill them manually.\n" ^
	     "Do you want to wait for those processes to terminate ?") () in
      let () = List.iter (fun _ -> session_notebook#remove_page 0) session_notebook#pages in
      let nb_try=ref (0) in
      let () = wait_window#show () in
      let () = while (Coq.coqtop_zombies () <> 0)&&(!nb_try <= 50) do
	incr nb_try;
	Thread.delay 0.1 ;
      done in
	if (!nb_try = 50) then begin
	  wait_window#misc#hide ();
	  match warning_window#run () with
	    | `YES -> warning_window#misc#hide (); true
	    | `NO | `DELETE_EVENT -> false
	end
	else false)

let main files =
  (* Statup preferences *)
  load_pref ();

  (* Main window *)
  let w = GWindow.window
    ~wm_class:"CoqIde" ~wm_name:"CoqIde"
    ~allow_grow:true ~allow_shrink:true
    ~width:!current.window_width ~height:!current.window_height
    ~title:"CoqIde" ()
  in
  (try
     let icon_image = lib_ide_file "coq.png" in
     let icon = GdkPixbuf.from_file icon_image in
     w#set_icon (Some icon)
   with _ -> ());

  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in


  (* Menu bar *)
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in

  (* Toolbar *)
  let toolbar = GButton.toolbar
    ~orientation:`HORIZONTAL
    ~style:`ICONS
    ~tooltips:true
    ~packing:(* handle#add *)
    (vbox#pack ~expand:false ~fill:false)
    ()
  in
  show_toolbar :=
    (fun b -> if b then toolbar#misc#show () else toolbar#misc#hide ());

  let factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/" menubar in
  let accel_group = factory#accel_group in

  (* File Menu *)
  let file_menu = factory#add_submenu "_File" in

  let file_factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/File/" file_menu ~accel_group in

  (* File/Load Menu *)
  let load_m = file_factory#add_item "_New"
    ~key:GdkKeysyms._N in
  let load_f () =
    match select_file_for_save ~title:"Create file" () with
      | None -> ()
      | Some f -> do_load f
  in
  ignore (load_m#connect#activate ~callback:(load_f));

  let load_m = file_factory#add_item "_Open"
    ~key:GdkKeysyms._O in
  let load_f () =
    match select_file_for_open ~title:"Load file" () with
      | None -> ()
      | Some f -> do_load f
  in
  ignore (load_m#connect#activate ~callback:(load_f));

  (* File/Save Menu *)
  let save_m = file_factory#add_item "_Save"
    ~key:GdkKeysyms._S in
  let save_f () =
    let current = session_notebook#current_term in
    try
      (match current.analyzed_view#filename with
        | None ->
          begin match select_file_for_save ~title:"Save file" ()
            with
              | None -> ()
              | Some f ->
                if current.analyzed_view#save_as f then begin
                  current.tab_label#set_text (Filename.basename f);
                  flash_info ("File " ^ f ^ " saved")
                end
                else warning ("Save Failed (check if " ^ f ^ " is writable)")
          end
        | Some f ->
          if current.analyzed_view#save f then
            flash_info ("File " ^ f ^ " saved")
          else warning  ("Save Failed (check if " ^ f ^ " is writable)")

      )
    with
      | e -> warning "Save: unexpected error"
  in
  ignore (save_m#connect#activate ~callback:save_f);

  (* File/Save As Menu *)
  let saveas_m = file_factory#add_item "S_ave as"
  in
  let saveas_f () =
    let current = session_notebook#current_term in
    try (match current.analyzed_view#filename with
      | None ->
        begin match select_file_for_save ~title:"Save file as" ()
          with
            | None -> ()
            | Some f ->
              if current.analyzed_view#save_as f then begin
                current.tab_label#set_text (Filename.basename f);
                flash_info "Saved"
              end
              else flash_info "Save Failed"
        end
      | Some f ->
        begin match select_file_for_save
            ~dir:(ref (Filename.dirname f))
            ~filename:(Filename.basename f)
            ~title:"Save file as" ()
          with
            | None -> ()
            | Some f ->
              if current.analyzed_view#save_as f then begin
                current.tab_label#set_text (Filename.basename f);
                flash_info "Saved"
              end else flash_info "Save Failed"
        end);
    with e -> flash_info "Save Failed"
  in
  ignore (saveas_m#connect#activate ~callback:saveas_f);
  (* XXX *)
  (* File/Save All Menu *)
  let saveall_m = file_factory#add_item "Sa_ve all" in
  (* XXX *)
  ignore (saveall_m#connect#activate ~callback:saveall_f);
  (* XXX *)
  (* File/Revert Menu *)
  let revert_m = file_factory#add_item "_Revert all buffers" in
  let revert_f {analyzed_view = av} =
    (try
       match av#filename,av#stats with
         | Some f,Some stats ->
           let new_stats = Unix.stat f in
           if new_stats.Unix.st_mtime > stats.Unix.st_mtime
           then av#revert
         | Some _, None -> av#revert
         | _ -> ()
     with _ -> av#revert)
  in
  ignore (revert_m#connect#activate ~callback:(fun () -> List.iter revert_f session_notebook#pages));

  (* File/Close Menu *)
  let close_m =
    file_factory#add_item "_Close buffer" ~key:GdkKeysyms._W in
  ignore (close_m#connect#activate ~callback:remove_current_view_page);

  (* File/Print Menu *)
  let _ = file_factory#add_item "_Print..."
    ~key:GdkKeysyms._P
    ~callback:(fun () -> do_print session_notebook#current_term) in

  (* File/Export to Menu *)
  let export_f kind () =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
        flash_info "Cannot print: this buffer has no name"
      | Some f ->
        let basef = Filename.basename f in
        let output =
          let basef_we = try Filename.chop_extension basef with _ -> basef in
          match kind with
            | "latex" -> basef_we ^ ".tex"
            | "dvi" | "ps" | "pdf" | "html" -> basef_we ^ "." ^ kind
            | _ -> assert false
        in
        let cmd =
          local_cd f ^ !current.cmd_coqdoc ^ " --" ^ kind ^
	    " -o " ^ (Filename.quote output) ^ " " ^ (Filename.quote basef)
        in
        let s,_ = run_command av#insert_message cmd in
        flash_info (cmd ^
                      if s = Unix.WEXITED 0
                      then " succeeded"
                      else " failed")
  in
  let file_export_m =  file_factory#add_submenu "E_xport to" in

  let file_export_factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/Export/" file_export_m ~accel_group in
  let _ =
    file_export_factory#add_item "_Html" ~callback:(export_f "html")
  in
  let _ =
    file_export_factory#add_item "_LaTeX" ~callback:(export_f "latex")
  in
  let _ =
    file_export_factory#add_item "_Dvi" ~callback:(export_f "dvi")
  in
  let _ =
    file_export_factory#add_item "_Pdf" ~callback:(export_f "pdf")
  in
  let _ =
    file_export_factory#add_item "_Ps" ~callback:(export_f "ps")
  in

  (* File/Rehighlight Menu *)
  let rehighlight_m = file_factory#add_item "Reh_ighlight" ~key:GdkKeysyms._L in
  ignore (rehighlight_m#connect#activate
            ~callback:(fun () ->
              force_retag
                session_notebook#current_term.script#buffer;
              session_notebook#current_term.analyzed_view#recenter_insert));

  (* File/Quit Menu *)
  let quit_f () = if not (forbid_quit_to_save ()) then exit 0 in
  let _ = file_factory#add_item "_Quit" ~key:GdkKeysyms._Q
    ~callback:quit_f
  in
    ignore (w#event#connect#delete ~callback:(fun _ -> quit_f (); true));

  (* Edit Menu *)
  let edit_menu = factory#add_submenu "_Edit" in
  let edit_f = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/Edit/" edit_menu ~accel_group in
  ignore(edit_f#add_item "_Undo" ~key:GdkKeysyms._u ~callback:
           (fun () -> do_if_not_computing "undo"
             (fun sess ->
               ignore (sess.analyzed_view#without_auto_complete
                         (fun () -> session_notebook#current_term.script#undo) ()))
             [session_notebook#current_term]));
  ignore(edit_f#add_item "_Clear Undo Stack"
               (* ~key:GdkKeysyms._exclam *)
           ~callback:
           (fun () ->
             ignore session_notebook#current_term.script#clear_undo));
  ignore(edit_f#add_separator ());
  let get_active_view_for_cp () =
    let has_sel (i0,i1) = i0#compare i1 <> 0 in
    let current = session_notebook#current_term in
    if has_sel current.script#buffer#selection_bounds
    then current.script#as_view
    else if has_sel current.proof_view#buffer#selection_bounds
    then current.proof_view#as_view
    else current.message_view#as_view
  in
  ignore(edit_f#add_item "Cut" ~key:GdkKeysyms._X ~callback:
           (fun () -> GtkSignal.emit_unit
             (get_active_view_for_cp ())
             ~sgn:GtkText.View.S.cut_clipboard
           ));
  ignore(edit_f#add_item "Copy" ~key:GdkKeysyms._C ~callback:
           (fun () -> GtkSignal.emit_unit
             (get_active_view_for_cp ())
             ~sgn:GtkText.View.S.copy_clipboard));
  ignore(edit_f#add_item "Paste" ~key:GdkKeysyms._V ~callback:
           (fun () ->
             try GtkSignal.emit_unit
                   session_notebook#current_term.script#as_view
                   ~sgn:GtkText.View.S.paste_clipboard
             with _ -> prerr_endline "EMIT PASTE FAILED"));
  ignore (edit_f#add_separator ());


  (*
    let toggle_auto_complete_i =
    edit_f#add_check_item "_Auto Completion"
    ~active:!current.auto_complete
    ~callback:
    in
  *)
  (*
    auto_complete :=
    (fun b -> match session_notebook#current_term.analyzed_view with
    | Some av -> av#set_auto_complete b
    | None -> ());
  *)

  let last_found = ref None in
  let search_backward = ref false in
  let find_w = GWindow.window
    (* ~wm_class:"CoqIde" ~wm_name:"CoqIde" *)
    (* ~allow_grow:true ~allow_shrink:true *)
    (* ~width:!current.window_width ~height:!current.window_height *)
    ~position:`CENTER
    ~title:"CoqIde search/replace" ()
  in
  let find_box = GPack.table
    ~columns:3 ~rows:5
    ~col_spacings:10 ~row_spacings:10 ~border_width:10
    ~homogeneous:false ~packing:find_w#add () in

  let _ =
    GMisc.label ~text:"Find:"
      ~xalign:1.0
      ~packing:(find_box#attach ~left:0 ~top:0 ~fill:`X) ()
  in
  let find_entry = GEdit.entry
    ~editable: true
    ~packing: (find_box#attach ~left:1 ~top:0 ~expand:`X)
    ()
  in
  let _ =
    GMisc.label ~text:"Replace with:"
      ~xalign:1.0
      ~packing:(find_box#attach ~left:0 ~top:1 ~fill:`X) ()
  in
  let replace_entry = GEdit.entry
    ~editable: true
    ~packing: (find_box#attach ~left:1 ~top:1 ~expand:`X)
    ()
  in
  (* let _ =
     GButton.check_button
     ~label:"case sensitive"
     ~active:true
     ~packing: (find_box#attach ~left:1 ~top:2)
     ()
     in
  *)
  let find_backwards_check =
    GButton.check_button
      ~label:"search backwards"
      ~active:!search_backward
      ~packing: (find_box#attach ~left:1 ~top:3)
      ()
  in
  let close_find_button =
    GButton.button
      ~label:"Close"
      ~packing: (find_box#attach ~left:2 ~top:2)
      ()
  in
  let replace_find_button =
    GButton.button
      ~label:"Replace and find"
      ~packing: (find_box#attach ~left:2 ~top:1)
      ()
  in
  let find_again_button =
    GButton.button
      ~label:"_Find again"
      ~packing: (find_box#attach ~left:2 ~top:0)
      ()
  in
  let last_find () =
    let v = session_notebook#current_term.script in
    let b = v#buffer in
    let start,stop =
      match !last_found with
	| None -> let i = b#get_iter_at_mark `INSERT in (i,i)
	| Some(start,stop) ->
	  let start = b#get_iter_at_mark start
	  and stop = b#get_iter_at_mark stop
	  in
	  b#remove_tag Tags.Script.found ~start ~stop;
	  last_found:=None;
	  start,stop
    in
    (v,b,start,stop)
  in
  let do_replace () =
    let v = session_notebook#current_term.script in
    let b = v#buffer in
    match !last_found with
      | None -> ()
      | Some(start,stop) ->
	let start = b#get_iter_at_mark start
	and stop = b#get_iter_at_mark stop
	in
	b#delete ~start ~stop;
	b#insert ~iter:start replace_entry#text;
	last_found:=None
  in
  let find_from (v : Undo.undoable_view)
      (b : GText.buffer) (starti : GText.iter) text =
    prerr_endline ("Searching for " ^ text);
    match (if !search_backward then starti#backward_search text
      else starti#forward_search text)
    with
      | None -> ()
      | Some(start,stop) ->
	b#apply_tag Tags.Script.found ~start ~stop;
	let start = `MARK (b#create_mark start)
	and stop = `MARK (b#create_mark stop)
	in
	v#scroll_to_mark ~use_align:false ~yalign:0.75 ~within_margin:0.25
	  stop;
	last_found := Some(start,stop)
  in
  let do_find () =
    let (v,b,starti,_) = last_find () in
    find_from v b starti find_entry#text
  in
  let do_replace_find () =
    do_replace();
    do_find()
  in
  let close_find () =
    let (v,b,_,stop) = last_find () in
    b#place_cursor ~where:stop;
    find_w#misc#hide();
    v#coerce#misc#grab_focus()
  in
  to_do_on_page_switch :=
    (fun i -> if find_w#misc#visible then close_find())::
    !to_do_on_page_switch;
  let find_again () =
    let (v,b,start,_) = last_find () in
    let start =
      if !search_backward
      then start#backward_chars 1
      else start#forward_chars 1
    in
    find_from v b start find_entry#text
  in
  let click_on_backward () =
    search_backward := not !search_backward
  in
  let key_find ev =
    let s = GdkEvent.Key.state ev and k = GdkEvent.Key.keyval ev in
    if k = GdkKeysyms._Escape then
      begin
	let (v,b,_,stop) = last_find () in
	find_w#misc#hide();
	v#coerce#misc#grab_focus();
	true
      end
    else if k = GdkKeysyms._Escape then
      begin
	close_find();
	true
      end
    else if k = GdkKeysyms._Return ||
	   List.mem `CONTROL s && k = GdkKeysyms._f then
      begin
	find_again ();
	true
      end
    else if List.mem `CONTROL s && k = GdkKeysyms._b then
      begin
	find_backwards_check#set_active (not !search_backward);
	true
      end
    else false (* to let default callback execute *)
  in
  let find_f ~backward () =
    let save_dir = !search_backward in
    search_backward := backward;
    find_w#show ();
    find_w#present ();
    find_entry#misc#grab_focus ();
    search_backward := save_dir
  in
  let _ = edit_f#add_item "_Find in buffer"
    ~key:GdkKeysyms._F
    ~callback:(find_f ~backward:false)
  in
  let _ = edit_f#add_item "Find _backwards"
    ~key:GdkKeysyms._B
    ~callback:(find_f ~backward:true)
  in
  let _ = find_again_button#connect#clicked find_again in
  let _ = close_find_button#connect#clicked close_find in
  let _ = replace_find_button#connect#clicked do_replace_find in
  let _ = find_backwards_check#connect#clicked click_on_backward in
  let _ = find_entry#connect#changed do_find in
  let _ = find_entry#event#connect#key_press ~callback:key_find in
  let _ = find_w#event#connect#delete ~callback:(fun _ -> find_w#misc#hide(); true) in
  (*
    let search_if = edit_f#add_item "Search _forward"
    ~key:GdkKeysyms._greater
    in
    let search_ib = edit_f#add_item "Search _backward"
    ~key:GdkKeysyms._less
    in
  *)
  (*
    let complete_i = edit_f#add_item "_Complete"
    ~key:GdkKeysyms._comma
    ~callback:
    (do_if_not_computing
    (fun b ->
    let v = session_notebook#current_term.analyzed_view

    in v#complete_at_offset
    ((v#view#buffer#get_iter `SEL_BOUND)#offset)
    ))
    in
    complete_i#misc#set_state `INSENSITIVE;
  *)

  ignore(edit_f#add_item "Complete Word" ~key:GdkKeysyms._slash ~callback:
	   (fun () ->
	     ignore (
	       let av = session_notebook#current_term.analyzed_view in
	       av#complete_at_offset (av#get_insert)#offset
	     )));

  ignore(edit_f#add_separator ());
  (* external editor *)
  let _ =
    edit_f#add_item "External editor" ~callback:
      (fun () ->
	let av = session_notebook#current_term.analyzed_view in
	match av#filename with
	  | None -> warning "Call to external editor available only on named files"
	  | Some f ->
	    save_f ();
	    let com = Minilib.subst_command_placeholder !current.cmd_editor (Filename.quote f) in
	    let _ = run_command av#insert_message com in
	    av#revert)
  in
  let _ = edit_f#add_separator () in
  (* Preferences *)
  let reset_revert_timer () =
    disconnect_revert_timer ();
    if !current.global_auto_revert then
      revert_timer := Some
	(GMain.Timeout.add ~ms:!current.global_auto_revert_delay
	   ~callback:
	   (fun () ->
	     do_if_not_computing "revert" (sync revert_f) session_notebook#pages;
	     true))
  in reset_revert_timer (); (* to enable statup preferences timer *)
  (* XXX *)
  let auto_save_f {analyzed_view = av} =
    (try
       av#auto_save
     with _ -> ())
  in

  let reset_auto_save_timer () =
    disconnect_auto_save_timer ();
    if !current.auto_save then
      auto_save_timer := Some
	(GMain.Timeout.add ~ms:!current.auto_save_delay
	   ~callback:
	   (fun () ->
	     do_if_not_computing "autosave" (sync auto_save_f) session_notebook#pages;
	     true))
  in reset_auto_save_timer (); (* to enable statup preferences timer *)


  let _ =
    edit_f#add_item "_Preferences"
      ~callback:(fun () -> configure ~apply:update_notebook_pos (); reset_revert_timer ())
  in
  (*
    let save_prefs_m =
    configuration_factory#add_item "_Save preferences"
    ~callback:(fun () -> save_pref ())
    in
  *)
  (* Navigation Menu *)
  let navigation_menu =  factory#add_submenu "_Navigation" in
  let navigation_factory =
    new GMenu.factory navigation_menu
      ~accel_path:"<CoqIde MenuBar>/Navigation/"
      ~accel_group
      ~accel_modi:!current.modifier_for_navigation
  in
  let do_or_activate f () =
    do_if_not_computing "do_or_activate"
      (fun current ->
        let av = current.analyzed_view in
        ignore (f av);
        pop_info ();
        push_info
          (match Coq.current_status !(current.toplvl) with
            | Ide_intf.Fail (l,str) ->
	      "Oops, problem while fetching coq status."
            | Ide_intf.Good str -> str)
      )
      [session_notebook#current_term]
  in
  let add_to_menu_toolbar text ~tooltip ?key ~callback icon =
    begin
      match key with None -> ()
	| Some key -> ignore (navigation_factory#add_item text ~key ~callback)
    end;
    ignore (toolbar#insert_button
	      ~tooltip
	      (* ~text:tooltip*)
	      ~icon:(stock_to_widget ~size:`LARGE_TOOLBAR icon)
	      ~callback
	      ())
  in
  add_to_menu_toolbar
    "_Save"
    ~tooltip:"Save current buffer"
    ~callback:save_f
    `SAVE;
  add_to_menu_toolbar
    "_Close"
    ~tooltip:"Close current buffer"
    ~callback:remove_current_view_page
    `CLOSE;
  add_to_menu_toolbar
    "_Forward"
    ~tooltip:"Forward one command"
    ~key:GdkKeysyms._Down
    ~callback:(do_or_activate (fun a -> a#process_next_phrase true true true ))
    `GO_DOWN;
  add_to_menu_toolbar "_Backward"
    ~tooltip:"Backward one command"
    ~key:GdkKeysyms._Up
    ~callback:(do_or_activate (fun a -> a#undo_last_step))
    `GO_UP;
  add_to_menu_toolbar
    "_Go to"
    ~tooltip:"Go to cursor"
    ~key:GdkKeysyms._Right
    ~callback:(do_or_activate (fun a-> a#go_to_insert))
    `JUMP_TO;
  add_to_menu_toolbar
    "_Start"
    ~tooltip:"Restart Coq"
    ~key:GdkKeysyms._Home
    ~callback:force_reset_initial
    `GOTO_TOP;
  add_to_menu_toolbar
    "_End"
    ~tooltip:"Go to end"
    ~key:GdkKeysyms._End
    ~callback:(do_or_activate (fun a -> a#process_until_end_or_error))
    `GOTO_BOTTOM;
  add_to_menu_toolbar "_Interrupt"
    ~tooltip:"Interrupt computations"
    ~key:GdkKeysyms._Break
    ~callback:break
    `STOP;
  add_to_menu_toolbar "_Hide"
    ~tooltip:"Hide proof"
    ~key:GdkKeysyms._h
    ~callback:(fun x ->
      let sess = session_notebook#current_term in
      toggle_proof_visibility sess.script#buffer
        sess.analyzed_view#get_insert)
    `MISSING_IMAGE;
  add_to_menu_toolbar "_Previous"
    ~tooltip:"Previous occurrence"
    ~key:GdkKeysyms._less
    ~callback:(do_or_activate (fun a ->
      a#go_to_prev_occ_of_cur_word))
    `GO_BACK;
  add_to_menu_toolbar "_Next"
    ~tooltip:"Next occurrence"
    ~key:GdkKeysyms._greater
    ~callback:(do_or_activate (fun a ->
      a#go_to_next_occ_of_cur_word))
    `GO_FORWARD;

  (* Tactics Menu *)
  let tactics_menu =  factory#add_submenu "_Try Tactics" in
  let tactics_factory =
    new GMenu.factory tactics_menu
      ~accel_path:"<CoqIde MenuBar>/Tactics/"
      ~accel_group
      ~accel_modi:!current.modifier_for_tactics
  in
  let do_if_active f () =
    do_if_not_computing "do_if_active"
      (fun sess -> ignore (f sess.analyzed_view))
      [session_notebook#current_term] in

  ignore (tactics_factory#add_item "_auto"
	    ~key:GdkKeysyms._a
	    ~callback:(do_if_active (fun a -> a#insert_command "progress auto.\n" "auto.\n"))
  );
  ignore (tactics_factory#add_item "_auto with *"
	    ~key:GdkKeysyms._asterisk
	    ~callback:(do_if_active (fun a -> a#insert_command
	      "progress auto with *.\n"
	      "auto with *.\n")));
  ignore (tactics_factory#add_item "_eauto"
	    ~key:GdkKeysyms._e
	    ~callback:(do_if_active (fun a -> a#insert_command
	      "progress eauto.\n"
	      "eauto.\n"))
  );
  ignore (tactics_factory#add_item "_eauto with *"
	    ~key:GdkKeysyms._ampersand
	    ~callback:(do_if_active (fun a -> a#insert_command
	      "progress eauto with *.\n"
	      "eauto with *.\n"))
  );
  ignore (tactics_factory#add_item "_intuition"
	    ~key:GdkKeysyms._i
	    ~callback:(do_if_active (fun a -> a#insert_command
	      "progress intuition.\n"
	      "intuition.\n"))
  );
  ignore (tactics_factory#add_item "_omega"
	    ~key:GdkKeysyms._o
	    ~callback:(do_if_active (fun a -> a#insert_command
	      "omega.\n" "omega.\n"))
  );
  ignore (tactics_factory#add_item "_simpl"
	    ~key:GdkKeysyms._s
	    ~callback:(do_if_active (fun a -> a#insert_command "progress simpl.\n" "simpl.\n" ))
  );
  ignore (tactics_factory#add_item "_tauto"
	    ~key:GdkKeysyms._p
	    ~callback:(do_if_active (fun a -> a#insert_command "tauto.\n" "tauto.\n" ))
  );
  ignore (tactics_factory#add_item "_trivial"
	    ~key:GdkKeysyms._v
	    ~callback:(do_if_active( fun a -> a#insert_command "progress trivial.\n"  "trivial.\n" ))
  );


  ignore (toolbar#insert_button
	    ~tooltip:"Proof Wizard"
	    ~text:"Wizard"
	    ~icon:(stock_to_widget ~size:`LARGE_TOOLBAR `DIALOG_INFO)
	    ~callback:(do_if_active (fun a -> a#tactic_wizard
	      !current.automatic_tactics
	    ))
	    ());



  ignore (tactics_factory#add_item "<Proof _Wizard>"
	    ~key:GdkKeysyms._dollar
	    ~callback:(do_if_active (fun a -> a#tactic_wizard
	      !current.automatic_tactics
	    ))
  );

  ignore (tactics_factory#add_separator ());
  let add_simple_template (factory: GMenu.menu GMenu.factory)
      (menu_text, text) =
    let text =
      let l = String.length text - 1 in
      if String.get text l = '.'
      then text ^"\n"
      else text ^" "
    in
    ignore (factory#add_item menu_text
	      ~callback:
	      (fun () -> let {script = view } = session_notebook#current_term in
			 ignore (view#buffer#insert_interactive text)))
  in
  List.iter
    (fun l ->
      match l with
	| [] -> ()
	| [s] -> add_simple_template tactics_factory ("_"^s, s)
	| s::_ ->
	  let a = "_@..." in
	  a.[1] <- s.[0];
	  let f = tactics_factory#add_submenu a in
	  let ff = new GMenu.factory f ~accel_group in
	  List.iter
	    (fun x ->
	      add_simple_template
		ff
		((String.sub x 0 1)^
		    "_"^
		    (String.sub x 1 (String.length x - 1)),
		 x))
	    l
    )
    Coq_commands.tactics;

  (* Templates Menu *)
  let templates_menu =  factory#add_submenu "Te_mplates" in
  let templates_factory = new GMenu.factory templates_menu
    ~accel_path:"<CoqIde MenuBar>/Templates/"
    ~accel_group
    ~accel_modi:!current.modifier_for_templates
  in
  let add_complex_template (menu_text, text, offset, len, key) =
    (* Templates/Lemma *)
    let callback () =
      let {script = view } = session_notebook#current_term in
      if view#buffer#insert_interactive text then begin
	let iter = view#buffer#get_iter_at_mark `INSERT in
	ignore (iter#nocopy#backward_chars offset);
	view#buffer#move_mark `INSERT ~where:iter;
	ignore (iter#nocopy#backward_chars len);
	view#buffer#move_mark `SEL_BOUND ~where:iter;
      end in
    ignore (templates_factory#add_item menu_text ~callback ?key)
  in
  add_complex_template
    ("_Lemma __", "Lemma new_lemma : .\nIdeproof.\n\nSave.\n",
     19, 9, Some GdkKeysyms._L);
  add_complex_template
    ("_Theorem __", "Theorem new_theorem : .\nIdeproof.\n\nSave.\n",
     19, 11, Some GdkKeysyms._T);
  add_complex_template
    ("_Definition __", "Definition ident := .\n",
     6, 5, Some GdkKeysyms._D);
  add_complex_template
    ("_Inductive __", "Inductive ident : :=\n  | : .\n",
     14, 5, Some GdkKeysyms._I);
  add_complex_template
    ("_Fixpoint __", "Fixpoint ident (_ : _) {struct _} : _ :=\n.\n",
     29, 5, Some GdkKeysyms._F);
  add_complex_template("_Scheme __",
		       "Scheme new_scheme := Induction for _ Sort _\
\nwith _ := Induction for _ Sort _.\n",61,10, Some GdkKeysyms._S);

  (* Template for match *)
  let callback () =
    let w = get_current_word () in
    let cur_ct = !(session_notebook#current_term.toplvl) in
    try
      match Coq.make_cases cur_ct w with
        | Ide_intf.Fail _ -> raise Not_found
        | Ide_intf.Good cases ->
          let print c = function
            | [x] -> Format.fprintf c "  | %s => _@\n" x
            | x::l -> Format.fprintf c "  | (%s%a) => _@\n" x
              (print_list (fun c s -> Format.fprintf c " %s" s)) l
            | [] -> assert false
          in
          let b = Buffer.create 1024 in
          let fmt = Format.formatter_of_buffer b in
          Format.fprintf fmt "@[match var with@\n%aend@]@."
            (print_list print) cases;
          let s = Buffer.contents b in
          prerr_endline s;
          let {script = view } = session_notebook#current_term in
          ignore (view#buffer#delete_selection ());
          let m = view#buffer#create_mark
            (view#buffer#get_iter `INSERT)
          in
          if view#buffer#insert_interactive s then
            let i = view#buffer#get_iter (`MARK m) in
            let _ = i#nocopy#forward_chars 9 in
            view#buffer#place_cursor ~where:i;
            view#buffer#move_mark ~where:(i#backward_chars 3)
              `SEL_BOUND
    with Not_found -> flash_info "Not an inductive type"
  in
  ignore (templates_factory#add_item "match ..."
	    ~key:GdkKeysyms._C
	    ~callback
  );

  (*
    let add_simple_template (factory: GMenu.menu GMenu.factory)
    (menu_text, text) =
    let text =
    let l = String.length text - 1 in
    if String.get text l = '.'
    then text ^"\n"
    else text ^" "
    in
    ignore (factory#add_item menu_text
    ~callback:
    (fun () -> let {view = view } = session_notebook#current_term in
    ignore (view#buffer#insert_interactive text)))
    in
  *)
  ignore (templates_factory#add_separator ());
  (*
    List.iter (add_simple_template templates_factory)
    [ "_auto", "auto ";
    "_auto with *", "auto with * ";
    "_eauto", "eauto ";
    "_eauto with *", "eauto with * ";
    "_intuition", "intuition ";
    "_omega", "omega ";
    "_simpl", "simpl ";
    "_tauto", "tauto ";
    "tri_vial", "trivial ";
    ];
    ignore (templates_factory#add_separator ());
  *)
  List.iter
    (fun l ->
      match l with
	| [] -> ()
	| [s] -> add_simple_template templates_factory ("_"^s, s)
	| s::_ ->
	  let a = "_@..." in
	  a.[1] <- s.[0];
	  let f = templates_factory#add_submenu a in
	  let ff = new GMenu.factory f ~accel_group in
	  List.iter
	    (fun x ->
	      add_simple_template
		ff
		((String.sub x 0 1)^
		    "_"^
		    (String.sub x 1 (String.length x - 1)),
		 x))
	    l
    )
    Coq_commands.commands;

  (* Queries Menu *)
  let queries_menu =  factory#add_submenu "_Queries" in
  let queries_factory = new GMenu.factory queries_menu ~accel_group
    ~accel_path:"<CoqIde MenuBar>/Queries"
    ~accel_modi:[]
  in

  (* Command/Show commands *)
  let _ =
    queries_factory#add_item "_SearchAbout " ~key:GdkKeysyms._F2
      ~callback:(fun () -> let term = get_current_word () in
			   session_notebook#current_term.command#new_command
			     ~command:"SearchAbout"
			     ~term
			     ())
  in
  let _ =
    queries_factory#add_item "_Check " ~key:GdkKeysyms._F3
      ~callback:(fun () -> let term = get_current_word () in
			   session_notebook#current_term.command#new_command
			     ~command:"Check"
			     ~term
			     ())
  in
  let _ =
    queries_factory#add_item "_Print " ~key:GdkKeysyms._F4
      ~callback:(fun () -> let term = get_current_word () in
			   session_notebook#current_term.command#new_command
			     ~command:"Print"
			     ~term
			     ())
  in
  let _ =
    queries_factory#add_item "_About " ~key:GdkKeysyms._F5
      ~callback:(fun () -> let term = get_current_word () in
			   session_notebook#current_term.command#new_command
			     ~command:"About"
			     ~term
			     ())
  in
  let _ =
    queries_factory#add_item "_Locate"
      ~callback:(fun () -> let term = get_current_word () in
			   session_notebook#current_term.command#new_command
			     ~command:"Locate"
			     ~term
			     ())
  in
  let _ =
    queries_factory#add_item "_Whelp Locate"
      ~callback:(fun () -> let term = get_current_word () in
			   session_notebook#current_term.command#new_command
			     ~command:"Whelp Locate"
			     ~term
			     ())
  in

  (* Display menu *)

  let display_menu =  factory#add_submenu "_Display" in
  let view_factory =  new GMenu.factory display_menu
    ~accel_path:"<CoqIde MenuBar>/Display/"
    ~accel_group
    ~accel_modi:!current.modifier_for_display
  in
  let _ =
    List.map
      (fun (opts,text,key,dflt) ->
        view_factory#add_check_item ~key ~active:dflt text
          ~callback:(fun v -> do_or_activate (fun a ->
            ignore (setopts !(session_notebook#current_term.toplvl) opts v);
            a#show_goals) ()))
      print_items
  in

  (* Externals *)
  let externals_menu =  factory#add_submenu "_Compile" in
  let externals_factory = new GMenu.factory externals_menu
    ~accel_path:"<CoqIde MenuBar>/Compile/"
    ~accel_group
    ~accel_modi:[]
  in

  (* Command/Compile Menu *)
  let compile_f () =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    save_f ();
    match av#filename with
      | None ->
	flash_info "Active buffer has no name"
      | Some f ->
	let cmd = !current.cmd_coqc ^ " -I "
	  ^ (Filename.quote (Filename.dirname f))
	  ^ " " ^ (Filename.quote f) in
	let s,res = run_command av#insert_message cmd in
	if s = Unix.WEXITED 0 then
	  flash_info (f ^ " successfully compiled")
	else begin
	  flash_info (f ^ " failed to compile");
	  av#process_until_end_or_error;
	  av#insert_message "Compilation output:\n";
	  av#insert_message res
	end
  in
  let _ =
    externals_factory#add_item "_Compile Buffer" ~callback:compile_f
  in

  (* Command/Make Menu *)
  let make_f () =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
	flash_info "Cannot make: this buffer has no name"
      | Some f ->
	let cmd = local_cd f ^ !current.cmd_make in

	(*
	  save_f ();
	*)
	av#insert_message "Command output:\n";
	let s,res = run_command av#insert_message cmd in
	last_make := res;
	last_make_index := 0;
	flash_info (!current.cmd_make ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let _ = externals_factory#add_item "_Make"
    ~key:GdkKeysyms._F6
    ~callback:make_f
  in


  (* Compile/Next Error *)
  let next_error () =
    try
      let file,line,start,stop,error_msg = search_next_error () in
      do_load file;
      let v = session_notebook#current_term in
      let av = v.analyzed_view in
      let input_buffer = v.script#buffer in
      (*
	let init = input_buffer#start_iter in
	let i = init#forward_lines (line-1) in
      *)
      (*
	let convert_pos = byte_offset_to_char_offset phrase in
	let start = convert_pos start in
	let stop = convert_pos stop in
      *)
      (*
	let starti = i#forward_chars start in
	let stopi = i#forward_chars stop in
      *)
      let starti = input_buffer#get_iter_at_byte ~line:(line-1) start in
      let stopi = input_buffer#get_iter_at_byte ~line:(line-1) stop in
      input_buffer#apply_tag Tags.Script.error
	~start:starti
	~stop:stopi;
      input_buffer#place_cursor ~where:starti;
      av#set_message error_msg;
      v.script#misc#grab_focus ()
    with Not_found ->
      last_make_index := 0;
      let v = session_notebook#current_term in
      let av = v.analyzed_view in
      av#set_message "No more errors.\n"
  in
  let _ =
    externals_factory#add_item "_Next error"
      ~key:GdkKeysyms._F7
      ~callback:next_error in


  (* Command/CoqMakefile Menu*)
  let coq_makefile_f () =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
	flash_info "Cannot make makefile: this buffer has no name"
      | Some f ->
	let cmd = local_cd f ^ !current.cmd_coqmakefile in
	let s,res = run_command av#insert_message cmd in
	flash_info
	  (!current.cmd_coqmakefile ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let _ = externals_factory#add_item "_Make makefile" ~callback:coq_makefile_f
  in
  (* Windows Menu *)
  let configuration_menu = factory#add_submenu "_Windows" in
  let configuration_factory = new GMenu.factory configuration_menu
    ~accel_path:"<CoqIde MenuBar>/Windows"
    ~accel_modi:[]
    ~accel_group
  in
  let _ =
    configuration_factory#add_item
      "Show/Hide _Query Pane"
      ~key:GdkKeysyms._Escape
      ~callback:(fun () ->
        let ccw = session_notebook#current_term.command in
        if ccw#frame#misc#visible then
          ccw#frame#misc#hide ()
        else
          ccw#frame#misc#show ())
  in
  let _ =
    configuration_factory#add_check_item
      "Show/Hide _Toolbar"
      ~callback:(fun _ ->
	!current.show_toolbar <- not !current.show_toolbar;
	!show_toolbar !current.show_toolbar)
  in
  let _ =
    configuration_factory#add_item
      "Detach _View"
      ~callback:
      (fun () -> do_if_not_computing "detach view"
	(function {script=v;analyzed_view=av} ->
          let w = GWindow.window ~show:true
            ~width:(!current.window_width*2/3)
            ~height:(!current.window_height*2/3)
            ~position:`CENTER
            ~title:(match av#filename with
              | None -> "*Unnamed*"
              | Some f -> f)
            ()
          in
          let sb = GBin.scrolled_window
            ~packing:w#add ()
          in
          let nv = GText.view
            ~buffer:v#buffer
            ~packing:sb#add
            ()
          in
          nv#misc#modify_font
            !current.text_font;
          ignore (w#connect#destroy
                    ~callback:
                    (fun () -> av#remove_detached_view w));
          av#add_detached_view w)
        [session_notebook#current_term])
  in

  (* Help Menu *)
  let help_menu = factory#add_submenu "_Help" in
  let help_factory = new GMenu.factory help_menu
    ~accel_path:"<CoqIde MenuBar>/Help/"
    ~accel_modi:[]
    ~accel_group in
  let _ = help_factory#add_item "Browse Coq _Manual"
    ~callback:
    (fun () ->
      let av = session_notebook#current_term.analyzed_view in
      browse av#insert_message (doc_url ())) in
  let _ = help_factory#add_item "Browse Coq _Library"
    ~callback:
    (fun () ->
      let av = session_notebook#current_term.analyzed_view in
      browse av#insert_message !current.library_url) in
  let _ =
    help_factory#add_item "Help for _keyword" ~key:GdkKeysyms._F1
      ~callback:(fun () ->
	let av = session_notebook#current_term.analyzed_view in
	av#help_for_keyword ())
  in
  let _ = help_factory#add_separator () in
  let about_m = help_factory#add_item "_About" in
  (* End of menu *)

  (* The vertical Separator between Scripts and Goals *)
  vbox#pack ~expand:true session_notebook#coerce;
  update_notebook_pos ();
  let nb = session_notebook in
  let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  lower_hbox#pack ~expand:true status#coerce;
  let search_lbl = GMisc.label ~text:"Search:"
    ~show:false
    ~packing:(lower_hbox#pack ~expand:false) ()
  in
  let search_history = ref [] in
  let search_input = GEdit.combo ~popdown_strings:!search_history
    ~enable_arrow_keys:true
    ~show:false
    ~packing:(lower_hbox#pack ~expand:false) ()
  in
  search_input#disable_activate ();
  let ready_to_wrap_search = ref false in

  let start_of_search = ref None in
  let start_of_found = ref None in
  let end_of_found = ref None in
  let search_forward = ref true in
  let matched_word = ref None in

  let memo_search () =
    matched_word := Some search_input#entry#text
  in
  let end_search () =
    prerr_endline "End Search";
    memo_search ();
    let v = session_notebook#current_term.script in
    v#buffer#move_mark `SEL_BOUND ~where:(v#buffer#get_iter_at_mark `INSERT);
    v#coerce#misc#grab_focus ();
    search_input#entry#set_text "";
    search_lbl#misc#hide ();
    search_input#misc#hide ()
  in
  let end_search_focus_out () =
    prerr_endline "End Search(focus out)";
    memo_search ();
    let v = session_notebook#current_term.script in
    v#buffer#move_mark `SEL_BOUND ~where:(v#buffer#get_iter_at_mark `INSERT);
    search_input#entry#set_text "";
    search_lbl#misc#hide ();
    search_input#misc#hide ()
  in
  ignore (search_input#entry#connect#activate ~callback:end_search);
  ignore (search_input#entry#event#connect#key_press
	    ~callback:(fun k -> let kv = GdkEvent.Key.keyval k in
				if
				  kv = GdkKeysyms._Right
				  || kv = GdkKeysyms._Up
				    || kv = GdkKeysyms._Left
				      || (kv = GdkKeysyms._g
					 && (List.mem `CONTROL (GdkEvent.Key.state k)))
				then end_search ();
				false));
  ignore (search_input#entry#event#connect#focus_out
	    ~callback:(fun _ -> end_search_focus_out (); false));
  to_do_on_page_switch :=
    (fun i ->
      start_of_search := None;
      ready_to_wrap_search:=false)::!to_do_on_page_switch;

  (* TODO : make it work !!! *)
  let rec search_f () =
    search_lbl#misc#show ();
    search_input#misc#show ();

    prerr_endline "search_f called";
    if !start_of_search = None then begin
      (* A full new search is starting *)
      start_of_search :=
	Some (session_notebook#current_term.script#buffer#create_mark
		(session_notebook#current_term.script#buffer#get_iter_at_mark `INSERT));
      start_of_found := !start_of_search;
      end_of_found := !start_of_search;
      matched_word := Some "";
    end;
    let txt = search_input#entry#text in
    let v = session_notebook#current_term.script in
    let iit = v#buffer#get_iter_at_mark `SEL_BOUND
    and insert_iter = v#buffer#get_iter_at_mark `INSERT
    in
    prerr_endline ("SELBOUND="^(string_of_int iit#offset));
    prerr_endline ("INSERT="^(string_of_int insert_iter#offset));

    (match
	if !search_forward then iit#forward_search txt
	else let npi = iit#forward_chars (Glib.Utf8.length txt) in
	     match
	       (npi#offset = (v#buffer#get_iter_at_mark `INSERT)#offset),
	       (let t = iit#get_text ~stop:npi in
		flash_info (t^"\n"^txt);
		t = txt)
	     with
	       | true,true ->
		 (flash_info "T,T";iit#backward_search txt)
	       | false,true -> flash_info "F,T";Some (iit,npi)
	       | _,false ->
		 (iit#backward_search txt)

     with
       | None ->
	 if !ready_to_wrap_search then begin
	   ready_to_wrap_search := false;
	   flash_info "Search wrapped";
	   v#buffer#place_cursor
	     ~where:(if !search_forward then v#buffer#start_iter else
		 v#buffer#end_iter);
	   search_f ()
	 end else begin
	   if !search_forward then flash_info "Search at end"
	   else flash_info "Search at start";
	   ready_to_wrap_search := true
	 end
       | Some (start,stop) ->
	 prerr_endline "search: before moving marks";
	 prerr_endline ("SELBOUND="^(string_of_int (v#buffer#get_iter_at_mark `SEL_BOUND)#offset));
	 prerr_endline ("INSERT="^(string_of_int (v#buffer#get_iter_at_mark `INSERT)#offset));

	 v#buffer#move_mark `SEL_BOUND ~where:start;
	 v#buffer#move_mark `INSERT ~where:stop;
	 prerr_endline "search: after moving marks";
	 prerr_endline ("SELBOUND="^(string_of_int (v#buffer#get_iter_at_mark `SEL_BOUND)#offset));
	 prerr_endline ("INSERT="^(string_of_int (v#buffer#get_iter_at_mark `INSERT)#offset));
	 v#scroll_to_mark `SEL_BOUND
    )
  in
  ignore (search_input#entry#event#connect#key_release
	    ~callback:
	    (fun ev ->
	      if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then begin
		let v = session_notebook#current_term.script in
		(match !start_of_search with
		  | None ->
		    prerr_endline "search_key_rel: Placing sel_bound";
		    v#buffer#move_mark
		      `SEL_BOUND
		      ~where:(v#buffer#get_iter_at_mark `INSERT)
		  | Some mk -> let it = v#buffer#get_iter_at_mark
				 (`MARK mk) in
			       prerr_endline "search_key_rel: Placing cursor";
			       v#buffer#place_cursor ~where:it;
			       start_of_search := None
		);
		search_input#entry#set_text "";
		v#coerce#misc#grab_focus ();
	      end;
	      false
	    ));
  ignore (search_input#entry#connect#changed ~callback:search_f);
  push_info "Ready";
  (* Location display *)
  let l = GMisc.label
    ~text:"Line:     1 Char:   1"
    ~packing:lower_hbox#pack () in
  l#coerce#misc#set_name "location";
  set_location := l#set_text;
  (* Progress Bar *)
  lower_hbox#pack pbar#coerce;
  pbar#set_text "CoqIde started";
  (* XXX *)
  change_font :=
    (fun fd ->
      List.iter
	(fun {script=view; proof_view=prf_v; message_view=msg_v} ->
          view#misc#modify_font fd;
          prf_v#misc#modify_font fd;
          msg_v#misc#modify_font fd
        )
	session_notebook#pages;
    );
  let about_full_string =
    "\nCoq is developed by the Coq Development Team\
     \n(INRIA - CNRS - LIX - LRI - PPS)\
     \nWeb site: " ^ Coq_config.wwwcoq ^
    "\nFeature wish or bug report: http://coq.inria.fr/bugs/\
     \n\
     \nCredits for CoqIDE, the Integrated Development Environment for Coq:\
     \n\
     \nMain author  : Benjamin Monate\
     \nContributors : Jean-Christophe Filliâtre\
     \n               Pierre Letouzey, Claude Marché\
     \n               Bruno Barras, Pierre Corbineau\
     \n               Julien Narboux, Hugo Herbelin, ... \
     \n\
     \nVersion information\
     \n-------------------\
     \n"
  in
  let initial_about (b:GText.buffer) =
    let initial_string =
      "Welcome to CoqIDE, an Integrated Development Environment for Coq\n"
    in
    let coq_version = Coq.short_version () in
    b#insert ~iter:b#start_iter "\n\n";
    if Glib.Utf8.validate ("You are running " ^ coq_version) then
      b#insert ~iter:b#start_iter ("You are running " ^ coq_version);
    if Glib.Utf8.validate initial_string then
      b#insert ~iter:b#start_iter initial_string;
    (try
       let image = lib_ide_file "coq.png" in
       let startup_image = GdkPixbuf.from_file image in
       b#insert ~iter:b#start_iter "\n\n";
       b#insert_pixbuf ~iter:b#start_iter ~pixbuf:startup_image;
       b#insert ~iter:b#start_iter "\n\n\t\t   "
     with _ -> ())
  in

  let about (b:GText.buffer) =
    (try
       let image = lib_ide_file "coq.png" in
       let startup_image = GdkPixbuf.from_file image in
       b#insert ~iter:b#start_iter "\n\n";
       b#insert_pixbuf ~iter:b#start_iter ~pixbuf:startup_image;
       b#insert ~iter:b#start_iter "\n\n\t\t   "
     with _ -> ());
    if Glib.Utf8.validate about_full_string
    then b#insert about_full_string;
    let coq_version = Coq.version () in
    if Glib.Utf8.validate coq_version
    then b#insert coq_version

  in
  w#add_accel_group accel_group;
  (* Remove default pango menu for textviews *)
  w#show ();
  ignore (about_m#connect#activate
	    ~callback:(fun () -> let prf_v = session_notebook#current_term.proof_view in
                                 prf_v#buffer#set_text ""; about prf_v#buffer));
  (*

  *)
  resize_window := (fun () ->
    w#resize
      ~width:!current.window_width
      ~height:!current.window_height);
  ignore(nb#connect#switch_page
	   ~callback:
	   (fun i ->
	     prerr_endline ("switch_page: starts " ^ string_of_int i);
	     List.iter (function f -> f i) !to_do_on_page_switch;
	     prerr_endline "switch_page: success")
  );
  if List.length files >=1 then
    begin
      List.iter (fun f ->
	if Sys.file_exists f then do_load f else
          let f = if Filename.check_suffix f ".v" then f else f^".v" in
	  load_file (fun s -> print_endline s; exit 1) f)
        files;
      session_notebook#goto_page 0;
    end
  else
    begin
      let session = create_session () in
      let index = session_notebook#append_term session in
      session_notebook#goto_page index;
    end;
  initial_about session_notebook#current_term.proof_view#buffer;
  !show_toolbar !current.show_toolbar;
  session_notebook#current_term.script#misc#grab_focus ()

;;

(* This function check every half of second if GeoProof has send
   something on his private clipboard *)

let rec check_for_geoproof_input () =
  let cb_Dr = GData.clipboard (Gdk.Atom.intern "_GeoProof") in
  while true do
    Thread.delay 0.1;
    let s = cb_Dr#text in
    (match s with
	Some s ->
	  if s <> "Ack" then
	    session_notebook#current_term.script#buffer#insert (s^"\n");
	  cb_Dr#set_text "Ack"
      | None -> ()
    );
  (* cb_Dr#clear does not work so i use : *)
  (* cb_Dr#set_text "Ack" *)
  done

let default_coqtop_path () =
  let prog = Sys.executable_name in
  let dir = Filename.dirname prog in
  if Filename.check_suffix prog ".byte" then dir^"/coqtop.byte"
  else dir^"/coqtop.opt"

let set_coqtop_path argv =
  let coqtop = ref "" in
  let rec filter_coqtop = function
    | "-coqtop" :: prog :: args ->
      if !coqtop = "" then
	(coqtop:=prog; filter_coqtop args)
      else
	(output_string stderr "Error: multiple -coqtop options"; exit 1)
    | arg::args -> arg::filter_coqtop args
    | [] -> (if !coqtop = "" then coqtop := default_coqtop_path (); [])
  in
  let argv = filter_coqtop argv in
  Minilib.coqtop_path := !coqtop;
  argv

let process_argv argv =
  try
    let continue,filtered = Coq.filter_coq_opts (List.tl argv) in
    if not continue then
      (List.iter safe_prerr_endline filtered; exit 0);
    let opts = List.filter (fun arg -> String.get arg 0 == '-') filtered in
    if opts <> [] then
      (safe_prerr_endline ("Illegal option: "^List.hd opts); exit 1);
    filtered
  with _ ->
    (safe_prerr_endline "coqtop choked on one of your option"; exit 1)
