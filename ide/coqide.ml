(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Preferences
open Vernacexpr
open Coq
open Ideutils
open Format

let out_some s = match s with 
  | None -> failwith "Internal error in out_some" | Some f -> f

let cb_ = ref None
let cb () = out_some !cb_
let last_cb_content = ref ""

let yes_icon = `YES
let no_icon = `NO
let save_icon = `SAVE
let saveas_icon = `SAVE_AS
let warning_icon = `DIALOG_WARNING
let dialog_size = `DIALOG
let small_size = `SMALL_TOOLBAR

let initial_cwd = Sys.getcwd ()

let status = ref None
let push_info = ref (function s -> failwith "not ready")
let pop_info = ref (function s -> failwith "not ready")
let flash_info = ref  (fun ?delay s -> failwith "not ready")

let set_location = ref  (function s -> failwith "not ready")

let pulse = ref (function () -> failwith "not ready")

let (message_view:GText.view option ref) = ref None
let (proof_view:GText.view option ref) = ref None

let (_notebook:GPack.notebook option ref) = ref None
let notebook () = out_some !_notebook

let decompose_tab w = 
  let vbox = new GPack.box ((Gobject.try_cast w "GtkBox"):Gtk.box Gtk.obj) in
  let l = vbox#children in
  match l with 
    | [img;lbl] -> 
	let img = new GMisc.image 
		    ((Gobject.try_cast img#as_widget "GtkImage"):
		       Gtk.image Gtk.obj) 
	in
	let lbl = GMisc.label_cast lbl in
	vbox,img,lbl
    | _ -> assert false
	
let set_tab_label i n =
  let nb = notebook () in
  let _,_,lbl = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget 
  in
  lbl#set_markup n

let set_tab_image i s = 
  let nb = notebook () in
  let _,img,_ = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget
  in
  img#set_stock s ~size:small_size

let set_current_tab_image s = set_tab_image (notebook())#current_page s
  
let set_current_tab_label n = set_tab_label (notebook())#current_page n 

let get_tab_label i =
  let nb = notebook () in
  let _,_,lbl = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget 
  in
  lbl#text

let get_current_tab_label () = get_tab_label (notebook())#current_page

let get_current_page () = 
  let i = (notebook())#current_page in
  (notebook())#get_nth_page i
				      

let reset_tab_label i = set_tab_label i (get_tab_label i)

let to_do_on_page_switch = ref []
  
module Vector = struct 
  exception Found of int
  type 'a t = ('a option) array ref
  let create () = ref [||]
  let get t i = out_some (Array.get !t i)
  let set t i v = Array.set !t i (Some v)
  let remove t i = Array.set !t i None
  let append t e = t := Array.append !t [|Some e|]; (Array.length !t)-1
  let iter f t =  Array.iter (function | None -> () | Some x -> f x) !t
  let find_or_fail f t = 
    let test i = function | None -> () | Some e -> if f e then raise (Found i) in 
    Array.iteri test t
	
  let exists f t =
    let l = Array.length !t in
    let rec test i = 
      (i < l) && (((!t.(i) <> None) && f (out_some !t.(i))) || test (i+1)) 
    in 
    test 0
end

type 'a viewable_script =
    {view : Undo.undoable_view;
     mutable analyzed_view : 'a option;
    }


class type analyzed_views= 
object('self)
    val mutable act_id : GtkSignal.id option
    val current_all : 'self viewable_script
    val mutable deact_id : GtkSignal.id option
    val input_buffer : GText.buffer
    val input_view : Undo.undoable_view
    val last_array : string array
    val mutable last_index : bool
    val message_buffer : GText.buffer
    val message_view : GText.view
    val proof_buffer : GText.buffer
    val proof_view : GText.view
    val mutable is_active : bool
    val mutable read_only : bool
    val mutable filename : string option
    val mutable stats : Unix.stats option
    val mutable detached_views : GWindow.window list
    method kill_detached_views : unit -> unit
    method add_detached_view : GWindow.window -> unit
    method remove_detached_view : GWindow.window -> unit

    method view : Undo.undoable_view
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
    method backtrack_to_insert : unit
    method clear_message : unit
    method deactivate : unit -> unit
    method disconnected_keypress_handler : GdkEvent.Key.t -> bool
    method electric_handler : GtkSignal.id
    method find_phrase_starting_at :
      GText.iter -> (GText.iter * GText.iter) option
    method get_insert : GText.iter
    method get_start_of_input : GText.iter
    method insert_command : string -> string -> unit
    method insert_commands : (string * string) list -> unit
    method insert_message : string -> unit
    method insert_this_phrase_on_success :
      bool -> bool -> bool -> string -> string -> bool
    method process_next_phrase : bool -> bool -> bool
    method process_until_insert_or_error : unit
    method process_until_iter_or_error : GText.iter -> unit
    method process_until_end_or_error : unit
    method recenter_insert : unit
    method reset_initial : unit
    method send_to_coq :
      string ->
      bool -> bool -> bool -> (Util.loc * Vernacexpr.vernac_expr) option
    method set_message : string -> unit
    method show_goals : unit
    method show_goals_full : unit
    method undo_last_step : unit
    method help_for_keyword : unit -> unit
    method complete_at_offset : int -> unit

    method blaster : unit -> unit
end

let (input_views:analyzed_views viewable_script Vector.t) = Vector.create ()


let signals_to_crash = [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup; 
			  Sys.sigill; Sys.sigpipe; Sys.sigquit; 
			  (* Sys.sigsegv; Sys.sigterm;*) Sys.sigusr2] 

let crash_save i =
(*  ignore (Unix.sigprocmask Unix.SIG_BLOCK signals_to_crash);*)
  Pervasives.prerr_endline "Trying to save all buffers in .crashcoqide files";
  let count = ref 0 in 
  Vector.iter 
    (function {view=view; analyzed_view = Some av } -> 
       (let filename = match av#filename with 
	 | None -> 
	     incr count; 
	     "Unnamed_coqscript_"^(string_of_int !count)^".crashcoqide"
	 | Some f -> f^".crashcoqide"
       in
       try 
	 if try_export filename (view#buffer#get_text ()) then
	   Pervasives.prerr_endline ("Saved "^filename)
	 else Pervasives.prerr_endline ("Could not save "^filename)
       with _ -> Pervasives.prerr_endline ("Could not save "^filename))
       | _ -> Pervasives.prerr_endline "Unanalyzed view found. Please report."
    )
    input_views;
  Pervasives.prerr_endline "Done. Please report.";
  if i <> 127 then exit i

let ignore_break () = 
  List.iter 
    (fun i -> 
       try Sys.set_signal i (Sys.Signal_handle crash_save) 
       with _ -> prerr_endline "Signal ignored (normal if Win32)") 
    signals_to_crash;
  Sys.set_signal Sys.sigint Sys.Signal_ignore

(* Locking machinery for Coq kernel *)
let coq_computing = Mutex.create ()

(* To prevent Coq from interrupting during undoing...*)
let coq_may_stop = Mutex.create ()

let break () = 
  if not (Mutex.try_lock coq_computing) then 
    begin
      prerr_endline "Break received";
      if Mutex.try_lock coq_may_stop then begin
	Util.interrupt := true;
	Mutex.unlock coq_may_stop
      end else prerr_endline "Break discarded (coq may not stop now)";
    end
  else begin
    Mutex.unlock coq_computing;
    prerr_endline "Break received and discarded (not computing)"
  end

let full_do_if_not_computing f x = 
    ignore (Thread.create 
	      (async (fun () ->
			if Mutex.try_lock coq_computing then begin
			  prerr_endline "Launching thread";
			  let w = Blaster_window.blaster_window () in
			  if not (Mutex.try_lock w#lock) then begin 
			    break ();
			    let lck = Mutex.create () in
			    Mutex.lock lck;
			    prerr_endline "Waiting on blaster...";
			    Condition.wait w#blaster_killed lck;
			    prerr_endline "Waiting on blaster ok";
			    Mutex.unlock lck
			  end else Mutex.unlock w#lock;
			  let idle = 
			      Glib.Timeout.add ~ms:300
				~callback:(fun () -> !pulse ();true) in
			    begin
			      prerr_endline "Getting lock";
			      try
				f x;
				Glib.Timeout.remove idle;
			    prerr_endline "Releasing lock";
			    Mutex.unlock w#lock;
			    Mutex.unlock coq_computing;
			      with e -> 
				Glib.Timeout.remove idle;
				prerr_endline "Releasing lock (on error)";
				Mutex.unlock w#lock;
				Mutex.unlock coq_computing;
				raise e
			    end
			end else 
			  prerr_endline 
			    "Discarded order (computations are ongoing)"))
	      ())

let do_if_not_computing f x = 
  ignore (full_do_if_not_computing f x)


let add_input_view tv = 
  Vector.append input_views tv

let get_input_view i = Vector.get input_views i

let active_view = ref None

let get_active_view () = Vector.get input_views (out_some !active_view)

let set_active_view i = 
  (match !active_view with  None -> () | Some i -> 
     reset_tab_label i);
  (notebook ())#goto_page i; 
  let txt = get_current_tab_label () in
  set_current_tab_label ("<span background=\"light green\">"^txt^"</span>");
  active_view := Some i

let set_current_view i = (notebook ())#goto_page i

let kill_input_view i = 
  let v = Vector.get input_views i in
  (match v.analyzed_view with 
    | Some v -> v#kill_detached_views ()
    | None -> ());
  v.view#destroy ();
  v.analyzed_view <- None;
  Vector.remove input_views i

let get_current_view_page () = (notebook ())#current_page
let get_current_view () = Vector.get input_views (notebook ())#current_page
let remove_current_view_page () = 
  let c =  (notebook ())#current_page in
  kill_input_view c;
  ((notebook ())#get_nth_page c)#misc#hide ()

let underscore = Glib.Utf8.to_unichar "_" (ref 0)
let bn = Glib.Utf8.to_unichar "\n" (ref 0)

let starts_word it = it#starts_word && it#backward_char#char <> underscore
let ends_word it = it#ends_line || (it#ends_word && it#char <> underscore)
let inside_word it = it#inside_word || it#char = underscore || it#backward_char#char = underscore
let is_on_word_limit it = inside_word it || ends_word it 

let rec find_word_start it =
  prerr_endline "Find word start";
  if starts_word it
  then it
  else find_word_start it#backward_char

let rec find_word_end it =
  prerr_endline "Find word end";
  if ends_word it
  then it
  else find_word_end it#forward_char

let get_word_around it = 
  let start = find_word_start it in
  let stop =  find_word_end it in
  start,stop


let rec complete_backward w (it:GText.iter) = 
  prerr_endline "Complete backward...";
	  match it#backward_search w with 
	    | None -> None
	    | Some (start,stop) -> 
		if starts_word start then 
		  let ne = find_word_end stop in
		  if ne#compare stop = 0
		  then complete_backward w start
		  else Some (start,stop,ne)
		else complete_backward w start
		  
let rec complete_forward w (it:GText.iter) = 
  prerr_endline "Complete forward...";
  match it#forward_search w with 
    | None -> None
    | Some (start,stop) -> 
	if starts_word start then 	
	  let ne = find_word_end stop in
	  if ne#compare stop = 0 then 
	    complete_forward w stop
	  else Some (stop,stop,ne)
	else complete_forward w stop

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
		      (find_word_end (input_buffer#get_iter (`OFFSET loffset)))#offset ,
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
	    Some (w,offset,(find_word_end (input_buffer#get_iter (`OFFSET offset)))#offset,false);
	      complete input_buffer w offset
	  | Some (ss,start,stop) as result -> 
	      last_completion := Some (w,offset,ss#offset,true);
	      result
      end
	  
let get_current_word () =
  let av = out_some ((get_current_view ()).analyzed_view) in 
  match GtkBase.Clipboard.wait_for_text (cb ()) with
    | None -> 
	prerr_endline "None selected";
	let it = av#get_insert in
	let start = find_word_start it in
	let stop = find_word_end start in
	av#view#buffer#move_mark `SEL_BOUND start;
	av#view#buffer#move_mark `INSERT stop;
	av#view#buffer#get_text ~slice:true ~start ~stop ()
    | Some t ->
 	prerr_endline "Some selected";
	prerr_endline t;
	t
	  

let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
  while len := input ic buf 0 1024; !len > 0 do
    Buffer.add_substring b buf 0 !len
  done

let with_file name ~f =
  let ic = open_in_gen [Open_rdonly;Open_creat] 0o644 name in
  try f ic; close_in ic with exn -> 
    close_in ic; !flash_info ("Error: "^Printexc.to_string exn)

type info =  {start:GText.mark;
	      stop:GText.mark;
	      ast:Util.loc * Vernacexpr.vernac_expr;
	      reset_info:Coq.reset_info;
	     }

exception Size of int
let (processed_stack:info Stack.t) = Stack.create ()
let push x = Stack.push x processed_stack
let pop () = try Stack.pop processed_stack with Stack.Empty -> raise (Size 0)
let top () = try Stack.top processed_stack with Stack.Empty -> raise (Size 0)
let is_empty () = Stack.is_empty processed_stack

  
(* push a new Coq phrase *)

let update_on_end_of_proof id =
  let lookup_lemma = function
  | { ast = _, ( VernacDefinition (_, _, ProveBody _, _, _)
	       | VernacStartTheoremProof _) ; 
      reset_info = Reset (_, r) } -> 
      if not !r then begin 
	prerr_endline "Toggling Reset info to true";
	r := true; raise Exit end
      else begin
	prerr_endline "Toggling Changing Reset id"; 
	r := false
      end
  | { ast = _, (VernacAbort _ | VernacAbortAll) } -> raise Exit
  | _ -> ()
  in
  try Stack.iter lookup_lemma processed_stack with Exit -> ()

let update_on_end_of_segment id =
  let lookup_section = function 
    | { ast = _, ( VernacBeginSection id'
		 | VernacDefineModule (id',_,_,None)
		 | VernacDeclareModule (id',_,_,None)
		 | VernacDeclareModuleType (id',_,None)); 
	reset_info = Reset (_, r) } 
       when id = id' -> raise Exit
    | { reset_info = Reset (_, r) } -> r := false
    | _ -> ()
  in
  try Stack.iter lookup_section processed_stack with Exit -> ()

let push_phrase start_of_phrase_mark end_of_phrase_mark ast = 
  let x = {start = start_of_phrase_mark;
	   stop = end_of_phrase_mark;
	   ast = ast;
	   reset_info = Coq.compute_reset_info (snd ast)
	  } 
  in
  push x;
  match snd ast with
    | VernacEndProof (_, None) -> update_on_end_of_proof ()
    | VernacEndSegment id -> update_on_end_of_segment id
    | _ -> ()

let repush_phrase x =
  let x = { x with reset_info = Coq.compute_reset_info (snd x.ast) } in
  push x;
  match snd x.ast with
    | VernacEndProof (_, None) -> update_on_end_of_proof ()
    | VernacEndSegment id -> update_on_end_of_segment id
    | _ -> ()

(* For electric handlers *)
exception Found

(* For find_phrase_starting_at *)
exception Stop of int

let activate_input i = 
  (match !active_view with
     | None -> () 
     | Some n ->
	 let a_v = out_some (Vector.get input_views n).analyzed_view in
	 a_v#deactivate ();
	 a_v#reset_initial
  );
  let activate_function = (out_some (Vector.get input_views i).analyzed_view)#activate in
  activate_function ();
  set_active_view i

class analyzed_view index =
  let {view = input_view_} as current_all_ =  get_input_view index in
  let proof_view_ = out_some !proof_view in
  let message_view_ = out_some !message_view in
object(self)
  val current_all =  current_all_
  val input_view = current_all_.view
  val proof_view = out_some !proof_view
  val message_view = out_some !message_view
  val input_buffer = input_view_#buffer
  val proof_buffer = proof_view_#buffer
  val message_buffer = message_view_#buffer 
  val mutable is_active = false
  val mutable read_only = false
  val mutable filename = None 
  val mutable stats = None
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.
  val mutable detached_views = []

  method add_detached_view (w:GWindow.window) = 
    detached_views <- w::detached_views
  method remove_detached_view (w:GWindow.window) = 
    detached_views <- List.filter (fun e -> w#misc#get_oid<>e#misc#get_oid) detached_views

  method kill_detached_views () = 
    List.iter (fun w -> w#destroy ()) detached_views;
    detached_views <- []

  method view = input_view
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
	  !push_info "Reverting buffer";
	  try
	    if is_active then self#reset_initial;
	    let b = Buffer.create 1024 in
	    with_file f ~f:(input_channel b);
	    let s = try_convert (Buffer.contents b) in
	    input_buffer#set_text s;
	    self#update_stats;
	    input_buffer#place_cursor input_buffer#start_iter;
	    input_buffer#set_modified false;
	    !pop_info ();
	    !flash_info "Buffer reverted";
	    Highlight.highlight_all input_buffer;
	  with _  -> 
	    !pop_info ();
	    !flash_info "Warning: could not revert buffer";
	end
	in
	if input_buffer#modified then 
	  match (GToolbox.question_box 
		   ~title:"Modified buffer changed on disk"
		   ~buttons:["Revert from File";
			     "Overwrite File";
			     "Disable Auto Revert"] 
		   ~default:0
		   ~icon:(stock_to_widget warning_icon)
		   "Some unsaved buffers changed on disk"
		)
	  with 1 -> do_revert ()
	  | 2 -> if self#save f then !flash_info "Overwritten" else
	      !flash_info "Could not overwrite file"
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
	      !flash_info ~delay:1000 "Autosaved"
	    end
	    else !flash_info "Autosave failed"
	  with _ -> !flash_info "Autosave error"
    end	      
      
  method save_as f =
    if Sys.file_exists f then 
      match (GToolbox.question_box ~title:"File exists on disk"
	       ~buttons:["Overwrite";
			 "Cancel";] 
	       ~default:1
	       ~icon:
	       (let img = GMisc.image () in
		img#set_stock warning_icon ~size:dialog_size;
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

  method show_goals = 
    try
      proof_view#buffer#set_text "";
      let s = Coq.get_current_goals () in
      match s with 
      | [] -> proof_buffer#insert (Coq.print_no_goal ())
      | (hyps,concl)::r -> 
	  let goal_nb = List.length s in
	  proof_buffer#insert (Printf.sprintf "%d subgoal%s\n" 
				 goal_nb
				 (if goal_nb<=1 then "" else "s"));
	  List.iter
	    (fun ((_,_,_,(s,_)) as hyp) -> 
	       proof_buffer#insert (s^"\n"))
	    hyps;
	  proof_buffer#insert (String.make 38 '_' ^ "(1/"^
			       (string_of_int goal_nb)^
			       ")\n") 
	  ;
	  let _,_,_,sconcl = concl in
	  proof_buffer#insert sconcl;
	  proof_buffer#insert "\n";
	  let my_mark = `NAME "end_of_conclusion" in
	  proof_buffer#move_mark
	    ~where:((proof_buffer#get_iter_at_mark `INSERT)) my_mark;
	  proof_buffer#insert "\n\n";
	  let i = ref 1 in
	  List.iter 
	    (function (_,(_,_,_,concl)) -> 
	       incr i;
	       proof_buffer#insert (String.make 38 '_' ^"("^
				    (string_of_int !i)^
				    "/"^
				    (string_of_int goal_nb)^
				    ")\n");
	       proof_buffer#insert concl;
	       proof_buffer#insert "\n\n";
	    )
	    r;
	  ignore (proof_view#scroll_to_mark my_mark) 
      with e -> prerr_endline ("Don't worry be happy despite: "^Printexc.to_string e)
	

  val mutable full_goal_done = true

  method show_goals_full = 
    if not full_goal_done then
      begin
	try
	  proof_view#buffer#set_text "";
	  let s = Coq.get_current_goals () in
	  let last_shown_area = proof_buffer#create_tag [`BACKGROUND "light green"]
	  in
	  match s with 
	  | [] -> proof_buffer#insert (Coq.print_no_goal ())
	  | (hyps,concl)::r -> 
	      let goal_nb = List.length s in
	      proof_buffer#insert (Printf.sprintf "%d subgoal%s\n" 
				     goal_nb
				     (if goal_nb<=1 then "" else "s"));
	      let coq_menu commands = 
		let tag = proof_buffer#create_tag []
		in 
		ignore
		  (tag#connect#event ~callback:
		     (fun ~origin ev it ->
			match GdkEvent.get_type ev with 
			| `BUTTON_PRESS -> 
			    let ev = (GdkEvent.Button.cast ev) in
			    if (GdkEvent.Button.button ev) = 3
			    then begin 
			      let loc_menu = GMenu.menu () in
			      let factory = new GMenu.factory loc_menu in
			      let add_coq_command (cp,ip) = 
				ignore 
				  (factory#add_item cp 
				     ~callback:
				     (fun () -> ignore
					(self#insert_this_phrase_on_success 
					   true
					   true 
					   false 
					   (ip^"\n") 
					   (ip^"\n"))
				     )
				  )
			      in
			      List.iter add_coq_command commands;
			      loc_menu#popup 
				~button:3
				~time:(GdkEvent.Button.time ev);
			    end
			| `MOTION_NOTIFY -> 
			    proof_buffer#remove_tag
			    ~start:proof_buffer#start_iter
			    ~stop:proof_buffer#end_iter
			    last_shown_area;
			    prerr_endline "Before find_tag_limits";
			    
			    let s,e = find_tag_limits tag 
					(new GText.iter it) 
			    in
			    prerr_endline "After find_tag_limits";
			    proof_buffer#apply_tag 
			      ~start:s 
			      ~stop:e 
			      last_shown_area;
			    
			    prerr_endline "Applied tag";
			    ()
			| _ -> ())
		  );
		tag
	      in
	      List.iter
		(fun ((_,_,_,(s,_)) as hyp) -> 
		   let tag = coq_menu (hyp_menu hyp) in
		   proof_buffer#insert ~tags:[tag] (s^"\n"))
		hyps;
	      proof_buffer#insert 
		(String.make 38 '_' ^"(1/"^
		 (string_of_int goal_nb)^
		 ")\n") 
	      ;
	      let tag = coq_menu (concl_menu concl) in
	      let _,_,_,sconcl = concl in
	      proof_buffer#insert ~tags:[tag] sconcl;
	      proof_buffer#insert "\n";
	      let my_mark = `NAME "end_of_conclusion" in
	      proof_buffer#move_mark
		~where:((proof_buffer#get_iter_at_mark `INSERT)) my_mark;
	      proof_buffer#insert "\n\n";
	      let i = ref 1 in
	      List.iter 
		(function (_,(_,_,_,concl)) -> 
		   incr i;
		   proof_buffer#insert 
		     (String.make 38 '_' ^"("^
		      (string_of_int !i)^
		      "/"^
		      (string_of_int goal_nb)^
		      ")\n");
		   proof_buffer#insert concl;
		   proof_buffer#insert "\n\n";
		)
		r;
	      ignore (proof_view#scroll_to_mark my_mark) ;
	      full_goal_done <- true;
	  with e -> prerr_endline (Printexc.to_string e)
      end
      
  method send_to_coq phrase show_output show_error localize =
    try 
      full_goal_done <- false;
      prerr_endline "Send_to_coq starting now";
      let r = Some (Coq.interp phrase) in
      let msg = read_stdout () in 
      self#insert_message (if show_output then msg else "");
      r
    with e ->
      (if show_error then
	 let (s,loc) = Coq.process_exn e in
	 assert (Glib.Utf8.validate s);
	 self#set_message s;
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
		input_buffer#apply_tag_by_name "error"
   		  ~start:starti
		  ~stop:stopi;
		input_buffer#place_cursor starti;
	   ));
      None

  method find_phrase_starting_at (start:GText.iter) = 
    prerr_endline "find_phrase_starting_at starting now";
    let trash_bytes = ref "" in
    let end_iter = start#copy in
    let lexbuf_function s count =
      let i = ref 0 in
      let n_trash = String.length !trash_bytes in
      String.blit !trash_bytes 0 s 0 n_trash;
      i := n_trash;
      try
	while !i <= count - 1 do
	  let c = end_iter#char in
	  if c = 0 then raise (Stop !i);
	  let c' = Glib.Utf8.from_unichar c in
	  let n = String.length c' in
	  if (n<=0) then exit (-2);
	  if n > count - !i  then 
	    begin
	      let ri = count - !i in
	      String.blit c' 0 s !i ri;
	      trash_bytes := String.sub c' ri (n-ri);
	      i := count ;
	    end else begin
	      String.blit c' 0 s !i n;
	      i:= !i + n
	    end;
	  if not end_iter#nocopy#forward_char then 
	    raise (Stop !i)
	done;
	count
      with Stop x ->
	x
    in
    try
      trash_bytes := "";
      let phrase = Find_phrase.get (Lexing.from_function lexbuf_function) 
      in
      end_iter#nocopy#set_offset (start#offset + !Find_phrase.length);
      Some (start,end_iter)
    with
    | Find_phrase.EOF s -> 
	(* Phrase is at the end of the buffer*)
	let si = start#offset in
	let ei = si + !Find_phrase.length in
	end_iter#nocopy#set_offset (ei - 1);
	input_buffer#insert ~iter:end_iter "\n";
	Some (input_buffer#get_iter (`OFFSET si),
	      input_buffer#get_iter (`OFFSET ei))
    | _ -> None

  method complete_at_offset (offset:int) = 
    prerr_endline ("Completion at offset : " ^ string_of_int offset);
    let it () = input_buffer#get_iter (`OFFSET offset) in
    let iit = it () in
    let start = find_word_start iit in
    if is_on_word_limit iit then 
      let w = input_buffer#get_text 
		~start
		~stop:iit
		()
      in
      prerr_endline ("Completion of prefix : " ^ w);
      match complete input_buffer w start#offset with 
      | None -> () 
      | Some (ss,start,stop) -> 
	  let completion = input_buffer#get_text ~start ~stop () in
	  ignore (input_buffer#delete_selection ());
	  ignore (input_buffer#insert_interactive completion);
	  input_buffer#move_mark `SEL_BOUND (it())#backward_char;
	  ()
	  
  method process_next_phrase display_goals do_highlight = 
    begin
      try 
	self#clear_message;
	prerr_endline "process_next_phrase starting now";
	if do_highlight then begin
	  !push_info "Coq is computing";
	  input_view#set_editable false;
	end;
	begin match (self#find_phrase_starting_at self#get_start_of_input) 
	with 
	| None -> 	  
	    if do_highlight then begin
	      input_view#set_editable true;
	      !pop_info ();
	    end; false
	| Some(start,stop) ->
	    prerr_endline "process_next_phrase : to_process highlight";
	    let b = input_buffer in
	    if do_highlight then begin
	      input_buffer#apply_tag_by_name ~start ~stop "to_process";
	      prerr_endline "process_next_phrase : to_process applied";
	      process_pending ()
	    end;
	    prerr_endline "process_next_phrase : getting phrase";
	    let phrase = start#get_slice ~stop in
	    let r = 
	      match self#send_to_coq phrase true true true with
	      | Some ast ->
		  begin
		    b#move_mark ~where:stop (`NAME "start_of_input");
		    b#apply_tag_by_name "processed" ~start ~stop;
		    if (self#get_insert#compare) stop <= 0 then 
		      begin
			b#place_cursor stop;
			self#recenter_insert
		      end;
		    let start_of_phrase_mark = `MARK (b#create_mark start)
		    in
		    let end_of_phrase_mark = `MARK (b#create_mark stop) in
		    push_phrase 
		      start_of_phrase_mark 
		      end_of_phrase_mark ast;
		    if display_goals then self#show_goals;
		    true
		  end
	      | None -> false
	    in
	    if do_highlight then begin
	      b#remove_tag_by_name ~start ~stop "to_process" ;
	      input_view#set_editable true;
	      !pop_info ();
	    end;
	    r;
	end
      with e -> raise e
    end
    
  method insert_this_phrase_on_success 
    show_output show_msg localize coqphrase insertphrase = 
    match self#send_to_coq coqphrase show_output show_msg localize with
    | Some ast ->
	begin
	  let stop = self#get_start_of_input in
	  if stop#starts_line then
	    input_buffer#insert ~iter:stop insertphrase
	  else input_buffer#insert ~iter:stop ("\n"^insertphrase); 
	  let start = self#get_start_of_input in
	  input_buffer#move_mark ~where:stop (`NAME "start_of_input");
	  input_buffer#apply_tag_by_name "processed" ~start ~stop;
	  if (self#get_insert#compare) stop <= 0 then 
	    input_buffer#place_cursor stop;
	  let start_of_phrase_mark = `MARK (input_buffer#create_mark start) 
	  in
	  let end_of_phrase_mark = `MARK (input_buffer#create_mark stop) in
	  push_phrase start_of_phrase_mark end_of_phrase_mark ast;
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
	    input_buffer#move_mark ~where:stop (`NAME "start_of_input");
	    input_buffer#apply_tag_by_name "processed" ~start ~stop;
	    if (self#get_insert#compare) stop <= 0 then 
	    input_buffer#place_cursor stop;
	    let start_of_phrase_mark = `MARK (input_buffer#create_mark start) 
	    in
	    let end_of_phrase_mark = `MARK (input_buffer#create_mark stop) in
	    push_phrase start_of_phrase_mark end_of_phrase_mark ast
	    end
	    | None -> ())
	    | _ -> ())
	    with _ -> ()*)
	  true
	end
    | None -> self#insert_message ("Unsuccesfully tried: "^coqphrase);
	false

  method process_until_iter_or_error stop =
    let stop' = `OFFSET stop#offset in
    let start = self#get_start_of_input#copy in
    let start' = `OFFSET start#offset in
    input_buffer#apply_tag_by_name 
      ~start
      ~stop
      "to_process";
    input_view#set_editable false;
    !push_info "Coq is computing";
    process_pending ();
    (try 
       while ((stop#compare self#get_start_of_input>=0) 
	      && (self#process_next_phrase false false))
       do Util.check_for_interrupt () done
     with Sys.Break -> 
       prerr_endline "Interrupted during process_until_iter_or_error");
    self#show_goals;
    (* Start and stop might be invalid if an eol was added at eof *)
    let start = input_buffer#get_iter start' in
    let stop =  input_buffer#get_iter stop' in
    input_buffer#remove_tag_by_name ~start ~stop "to_process" ;
    input_view#set_editable true;
    !pop_info()

  method process_until_end_or_error = 
    self#process_until_iter_or_error input_buffer#end_iter

  method process_until_insert_or_error = 
    let stop = self#get_insert in
    self#process_until_iter_or_error stop

  method reset_initial =
    Stack.iter 
      (function inf -> 
	 let start = input_buffer#get_iter_at_mark inf.start in
	 let stop = input_buffer#get_iter_at_mark inf.stop in
	 input_buffer#move_mark ~where:start (`NAME "start_of_input");
	 input_buffer#remove_tag_by_name "processed" ~start ~stop;
	 input_buffer#delete_mark inf.start;
	 input_buffer#delete_mark inf.stop;
      ) 
      processed_stack;
    Stack.clear processed_stack;
    self#clear_message;
    Coq.reset_initial ()


  (* backtrack Coq to the phrase preceding iterator [i] *)
  method backtrack_to_no_lock i =
    prerr_endline "Backtracking_to iter starts now.";
    (* re-synchronize Coq to the current state of the stack *)
    let rec synchro () =
      if is_empty () then
	Coq.reset_initial ()
      else begin
	let t = pop () in
	begin match t.reset_info with
	| Reset (id, ({contents=true} as v)) -> v:=false; 
	    (match snd t.ast with
	     | VernacBeginSection _ | VernacDefineModule _ 
	     | VernacDeclareModule _ | VernacDeclareModuleType _
	     | VernacEndSegment _ 
	       -> reset_to_mod id
	     | _ ->  reset_to id)
	| _ -> synchro ()
	end;
	interp_last t.ast;
	repush_phrase t
      end
    in
    let add_undo t = match t with | Some n -> Some (succ n) | None -> None
    in
    (* pop Coq commands until we reach iterator [i] *)
    let  rec pop_commands done_smthg undos =
      if is_empty () then 
	done_smthg, undos
      else
	let t = top () in 
	if i#compare (input_buffer#get_iter_at_mark t.stop) < 0 then begin
	  ignore (pop ());
	  let undos = if is_tactic (snd t.ast) then add_undo undos else None in
	  pop_commands true undos
	end else
	  done_smthg, undos
    in
    let done_smthg, undos = pop_commands false (Some 0) in
    prerr_endline "Popped commands";
    if done_smthg then
      begin 
	try 
	  (match undos with 
	   | None -> synchro () 
	   | Some n -> try Pfedit.undo n with _ -> synchro ());
	  let start = if is_empty () then input_buffer#start_iter 
	  else input_buffer#get_iter_at_mark (top ()).stop 
	  in
	  prerr_endline "Removing (long) processed tag...";
	  input_buffer#remove_tag_by_name 
	    ~start 
	    ~stop:self#get_start_of_input
	    "processed";
	  prerr_endline "Moving (long) start_of_input...";
	  input_buffer#move_mark ~where:start (`NAME "start_of_input");
	  self#show_goals;
	  clear_stdout ();
	  self#clear_message;
	with _ -> 
	  !push_info "WARNING: undo failed badly -> Coq might be in an inconsistent state.
Please restart and report NOW.";
      end
    else prerr_endline "backtrack_to : discarded (...)"
      
  method backtrack_to i = 
    if Mutex.try_lock coq_may_stop then 
      (!push_info "Undoing...";self#backtrack_to_no_lock i ; Mutex.unlock coq_may_stop;
       !pop_info ())
    else prerr_endline "backtrack_to : discarded (lock is busy)"

  method backtrack_to_insert = 
    self#backtrack_to self#get_insert


  method undo_last_step =
    if Mutex.try_lock coq_may_stop then  
      (!push_info "Undoing last step...";
       (try
	  let last_command = top () in
	  let start = input_buffer#get_iter_at_mark last_command.start in
	  let update_input () =
	    prerr_endline "Removing processed tag...";
	    input_buffer#remove_tag_by_name 
	      ~start
	      ~stop:(input_buffer#get_iter_at_mark last_command.stop) 
	      "processed";
	    prerr_endline "Moving start_of_input";
	    input_buffer#move_mark
	      ~where:start
	      (`NAME "start_of_input");
	    input_buffer#place_cursor start;
	    self#recenter_insert;
	    self#show_goals;
	    self#clear_message
	  in
	  begin match last_command with 
	  | {ast=_,VernacSolve _} -> 
	      begin 
		try Pfedit.undo 1; ignore (pop ()); update_input () 
		with _ -> self#backtrack_to_no_lock start
	      end
	  | {ast=_,t;reset_info=Reset (id, {contents=true})} ->
	      ignore (pop ());
	      (match t with 
	       | VernacBeginSection _ | VernacDefineModule _ 
	       | VernacDeclareModule _ | VernacDeclareModuleType _
	       | VernacEndSegment _ 
		 -> reset_to_mod id
	       | _ ->  reset_to id);
	      update_input ()
	  | { ast = _, ( VernacStartTheoremProof _ 
		       | VernacDefinition (_,_,ProveBody _,_,_));
	      reset_info=Reset(id,{contents=false})} ->
	      ignore (pop ());
	      (try 
		 Pfedit.delete_current_proof () 
	       with e ->
		 begin 
		   prerr_endline "WARNING : found a closed environment";
		   raise e
		 end);
	      update_input ()
	  | _ -> 
	      self#backtrack_to_no_lock start
	  end;
	with
	| Size 0 -> (* !flash_info "Nothing to Undo"*)()
       );
       !pop_info ();
       Mutex.unlock coq_may_stop)
    else prerr_endline "undo_last_step discarded"

      
  method blaster () = 
    
    ignore (Thread.create 
	      (fun () ->  
		 prerr_endline "Blaster called";
		 let c = Blaster_window.present_blaster_window () in
		 if Mutex.try_lock c#lock then begin
		   c#clear ();
		   let current_gls = try get_current_goals () with _ -> [] in
		   let gls_nb = List.length current_gls in
		   
		   let set_goal i (s,t) = 
		     let gnb = string_of_int i in
		     let s = gnb ^":"^s in
		     let t' = gnb ^": Progress "^t in
		     let t'' = gnb ^": "^t in
		     c#set
		       ("Goal "^gnb)
		       s 
		       (fun () -> try_interptac t')
		       (fun () -> self#insert_command t'' t'')
		   in
		   let set_current_goal (s,t) = 
		     c#set
		       "Goal 1"
		       s 
		       (fun () -> try_interptac ("Progress "^t))
		       (fun () -> self#insert_command t t)
		   in
		   begin match current_gls with 
		   | [] -> ()
		   | (hyp_l,current_gl)::r ->
		       List.iter set_current_goal (concl_menu current_gl);
		       List.iter 
			 (fun hyp -> 
			    List.iter set_current_goal (hyp_menu hyp))
			 hyp_l;
		       let i = ref 2 in
		       List.iter 
			 (fun (hyp_l,gl) -> 
			    List.iter (set_goal !i) (concl_menu gl);
			    incr i)
			 r
		   end;
		   let _ =  c#blaster () in
		   Mutex.unlock c#lock
		 end else prerr_endline "Blaster discarded")
	      ())
      
  method insert_command cp ip = 
    self#clear_message;
    ignore (self#insert_this_phrase_on_success true false false cp ip)
  method insert_commands l = 
    self#clear_message;
    ignore (List.exists 
	      (fun (cp,ip) -> 
		 self#insert_this_phrase_on_success true false false 
		 (cp^"\n") (ip^"\n")) l)

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
		input_buffer#place_cursor i;
		self#process_until_insert_or_error
	      end);
	  true
      | l when List.mem `CONTROL l -> 
	  let k = GdkEvent.Key.keyval k in
	  if GdkKeysyms._m=k
	  then break ();
	  false
      | l -> false
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

  method deactivate () = 
    is_active <- false;
    (match act_id with None -> () 
     | Some id ->
	 reset_initial ();
	 input_view#misc#disconnect id;
	 prerr_endline "DISCONNECTED old active : ";
	 print_id id;
    );
    deact_id <- Some 
      (input_view#event#connect#key_press self#disconnected_keypress_handler);
    prerr_endline "CONNECTED  inactive : ";
    print_id (out_some deact_id)

  method activate () =
    is_active <- true;
    (match deact_id with None -> () 
     | Some id -> input_view#misc#disconnect id;
	 prerr_endline "DISCONNECTED old inactive : ";
	 print_id id
    );
    act_id <- Some 
      (input_view#event#connect#key_press self#active_keypress_handler);
    prerr_endline "CONNECTED active : ";
    print_id (out_some act_id);
    let dir = (match 
		 (out_some ((Vector.get input_views index).analyzed_view))
		 #filename 
	       with
	       | None -> initial_cwd
	       | Some f -> Filename.dirname f
	      )
    in 
    if not (is_in_coq_lib dir) then 
      ignore (Coq.interp (Printf.sprintf "Add LoadPath \"%s\". " dir));
    Sys.chdir dir
      
      
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
	     ignore (self#process_next_phrase true true)
	   end;
	 end;
	 last_index <- not last_index;)

  method private electric_paren tag =
    let oparen_code = Glib.Utf8.to_unichar "("  (ref 0) in
    let cparen_code = Glib.Utf8.to_unichar ")"  (ref 0) in
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

  method help_for_keyword () = browse_keyword (get_current_word ())

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
			     (prerr_endline "insert_text: Placing cursor";input_buffer#place_cursor it)));
    ignore (input_buffer#connect#after#apply_tag
	      ~callback:(fun tag ~start ~stop ->
			   if (start#compare self#get_start_of_input)>=0
			   then 
			     input_buffer#remove_tag_by_name 
			       ~start
			       ~stop
			       "processed"
			)
	   );
    ignore 
      (input_buffer#connect#modified_changed
	 ~callback:
	 (fun () ->
	    if input_buffer#modified then 
	      set_tab_image index 
		(match (out_some (current_all.analyzed_view))#filename with 
		 | None -> saveas_icon
		 | Some _ -> save_icon
		)
	    else set_tab_image index yes_icon;
	 ));
    ignore (input_buffer#connect#changed
	      ~callback:(fun () -> 
			   last_modification_time <- Unix.time ();
			   let r = input_view#visible_rect in
			   let stop = 
			     input_view#get_iter_at_location 
			       ~x:(Gdk.Rectangle.x r + Gdk.Rectangle.width r)
			       ~y:(Gdk.Rectangle.y r + Gdk.Rectangle.height r)
			   in
			   input_buffer#remove_tag_by_name 
			     ~start:self#get_start_of_input
			     ~stop
			     "error";
			   Highlight.highlight_slice
			     input_buffer self#get_start_of_input stop
			)
	   );
    ignore (input_buffer#add_selection_clipboard (cb()));
    let paren_highlight_tag = input_buffer#create_tag ~name:"paren" [`BACKGROUND "purple"]  in
    self#electric_paren paren_highlight_tag;
    ignore (input_buffer#connect#after#mark_set 
	      ~callback:(fun it (m:Gtk.textmark) ->
			   !set_location 
			   (Printf.sprintf 
			      "Line: %5d Char: %3d" (self#get_insert#line + 1)
			      (self#get_insert#line_offset + 1));
			   match GtkText.Mark.get_name m  with
			   | Some "insert" ->		 
			       input_buffer#remove_tag
			       ~start:input_buffer#start_iter
			       ~stop:input_buffer#end_iter
			       paren_highlight_tag;
			   | Some s -> 
			       prerr_endline (s^" moved")
			   | None -> () )
	   );
    ignore (input_buffer#connect#insert_text
	      (fun it s -> 
		 prerr_endline "Should recenter ?";
		 if String.contains s '\n' then begin
		   prerr_endline "Should recenter : yes";
		   self#recenter_insert
		 end))
end

let create_input_tab filename =
  let b = GText.buffer () in 
  let tablabel = GMisc.label () in 
  let v_box = GPack.hbox ~homogeneous:false () in
  let image = GMisc.image ~packing:v_box#pack () in
  let label = GMisc.label ~text:filename ~packing:v_box#pack () in
  let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT
	      ~packing:((notebook ())#append_page
			  ~tab_label:v_box#coerce) () 
  in 
  let sw1 = GBin.scrolled_window
	      ~vpolicy:`AUTOMATIC 
	      ~hpolicy:`AUTOMATIC
	      ~packing:fr1#add () 
  in
  let tv1 = Undo.undoable_view ~buffer:b ~packing:(sw1#add) () in
  prerr_endline ("Language: "^ b#start_iter#language);
  tv1#misc#set_name "ScriptWindow";
  let _ = tv1#set_editable true in
  let _ = tv1#set_wrap_mode `NONE in
  b#place_cursor ~where:(b#start_iter);
  ignore (tv1#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));
(*  ignore (tv1#event#connect#button_press ~callback:
	    (fun ev -> 
	       if (GdkEvent.Button.button ev=2) then
		 (try 
		    prerr_endline "Paste invoked";
		    GtkSignal.emit_unit 
		      (get_current_view()).view#as_view 
		      GtkText.View.Signals.paste_clipboard;
		    true
		  with _ -> false)
	       else false
	    ));*)
  tv1#misc#grab_focus ();
  ignore (tv1#buffer#create_mark 
	    ~name:"start_of_input" 
	    tv1#buffer#start_iter);
  ignore (tv1#buffer#create_tag 
	    ~name:"kwd" 
	    [`FOREGROUND "blue"]);
  ignore (tv1#buffer#create_tag 
	    ~name:"decl" 
	    [`FOREGROUND "orange red"]);
  ignore (tv1#buffer#create_tag 
	    ~name:"comment" 
	    [`FOREGROUND "brown"]);
  ignore (tv1#buffer#create_tag 
	    ~name:"reserved" 
	    [`FOREGROUND "dark red"]);
  ignore (tv1#buffer#create_tag 
	    ~name:"error" 
	    [`UNDERLINE `DOUBLE ; `FOREGROUND "red"]);
  ignore (tv1#buffer#create_tag 
	    ~name:"to_process" 
	    [`BACKGROUND "light blue" ;`EDITABLE false]);
  ignore (tv1#buffer#create_tag 
	    ~name:"processed" 
	    [`BACKGROUND "light green" ;`EDITABLE false]);
  tv1
 
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
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in


  (* Menu bar *)
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in

  (* Tearable Toolbar *)
  let handle = GBin.handle_box 
		 ~show:!current.show_toolbar
		 ~handle_position:`LEFT
		 ~snap_edge:`LEFT
		 ~packing:vbox#pack
		 ()
  in
  let toolbar = GButton.toolbar 
		  ~orientation:`HORIZONTAL 
		  ~style:`BOTH
		  ~tooltips:true 
		  ~packing:handle#add
		  ()
  in
  show_toolbar := 
  (fun b -> if b then handle#misc#show () else handle#misc#hide ());

  let factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/" menubar in
  let accel_group = factory#accel_group in

  (* File Menu *)
  let file_menu = factory#add_submenu "_File" in

  let file_factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/File/" file_menu ~accel_group in

  (* File/Load Menu *)
  let load f =
    try
      Vector.find_or_fail 
	(function 
	   | {analyzed_view=Some av} -> 
	       (match av#filename with 
		| None -> false 
		| Some fn -> f=fn)
	   | _ -> false) 
	!input_views;
      let b = Buffer.create 1024 in
      with_file f ~f:(input_channel b);
      let s = do_convert (Buffer.contents b) in
      let view = create_input_tab (Glib.Convert.filename_to_utf8 
				     (Filename.basename f)) 
      in
      view#misc#modify_font !current.text_font;
      let index = add_input_view {view = view;
				  analyzed_view = None;
				 }
      in
      let av = (new analyzed_view index) in 
      (get_input_view index).analyzed_view <- Some av;
      av#set_filename 
	(Some (if Filename.is_relative f then 
		 Filename.concat initial_cwd f
	       else f
	      ));
      av#update_stats;
      let input_buffer = view#buffer in
      input_buffer#set_text s;
      input_buffer#place_cursor input_buffer#start_iter;
      set_current_view index;
      Highlight.highlight_all input_buffer;
      input_buffer#set_modified false;
      av#view#clear_undo
    with       
    | Vector.Found i -> set_current_view i
    | e -> !flash_info ("Load failed: "^(Printexc.to_string e))
  in
  let load_m = file_factory#add_item "_Open/Create" 
		 ~key:GdkKeysyms._O in
  let load_f () = 	  
    match select_file ~title:"Load file" () with 
    | None -> ()
    | (Some f) as fn -> load f
  in
  ignore (load_m#connect#activate (load_f));

  (* File/Save Menu *)
  let save_m = file_factory#add_item "_Save" 
		 ~key:GdkKeysyms._S in
  let save_f () = 
    let current = get_current_view () in
    try
      (match (out_some current.analyzed_view)#filename with 
       | None ->
	   begin match GToolbox.select_file ~title:"Save file" ()
	   with
	   | None -> ()
	   | Some f -> 
	       if (out_some current.analyzed_view)#save_as f then begin
		 set_current_tab_label (Filename.basename f);
		 !flash_info "Saved"
	       end
	       else !flash_info "Save Failed"
	   end
       | Some f -> 
	   if (out_some current.analyzed_view)#save f then 
	     !flash_info "Saved"
	   else !flash_info "Save Failed"
	     
      )
    with 
    | e -> !flash_info "Save failed"
  in   
  ignore (save_m#connect#activate save_f);

  (* File/Save As Menu *)
  let saveas_m = file_factory#add_item "S_ave as" 
  in
  let saveas_f () = 
    let current = get_current_view () in
    try (match (out_some current.analyzed_view)#filename with 
	 | None -> 
	     begin match GToolbox.select_file ~title:"Save file as" ()
	     with
	     | None -> ()
	     | Some f -> 
		 if (out_some current.analyzed_view)#save_as f then begin
		   set_current_tab_label (Filename.basename f);
		   !flash_info "Saved"
		 end
		 else !flash_info "Save Failed"
	     end
	 | Some f -> 
	     begin match GToolbox.select_file 
	       ~dir:(ref (Filename.dirname f)) 
	       ~filename:(Filename.basename f)
	       ~title:"Save file as" ()
	     with
	     | None -> ()
	     | Some f -> 
		 if (out_some current.analyzed_view)#save_as f then begin
		   set_current_tab_label (Filename.basename f);
		   !flash_info "Saved"
		 end else !flash_info "Save Failed"
	     end);
    with e -> !flash_info "Save Failed"
  in   
  ignore (saveas_m#connect#activate saveas_f);
  
  
  (* File/Save All Menu *)
  let saveall_m = file_factory#add_item "Sa_ve All" in
  let saveall_f () = 
    Vector.iter
      (function 
	 | {view = view ; analyzed_view = Some av} as full -> 
	     begin match av#filename with 
	     | None -> ()
	     | Some f ->
		 ignore (av#save f)
	     end
	 | _ -> ()
      )  input_views
  in
  let has_something_to_save () = 
    Vector.exists
      (function 
	 | {view=view} -> view#buffer#modified        
      )
      input_views
  in
  ignore (saveall_m#connect#activate saveall_f);

  (* File/Revert Menu *)
  let revert_m = file_factory#add_item "_Revert All Buffers" in
  let revert_f () = 
    Vector.iter 
      (function 
	   {view = view ; analyzed_view = Some av} as full -> 
	     (try 
		match av#filename,av#stats with 
		| Some f,Some stats -> 
		    let new_stats = Unix.stat f in
		    if new_stats.Unix.st_mtime > stats.Unix.st_mtime 
		    then av#revert
		| Some _, None -> av#revert
		| _ -> ()
		with _ -> av#revert)
	 | _ -> ()
      )  input_views
  in
  ignore (revert_m#connect#activate revert_f);

  (* File/Close Menu *)
  let close_m = file_factory#add_item "_Close Buffer" in
  let close_f () = 
    let v = out_some !active_view in
    let act = get_current_view_page () in
    if v = act then !flash_info "Cannot close an active view"
    else remove_current_view_page ()
  in
  ignore (close_m#connect#activate close_f);

  (* File/Print Menu *)
  let print_f () =
    let v = get_current_view () in
    let av = out_some v.analyzed_view in
    match av#filename with
    | None -> 
	!flash_info "Cannot print: this buffer has no name"
    | Some f ->
	let cmd = 
	  "cd " ^ Filename.dirname f ^ "; " ^
	  !current.cmd_coqdoc ^ " -ps " ^ Filename.basename f ^ 
	  " | " ^ !current.cmd_print
	in
	let s,_ = run_command av#insert_message cmd in
	!flash_info (cmd ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let print_m = file_factory#add_item "_Print" ~callback:print_f in

  (* File/Export to Menu *)
  let export_f kind () =
    let v = get_current_view () in
    let av = out_some v.analyzed_view in
    match av#filename with
    | None -> 
	!flash_info "Cannot print: this buffer has no name"
    | Some f ->
	let basef = Filename.basename f in
	let output = 
	  let basef_we = try Filename.chop_extension basef with _ -> basef in
	  match kind with
	  | "latex" -> basef_we ^ ".tex"
	  | "dvi" | "ps" | "html" -> basef_we ^ "." ^ kind
	  | _ -> assert false
	in
	let cmd = 
	  "cd " ^ Filename.dirname f ^ "; " ^
	  !current.cmd_coqdoc ^ " --" ^ kind ^ " -o " ^ output ^ " " ^ basef
	in
	let s,_ = run_command av#insert_message cmd in
	!flash_info (cmd ^ 
		     if s = Unix.WEXITED 0 
		     then " succeeded" 
		     else " failed")
  in
  let file_export_m =  file_factory#add_submenu "E_xport to" in

  let file_export_factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/Export/" file_export_m ~accel_group in
  let export_html_m = 
    file_export_factory#add_item "_Html" ~callback:(export_f "html") 
  in
  let export_latex_m = 
    file_export_factory#add_item "_LaTeX" ~callback:(export_f "latex")
  in
  let export_dvi_m = 
    file_export_factory#add_item "_Dvi" ~callback:(export_f "dvi") 
  in
  let export_ps_m = 
    file_export_factory#add_item "_Ps" ~callback:(export_f "ps") 
  in

  (* File/Rehighlight Menu *)
  let rehighlight_m = file_factory#add_item "Reh_ighlight" ~key:GdkKeysyms._L in
  ignore (rehighlight_m#connect#activate 
	    (fun () -> 
	       Highlight.rehighlight_all 
	       (get_current_view()).view#buffer;
	       (out_some (get_current_view()).analyzed_view)#recenter_insert));

  (*  (* File/Refresh Menu *)
      let refresh_m = file_factory#add_item "Restart all" ~key:GdkKeysyms._R in
      refresh_m#misc#set_state `INSENSITIVE;
  *)
  (* File/Quit Menu *)
  let quit_f () =
    if has_something_to_save () then 
      match (GToolbox.question_box ~title:"Quit"
	       ~buttons:["Save Named Buffers and Quit";
			 "Quit without Saving";
			 "Don't Quit"] 
	       ~default:0
	       ~icon:
	       (let img = GMisc.image () in
		img#set_stock warning_icon ~size:dialog_size;
		img#coerce)
	       "There are unsaved buffers"
	    )
      with 1 -> saveall_f () ; exit 0
      | 2 -> exit 0
      | _ -> ()
    else exit 0
  in
  let quit_m = file_factory#add_item "_Quit" ~key:GdkKeysyms._Q 
		 ~callback:quit_f
  in
  ignore (w#event#connect#delete (fun _ -> quit_f (); true));

  (* Edit Menu *)
  let edit_menu = factory#add_submenu "_Edit" in
  let edit_f = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/Edit/" edit_menu ~accel_group in
  ignore(edit_f#add_item "_Undo" ~key:GdkKeysyms._u ~callback:
	   (do_if_not_computing 
	      (fun () -> ignore (get_current_view()).view#undo)));
  ignore(edit_f#add_item "_Clear Undo Stack" ~key:GdkKeysyms._exclam ~callback:
	   (fun () -> 
	      ignore (get_current_view()).view#clear_undo));
  ignore(edit_f#add_separator ());
  ignore(edit_f#add_item "Copy" ~key:GdkKeysyms._C ~callback:
	   (fun () -> GtkSignal.emit_unit
	      (get_current_view()).view#as_view 
	      GtkText.View.Signals.copy_clipboard));
  ignore(edit_f#add_item "Cut" ~key:GdkKeysyms._X ~callback:
	   (do_if_not_computing 
	      (fun () -> GtkSignal.emit_unit
		 (get_current_view()).view#as_view 
		 GtkText.View.Signals.cut_clipboard)));
  ignore(edit_f#add_item "Paste" ~key:GdkKeysyms._V ~callback:
	   (do_if_not_computing
	      (fun () -> 
		 try GtkSignal.emit_unit
		   (get_current_view()).view#as_view 
		   GtkText.View.Signals.paste_clipboard
		 with _ -> prerr_endline "EMIT PASTE FAILED")));
  ignore (edit_f#add_separator ());
  let read_only_i = edit_f#add_check_item "Expert" ~active:false
		      ~key:GdkKeysyms._B
		      ~callback:(fun b -> ()
				)
  in
(*  read_only_i#misc#set_state `INSENSITIVE;*)

  let search_if = edit_f#add_item "Search _forward"
		    ~key:GdkKeysyms._greater
  in
  let search_ib = edit_f#add_item "Search _backward"
		    ~key:GdkKeysyms._less
  in
  let complete_i = edit_f#add_item "_Complete"
		     ~key:GdkKeysyms._comma
		     ~callback:
		     (do_if_not_computing 
			(fun b -> 
			   let v = out_some (get_current_view ()).analyzed_view 
				    
			   in v#complete_at_offset ((v#view#buffer#get_iter `SEL_BOUND)#offset)
			))
  in

  to_do_on_page_switch := 
  (fun i -> 
     prerr_endline ("Switching to tab "^(string_of_int i));
     let v = out_some (get_input_view i).analyzed_view in
     read_only_i#set_active v#read_only
  )::!to_do_on_page_switch;
  
  (* Navigation Menu *)
  let navigation_menu =  factory#add_submenu "_Navigation" in
  let navigation_factory = 
    new GMenu.factory navigation_menu 
      ~accel_path:"<CoqIde MenuBar>/Navigation/"
      ~accel_group 
      ~accel_modi:!current.modifier_for_navigation 
  in
  let do_or_activate f () = 
    let current = get_current_view () in
    let analyzed_view = out_some current.analyzed_view in
    if analyzed_view#is_active then 
      ignore (f analyzed_view)
    else
      begin
	!flash_info "New proof started";
	activate_input (notebook ())#current_page;
	ignore (f analyzed_view)
      end
  in

  let do_or_activate f = do_if_not_computing (do_or_activate f) in

  let add_to_menu_toolbar text ~tooltip ~key ~callback icon = 
    ignore (navigation_factory#add_item text ~key ~callback);
    ignore (toolbar#insert_button
	      ~tooltip
	      ~text:tooltip
	      ~icon:(stock_to_widget ~size:`LARGE_TOOLBAR icon)
	      ~callback
	      ())
  in
  add_to_menu_toolbar "_Interrupt computations"
    ~tooltip:"Interrupt computations"    
    ~key:GdkKeysyms._Break 
    ~callback:break
    `STOP
  ;
  add_to_menu_toolbar 
    "_Forward" 
    ~tooltip:"Forward" 
    ~key:GdkKeysyms._Down 
    ~callback:(do_or_activate (fun a -> a#process_next_phrase true true))
    `GO_DOWN;
  add_to_menu_toolbar "_Backward"
    ~tooltip:"Backward" 
    ~key:GdkKeysyms._Up
    ~callback:(do_or_activate (fun a -> a#undo_last_step))
    `GO_UP;
  add_to_menu_toolbar 
    "_Forward to" 
    ~tooltip:"Forward to" 
    ~key:GdkKeysyms._Right
    ~callback:(do_or_activate (fun a -> a#process_until_insert_or_error))
    `GOTO_LAST;
  add_to_menu_toolbar 
    "_Backward to" 
    ~tooltip:"Backward to" 
    ~key:GdkKeysyms._Left
    ~callback:(do_or_activate (fun a-> a#backtrack_to_insert))
    `GOTO_FIRST;
  add_to_menu_toolbar 
    "_Start" 
    ~tooltip:"Start" 
    ~key:GdkKeysyms._Home
    ~callback:(do_or_activate (fun a -> a#reset_initial))
    `GOTO_TOP;
  add_to_menu_toolbar 
    "_End" 
    ~tooltip:"End" 
    ~key:GdkKeysyms._End
    ~callback:(do_or_activate (fun a -> a#process_until_end_or_error))
    `GOTO_BOTTOM;

  (* Tactics Menu *)
  let tactics_menu =  factory#add_submenu "_Try Tactics" in
  let tactics_factory = 
    new GMenu.factory tactics_menu 
      ~accel_path:"<CoqIde MenuBar>/Tactics/"
      ~accel_group 
      ~accel_modi:!current.modifier_for_tactics
  in
  let do_if_active_raw f () = 
    let current = get_current_view () in
    let analyzed_view = out_some current.analyzed_view in
    if analyzed_view#is_active then ignore (f analyzed_view)
  in
  let do_if_active f = do_if_not_computing (do_if_active_raw f) in

  ignore (tactics_factory#add_item "_Blaster"
	    ~key:GdkKeysyms._b
	    ~callback: (do_if_active_raw (fun a -> a#blaster ()))
	    (* Custom locking mechanism! *)
	 )
	 ;

  ignore (tactics_factory#add_item "_Auto" 
	    ~key:GdkKeysyms._a
	    ~callback:(do_if_active (fun a -> a#insert_command "Progress Auto.\n" "Auto.\n"))
	 );
  ignore (tactics_factory#add_item "_Auto with *"
	    ~key:GdkKeysyms._asterisk
	    ~callback:(do_if_active (fun a -> a#insert_command 
				       "Progress Auto with *.\n"
				       "Auto with *.\n")));
  ignore (tactics_factory#add_item "_EAuto"
	    ~key:GdkKeysyms._e
	    ~callback:(do_if_active (fun a -> a#insert_command 
				       "Progress EAuto.\n"
				       "EAuto.\n"))
	 );
  ignore (tactics_factory#add_item "_EAuto with *"
	    ~key:GdkKeysyms._ampersand
	    ~callback:(do_if_active (fun a -> a#insert_command 
				       "Progress EAuto with *.\n" 
				       "EAuto with *.\n"))
	 );
  ignore (tactics_factory#add_item "_Intuition"
	    ~key:GdkKeysyms._i
	    ~callback:(do_if_active (fun a -> a#insert_command "Progress Intuition.\n" "Intuition.\n"))
	 );
  ignore (tactics_factory#add_item "_Omega"
	    ~key:GdkKeysyms._o
	    ~callback:(do_if_active (fun a -> a#insert_command "Omega.\n" "Omega.\n"))
	 );
  ignore (tactics_factory#add_item "_Simpl"
	    ~key:GdkKeysyms._s
	    ~callback:(do_if_active (fun a -> a#insert_command "Progress Simpl.\n" "Simpl.\n" ))
	 );
  ignore (tactics_factory#add_item "_Tauto"
	    ~key:GdkKeysyms._p
	    ~callback:(do_if_active (fun a -> a#insert_command "Tauto.\n" "Tauto.\n" ))
	 );
  ignore (tactics_factory#add_item "_Trivial"
	    ~key:GdkKeysyms._v
	    ~callback:(do_if_active( fun a -> a#insert_command "Progress Trivial.\n"  "Trivial.\n" ))
	 );


  ignore (toolbar#insert_button
	    ~tooltip:"Proof Wizard"
	    ~text:"Wizard"
	    ~icon:(stock_to_widget ~size:`LARGE_TOOLBAR `DIALOG_INFO)
	    ~callback:(do_if_active (fun a -> a#insert_commands 
				       !current.automatic_tactics
				    ))
	    ());

  ignore (tactics_factory#add_item "<Proof _Wizard>"
	    ~key:GdkKeysyms._dollar
	    ~callback:(do_if_active (fun a -> a#insert_commands 
				       !current.automatic_tactics
				    ))
	 );
  
  (* Templates Menu *)
  let templates_menu =  factory#add_submenu "Te_mplates" in
  let templates_factory = new GMenu.factory templates_menu 
			    ~accel_path:"<CoqIde MenuBar>/Templates/"
			    ~accel_group 
			    ~accel_modi:!current.modifier_for_templates
  in
  let add_complex_template (menu_text, text, offset, len, key) =
    (* Templates/Lemma *)
    let callback = do_if_not_computing 
		     (fun () ->
			let {view = view } = get_current_view () in
			if view#buffer#insert_interactive text then begin
			  let iter = view#buffer#get_iter_at_mark `INSERT in
			  ignore (iter#nocopy#backward_chars offset);
			  view#buffer#move_mark `INSERT iter;
			  ignore (iter#nocopy#backward_chars len);
			  view#buffer#move_mark `SEL_BOUND iter;
			  Highlight.highlight_all view#buffer
			end)
    in
    ignore (templates_factory#add_item menu_text ~callback ?key)
  in
  add_complex_template 
    ("_Lemma __", "Lemma new_lemma : .\nProof.\n\nSave.\n", 
     19, 9, Some GdkKeysyms._L);
  add_complex_template 
    ("_Theorem __", "Theorem new_theorem : .\nProof.\n\nSave.\n", 
     19, 11, Some GdkKeysyms._T);
  add_complex_template 
    ("_Definition __", "Definition ident := .\n",
     6, 5, Some GdkKeysyms._D);
  add_complex_template 
    ("_Inductive __", "Inductive ident : :=\n  | : .\n",
     14, 5, Some GdkKeysyms._I);
  add_complex_template("_Scheme __",
		       "Scheme new_scheme := Induction for _ Sort _
with _ := Induction for _ Sort _.\n",61,10, Some GdkKeysyms._S);

  (* Template for Cases *)
  let callback = (fun () -> 
		    let w = get_current_word () in
		    try 
		      let cases = Coq.make_cases w
		      in
		      let print c = function
			| [x] -> fprintf c "  | %s => _@\n" x
			| x::l -> fprintf c "  | (%s%a) => _@\n" x 
			    (print_list (fun c s -> fprintf c " %s" s)) l
			| [] -> assert false
		      in
		      let b = Buffer.create 1024 in
		      let fmt = formatter_of_buffer b in
		      fprintf fmt "@[Cases var of@\n%aend@]@."
			(print_list print) cases;
		      let s = Buffer.contents b in
		      prerr_endline s;
		      let {view = view } = get_current_view () in
		      ignore (view#buffer#delete_selection ());
		      let m = view#buffer#create_mark 
				(view#buffer#get_iter `INSERT)
		      in
		      if view#buffer#insert_interactive s then 
			let i = view#buffer#get_iter (`MARK m) in
			let _ = i#nocopy#forward_chars 9 in
			view#buffer#place_cursor i;
			view#buffer#move_mark ~where:(i#backward_chars 3)
			  `SEL_BOUND 
		    with Not_found -> !flash_info "Not an inductive type"
		 )
  in
  ignore (templates_factory#add_item "Cases ..."
	    ~key:GdkKeysyms._C
	    ~callback
	 );
  
  let add_simple_template (factory: GMenu.menu GMenu.factory) 
    (menu_text, text) =
    ignore (factory#add_item menu_text
	      ~callback:
	      (do_if_not_computing 
		 (fun () -> let {view = view } = get_current_view () in
		  ignore (view#buffer#insert_interactive text))))
  in
  ignore (templates_factory#add_separator ());
  List.iter (add_simple_template templates_factory)
    [ "_Auto", "Auto ";
      "_Auto with *", "Auto with * ";
      "_EAuto", "EAuto ";
      "_EAuto with *", "EAuto with * ";
      "_Intuition", "Intuition ";
      "_Omega", "Omega ";
      "_Simpl", "Simpl ";
      "_Tauto", "Tauto ";
      "Tri_vial", "Trivial ";
    ];
  ignore (templates_factory#add_separator ());
  List.iter 
    (fun l -> 
       match l with 
       |[s] -> add_simple_template templates_factory ("_"^s, s^" ") 
       | [] -> ()
       | s::r -> 
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
		 x^" "))
	     l
    ) 
    Coq_commands.commands;
  
  (* Commands Menu *)
  let commands_menu =  factory#add_submenu "_Commands" in
  let commands_factory = new GMenu.factory commands_menu ~accel_group
			   ~accel_path:"<CoqIde MenuBar>/Commands"
			   ~accel_modi:[]
  in
  
  (* Command/Show commands *)
  let commands_show_m = commands_factory#add_item 
			  "_Show Window"
			  ~key:GdkKeysyms._F12
			  ~callback:(Command_windows.command_window ())
			  #window#present
  in  
  let _ = 
    commands_factory#add_item "_SearchAbout " ~key:GdkKeysyms._F2
      ~callback:(fun () -> let term = get_current_word () in
		 (Command_windows.command_window ())#new_command
		 ~command:"SearchAbout"
		   ~term 
		   ())
  in
  let _ = 
    commands_factory#add_item "_Check " ~key:GdkKeysyms._F3
      ~callback:(fun () -> let term = get_current_word () in
		 (Command_windows.command_window ())#new_command
		 ~command:"Check"
		   ~term 
		   ())
  in
  let _ = 
    commands_factory#add_item "_Print " ~key:GdkKeysyms._F4
      ~callback:(fun () -> let term = get_current_word () in
		 (Command_windows.command_window ())#new_command
		 ~command:"Print"
		   ~term 
		   ())
  in

  (* Externals *)
  let externals_menu =  factory#add_submenu "_Externals" in
  let externals_factory = new GMenu.factory externals_menu 
			    ~accel_path:"<CoqIde MenuBar>/Externals/"
			    ~accel_group in
  
  (* Command/Compile Menu *)
  let compile_f () =
    let v = get_current_view () in
    let av = out_some v.analyzed_view in
    save_f ();
    match av#filename with
    | None -> 
	!flash_info "Active buffer has no name"
    | Some f ->
	let s,res = run_command 
		      av#insert_message 
		      (!current.cmd_coqc ^ " " ^ f) 
	in
	if s = Unix.WEXITED 0 then
	  !flash_info (f ^ " successfully compiled")
	else begin
	  !flash_info (f ^ " failed to compile");
	  av#process_until_end_or_error;
	  av#insert_message "Compilation output:\n";
	  av#insert_message res
	end
  in
  let compile_m = externals_factory#add_item "_Compile" ~callback:compile_f in

  (* Command/Make Menu *)
  let make_f () =
    let v = get_active_view () in
    let av = out_some v.analyzed_view in
    save_f ();
    av#insert_message "Command output:\n";
    let s,res = run_command av#insert_message !current.cmd_make in
    !flash_info (!current.cmd_make ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let make_m = externals_factory#add_item "_Make" ~callback:make_f in
  
  (* Command/CoqMakefile Menu*)
  let coq_makefile_f () =
    let v = get_active_view () in
    let av = out_some v.analyzed_view in
    let s,res = run_command av#insert_message !current.cmd_coqmakefile in
    !flash_info 
      (!current.cmd_coqmakefile ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let _ = externals_factory#add_item "_Make Makefile" ~callback:coq_makefile_f 
  in
  (* Configuration Menu *)
  let reset_revert_timer () =
    disconnect_revert_timer ();
    if !current.global_auto_revert then 
      revert_timer := Some
	(GMain.Timeout.add ~ms:!current.global_auto_revert_delay 
	   ~callback:
	   (fun () -> 
	      do_if_not_computing (fun () -> revert_f ()) ();
	      true))
  in reset_revert_timer (); (* to enable statup preferences timer *)

  let auto_save_f () = 
    Vector.iter 
      (function 
	   {view = view ; analyzed_view = Some av} as full -> 
	     (try 
		av#auto_save
	      with _ -> ())
	 | _ -> ()
      )  
      input_views
  in

  let reset_auto_save_timer () =
    disconnect_auto_save_timer ();
    if !current.auto_save then 
      auto_save_timer := Some
	(GMain.Timeout.add ~ms:!current.auto_save_delay 
	   ~callback:
	   (fun () -> 
	      do_if_not_computing (fun () -> auto_save_f ()) ();
	      true))
  in reset_auto_save_timer (); (* to enable statup preferences timer *)

  let configuration_menu = factory#add_submenu "Confi_guration" in
  let configuration_factory = new GMenu.factory configuration_menu ~accel_path:"<CoqIde MenuBar>/Configuration" ~accel_group
  in
  let edit_prefs_m =
    configuration_factory#add_item "Edit _preferences"
      ~callback:(fun () -> configure ();reset_revert_timer ())
  in
  let save_prefs_m =
    configuration_factory#add_item "_Save preferences"
      ~callback:(fun () -> save_pref ())
  in
  let detach_menu = configuration_factory#add_item 
		      "_Detach Scripting Window"
		      ~callback:
		      (do_if_not_computing
			 (fun () -> 
			    let nb = notebook () in
			    if nb#misc#toplevel#get_oid=w#coerce#get_oid then
			      begin  
				let nw = GWindow.window ~show:true () in
				let parent = out_some nb#misc#parent in
				ignore (nw#connect#destroy 
					  ~callback:
					  (fun () -> nb#misc#reparent parent));
				nw#add_accel_group accel_group;
				nb#misc#reparent nw#coerce
			      end	      
			 ))
  in
  let detach_current_view = configuration_factory#add_item 
			      "De_tach View"
			      ~callback:
			      (do_if_not_computing
				 (fun () -> 
				    match get_current_view () with  
				    | {view=v;analyzed_view=Some av} -> 
			      		let w = GWindow.window ~show:true 
						  ~width:(!current.window_width/2)
						  ~height:(!current.window_height)
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
					av#add_detached_view w
				    | _ -> ()

				 ))
  in
  (* Help Menu *)

  let help_menu = factory#add_submenu "_Help" in
  let help_factory = new GMenu.factory help_menu  
		       ~accel_path:"<CoqIde MenuBar>/Help/"
		       ~accel_modi:[]
		       ~accel_group in
  let _ = help_factory#add_item "Browse Coq _Manual" 
	    ~callback:(fun () -> browse (!current.doc_url ^ "main.html")) in
  let _ = help_factory#add_item "Browse Coq _Library" 
	    ~callback:(fun () -> browse !current.library_url) in
  let _ = 
    help_factory#add_item "Help for _keyword" ~key:GdkKeysyms._F1
      ~callback:(fun () -> 
		   let av = out_some ((get_current_view ()).analyzed_view) in 
		   av#help_for_keyword ())
  in
  let _ = help_factory#add_separator () in
  let faq_m = help_factory#add_item "_FAQ" in
  let about_m = help_factory#add_item "_About" in

  (* End of menu *)

  (* The vertical Separator between Scripts and Goals *)
  let hb = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in
  _notebook := Some (GPack.notebook ~scrollable:true 
		       ~packing:hb#add1
		       ());
  let nb = notebook () in
  let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add2 () in 
  let hb2 = GPack.paned `VERTICAL  ~border_width:3 ~packing:fr2#add () in
  let sw2 = GBin.scrolled_window 
	      ~vpolicy:`AUTOMATIC 
	      ~hpolicy:`AUTOMATIC
	      ~packing:(hb2#add) () in
  let sw3 = GBin.scrolled_window 
	      ~vpolicy:`AUTOMATIC 
	      ~hpolicy:`AUTOMATIC
	      ~packing:(hb2#add) () in
  let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  let status_bar = GMisc.statusbar ~packing:(lower_hbox#pack ~expand:true) () 
  in
  let search_lbl = GMisc.label ~text:"Search:"
		     ~show:false
		     ~packing:(lower_hbox#pack ~expand:false) () 
  in
  let search_history = ref [] in
  let search_input = GEdit.combo ~popdown_strings:!search_history
		       ~use_arrows:`DEFAULT
		       ~show:false
		       ~packing:(lower_hbox#pack ~expand:false) () 
  in
  search_input#disable_activate ();
  let ready_to_wrap_search = ref false in
  let start_of_search = ref None in
  let search_forward = ref true in
  let memo_search () = 
    if not (List.mem search_input#entry#text !search_history) then
      (search_history := 
       search_input#entry#text::!search_history;
       search_input#set_popdown_strings !search_history);
    start_of_search := None;
    ready_to_wrap_search := false
  in
  let end_search () = 
    prerr_endline "End Search";
    memo_search ();
    let v = (get_current_view ()).view in
    v#buffer#move_mark `SEL_BOUND (v#buffer#get_iter_at_mark `INSERT);
    v#coerce#misc#grab_focus ();
    search_input#entry#set_text "";
    search_lbl#misc#hide ();
    search_input#misc#hide ()
  in

  ignore (search_input#entry#connect#activate ~callback:end_search);
  to_do_on_page_switch := 
  (fun i -> 
     start_of_search := None;
     ready_to_wrap_search:=false)::!to_do_on_page_switch;

  let rec search_f () = 
    search_lbl#misc#show ();
    search_input#misc#show ();

    prerr_endline "search_f called";
    if !start_of_search = None then 
      start_of_search := 
      Some ((get_current_view ()).view#buffer#create_mark 
	      ((get_current_view ()).view#buffer#get_iter_at_mark `INSERT));
    let txt = search_input#entry#text in 
    let v = (get_current_view ()).view in
    let iit = v#buffer#get_iter_at_mark `SEL_BOUND in
    prerr_endline ("SELBOUND="^(string_of_int iit#offset));
    prerr_endline ("INSERT="^(string_of_int 
				(v#buffer#get_iter_at_mark `INSERT)#offset));
    
    (match
       if !search_forward then iit#forward_search txt 
       else let npi = iit#forward_chars (Glib.Utf8.length txt) in
       match 
	 (npi#offset = (v#buffer#get_iter_at_mark `INSERT)#offset),
	 (let t = iit#get_text ~stop:npi in 
	  !flash_info (t^"\n"^txt);
	  t = txt)
       with 
       | true,true -> 
	   (!flash_info "T,T";iit#backward_search txt)
       | false,true -> !flash_info "F,T";Some (iit,npi)
       | _,false ->
	   (iit#backward_search txt)

       with 
       | None -> 
	   if !ready_to_wrap_search then begin
	     ready_to_wrap_search := false;
	     !flash_info "Search wrapped";
	     v#buffer#place_cursor 
	       (if !search_forward then v#buffer#start_iter else
		  v#buffer#end_iter);
	     search_f ()
	   end else begin
	     if !search_forward then !flash_info "Search at end"
	     else !flash_info "Search at start";
	     ready_to_wrap_search := true
	   end
       | Some (start,stop) -> 
	   prerr_endline "search: before moving marks";
	   prerr_endline ("SELBOUND="^(string_of_int (v#buffer#get_iter_at_mark `SEL_BOUND)#offset));
	   prerr_endline ("INSERT="^(string_of_int (v#buffer#get_iter_at_mark `INSERT)#offset));

	   v#buffer#move_mark `SEL_BOUND start;
	   v#buffer#move_mark `INSERT stop;
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
		 let v = (get_current_view ()).view in
		 (match !start_of_search with 
		  | None -> 
		      prerr_endline "search_key_rel: Placing sel_bound";
		      v#buffer#move_mark 
			`SEL_BOUND 
			(v#buffer#get_iter_at_mark `INSERT)
		  | Some mk -> let it = v#buffer#get_iter_at_mark 
					  (`MARK mk) in
		    prerr_endline "search_key_rel: Placing cursor";
		    v#buffer#place_cursor it;
		    start_of_search := None
		 );
		 search_input#entry#set_text ""; 
		 v#coerce#misc#grab_focus ();
	       end; 
	       false
	    ));
  ignore (search_input#entry#connect#changed search_f);
  
  ignore (search_if#connect#activate
	    ~callback:(fun b -> 
			 search_forward:= true;
			 search_input#entry#coerce#misc#grab_focus ();
			 search_f ();
		      )
	 );
  ignore (search_ib#connect#activate
	    ~callback:(fun b ->
			 search_forward:= false;

			 (* Must restore the SEL_BOUND mark after 
			    grab_focus ! *)
			 let v = (get_current_view ()).view in
			 let old_sel = v#buffer#get_iter_at_mark `SEL_BOUND 
			 in
			 search_input#entry#coerce#misc#grab_focus ();
			 v#buffer#move_mark `SEL_BOUND old_sel;
			 search_f ();
		      ));
  let status_context = status_bar#new_context "Messages" in
  let flash_context = status_bar#new_context "Flash" in
  ignore (status_context#push "Ready");
  status := Some status_bar;
  push_info := (fun s -> ignore (status_context#push s));
  pop_info := (fun () -> status_context#pop ());
  flash_info := (fun ?(delay=5000) s -> flash_context#flash ~delay s);

  (* Location display *)
  let l = GMisc.label
	    ~text:"Line:     1 Char:   1" 
	    ~packing:lower_hbox#pack () in 
  l#coerce#misc#set_name "location";
  set_location := l#set_text;

  (* Progress Bar *)
  pulse := 
  (GRange.progress_bar ~text:"CoqIde started" ~pulse_step:0.2 ~packing:lower_hbox#pack ())#pulse;
  let tv2 = GText.view ~packing:(sw2#add) () in
  tv2#misc#set_name "GoalWindow";
  let _ = tv2#set_editable false in
  let tb2 = tv2#buffer in
  let tv3 = GText.view ~packing:(sw3#add) () in
  tv2#misc#set_name "MessageWindow";
  let _ = tv2#set_wrap_mode `CHAR in
  let _ = tv3#set_wrap_mode `WORD in
  let _ = tv3#set_editable false in
  let _ = GtkBase.Widget.add_events tv2#as_widget
	    [`ENTER_NOTIFY;`POINTER_MOTION] in
  let _ = tv2#event#connect#motion_notify
	    ~callback:
	    (fun e -> 
	       (do_if_not_computing
		  (fun e -> 
		     let win = match tv2#get_window `WIDGET with
		       | None -> assert false
		       | Some w -> w
		     in
		     let x,y = Gdk.Window.get_pointer_location win in
		     let b_x,b_y = tv2#window_to_buffer_coords 
				     ~tag:`WIDGET 
				     ~x 
				     ~y 
		     in
		     let it = tv2#get_iter_at_location ~x:b_x ~y:b_y in
		     let tags = it#tags in
		     List.iter 
		       ( fun t ->
			   ignore (GtkText.Tag.event 
				     t#as_tag
				     tv2#as_widget
				     e 
				     it#as_textiter))
		       tags;
		     false)) e;
	       false)
  in
  change_font := 
  (fun fd -> 
     tv2#misc#modify_font fd;
     tv3#misc#modify_font fd;
     Vector.iter 
       (fun {view=view} -> view#misc#modify_font fd)
       input_views;
  );
  (try 
     let image = Filename.concat lib_ide "coq.png" in
     let startup_image = GdkPixbuf.from_file image in
     tv2#buffer#insert_pixbuf ~iter:tv2#buffer#start_iter 
       ~pixbuf:startup_image;
     tv2#buffer#insert ~iter:tv2#buffer#start_iter "\t\t";
   with _ -> ());
  tv2#buffer#insert "\nCoqIde: an experimental Gtk2 interface for Coq.\n";
  tv2#buffer#insert ((Coq.version ()));
  w#add_accel_group accel_group;
  (* Remove default pango menu for textviews *)
  ignore (tv2#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));
  ignore (tv3#event#connect#button_press ~callback:
	    (fun ev -> GdkEvent.Button.button ev = 3));
  tv2#misc#set_can_focus true;
  tv3#misc#set_can_focus true;
  ignore (tv2#buffer#create_mark 
	    ~name:"end_of_conclusion" 
	    tv2#buffer#start_iter);
  ignore (tv3#buffer#create_tag 
	    ~name:"error" 
	    [`FOREGROUND "red"]);
  w#show ();
  message_view := Some tv3;
  proof_view := Some tv2;
  let view = create_input_tab "*Unnamed Buffer*" in
  let index = add_input_view {view = view;
			      analyzed_view = None;
			     }
  in
  (get_input_view index).analyzed_view <- Some (new analyzed_view index);
  activate_input index;
  set_tab_image index yes_icon;
  view#misc#modify_font !current.text_font; 
  tv2#misc#modify_font !current.text_font; 
  tv3#misc#modify_font !current.text_font;
  ignore (about_m#connect#activate 
	    ~callback:(fun () -> tv3#buffer#set_text "by Benjamin Monate"));
  ignore (faq_m#connect#activate 
	    ~callback:(fun () -> 
			 load (Filename.concat lib_ide "FAQ")));
  
  resize_window := (fun () -> 
		      w#resize 
		      ~width:!current.window_width
		      ~height:!current.window_height);

  ignore (w#misc#connect#size_allocate 
	    (let old_w = ref 0 
	     and old_h = ref 0 in
	     fun {Gtk.width=w;Gtk.height=h} -> 
	       if !old_w <> w or !old_h <> h then
		 begin
		   old_h := h;
		   old_w := w;
		   hb#set_position (w/2);
		   hb2#set_position (h/2);
		   !current.window_height <- h;
		   !current.window_width <- w;
		 end
	    ));
  ignore(nb#connect#switch_page 
	   ~callback:
	   (fun i -> List.iter (function f -> f i) !to_do_on_page_switch)
	);
  ignore(tv2#event#connect#enter_notify
	   (fun _ -> 
	      let w = (out_some (get_active_view ()).analyzed_view) in
	      !push_info "Computing advanced goal's menus";
	      prerr_endline "Entering Goal Window. Computing Menus....";
	      w#show_goals_full;
	      prerr_endline "....Done with Goal menu";
	      !pop_info();
	      false;
	   ));
  List.iter load files;
  if List.length files >=1 then activate_input 1
;;

let start () = 
  let files = Coq.init () in
  ignore_break ();
  GtkMain.Rc.add_default_file (Filename.concat lib_ide ".coqide-gtk2rc");
  (try 
     GtkMain.Rc.add_default_file (Filename.concat (Sys.getenv "HOME") ".coqide-gtk2rc");
  with Not_found -> ());
  ignore (GtkMain.Main.init ());
  GtkData.AccelGroup.set_default_mod_mask 
    (Some [`CONTROL;`SHIFT;`MOD1;`MOD3;`MOD4]);
  cb_ := Some (GtkBase.Clipboard.get Gdk.Atom.primary);
  Glib.Message.set_log_handler ~domain:"Gtk" ~levels:[`ERROR;`FLAG_FATAL;
						      `WARNING;`CRITICAL]
    (fun ~level msg -> failwith ("Coqide internal error: " ^ msg));
  Command_windows.main ();
  Blaster_window.main 9;
  main files;
  while true do 
    try 
      GtkThread.main ()
    with
      | Sys.Break -> prerr_endline "Interrupted." ; flush stderr
      | e -> 
	  Pervasives.prerr_endline ("CoqIde unexpected error:" ^ (Printexc.to_string e));
	  flush stderr;
	  crash_save 127
  done
