let window_width = 1280
let window_height = 1024


let monospace_font = ref (Pango.Font.from_string "Courier bold 14")
let general_font = ref !monospace_font
let lower_view_general_font = ref (Pango.Font.from_string "Courier bold 14")
let upper_view_general_font = ref !general_font
let statusbar_font = ref !general_font
let proved_lemma_font = ref !monospace_font
let to_prove_lemma_font = ref !monospace_font
let discharged_lemma_font = ref !monospace_font

let (load_m:GMenu.menu_item option ref) = ref None
let (save_m:GMenu.menu_item option ref) = ref None
let (rehighlight_m:GMenu.menu_item option ref) = ref None
let (refresh_m:GMenu.menu_item option ref) = ref None
let last_filename = ref None

let status = ref None
let push_info = ref (function s -> failwith "not ready")
let pop_info = ref (function s -> failwith "not ready")
let flash_info = ref  (function s -> failwith "not ready")

let out_some s = match s with | None -> assert false | Some f -> f

let try_convert s = 
  try
    if Glib.Utf8.validate s then s else
      (prerr_endline 
	 "Coqide warning: input is not UTF-8 encoded. Trying to convert from locale.";
       Glib.Convert.locale_to_utf8 s)
  with _ -> 
    "(* Fatal error: wrong encoding in input.
Please set your locale according to your file encoding.*)"

let try_export file_name s = 
  try 
    let s = Glib.Convert.locale_from_utf8 s in
    let oc = open_out file_name in
    output_string oc s;
    close_out oc
  with e -> prerr_endline (Printexc.to_string e)

let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
  while len := input ic buf 0 1024; !len > 0 do
    Buffer.add_substring b buf 0 !len
  done

let with_file name ~f =
  let ic = open_in name in
  try f ic; close_in ic with exn -> close_in ic; raise exn

type info =  {start:GText.mark;
	      stop:GText.mark;
	      ast:Vernacexpr.vernac_expr}
exception Size of int
let (processed_stack:info Stack.t) = Stack.create ()
let push x = Stack.push x processed_stack
let pop () = try Stack.pop processed_stack with Stack.Empty -> raise (Size 0)
let top () = try Stack.top processed_stack with Stack.Empty -> raise (Size 0)
let top_top () =
    let first = pop () in
    let snd = try top () with Size 0 -> push first; raise (Size 1) in
    push first;
   snd

(* For electric handlers *)
exception Found

(* For find_phrase_starting_at *)
exception Stop of int

let set_break () = 
  Sys.set_signal Sys.sigusr1 (Sys.Signal_handle (fun _ -> raise Sys.Break))
let unset_break () = 
  Sys.set_signal Sys.sigusr1 Sys.Signal_ignore

let pid = Unix.getpid ()

let break () = Unix.kill pid Sys.sigusr1
let can_break () = set_break () 
(* ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigusr1])*) 
let cant_break () = unset_break () 
(* ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigusr1])*)


(* Get back the standard coq out channels *)
let read_stdout,clear_stdout =
  let out_buff = Buffer.create 100 in
  Pp_control.std_ft := Format.formatter_of_buffer out_buff;
  (fun () -> Format.pp_print_flush !Pp_control.std_ft (); 
     let r = Buffer.contents out_buff in
     Buffer.clear out_buff; r),
  (fun () -> 
     Format.pp_print_flush !Pp_control.std_ft (); Buffer.clear out_buff)

let process_pending () = 
  while Glib.Main.pending () do 
    ignore (Glib.Main.iteration false) 
  done

let find_tag_limits (tag :GText.tag) (it:GText.iter) = 
  let start_it = it#copy in
    if not (start_it#begins_tag ~tag ()) 
    then ignore (start_it#backward_to_tag_toggle ~tag ());
    let end_it = it#copy in
      if not (end_it#ends_tag ~tag ())
      then ignore (end_it#forward_to_tag_toggle ~tag ());
      start_it,end_it

let analyze_all 
  (input_view:GText.view) 
  (proof_view:GText.view) 
  (message_view:GText.view)
  =
  let input_buffer = input_view#get_buffer in
  let proof_buffer = proof_view#get_buffer in
  let message_buffer = message_view#get_buffer in
  let insert_message s =
    message_buffer#insert s;
    message_view#misc#draw None
  in
  let set_message s =
    message_buffer#set_text s;
    message_view#misc#draw None
  in
  let clear_message () =
    message_buffer#set_text ""
  in
  ignore (message_view#get_buffer#connect#after#insert_text
	    ~callback:(fun it s -> ignore (message_view#scroll_to_mark
					     ~within_margin:0.49
					     (message_buffer#get_insert))));
  let last_index = ref true in
  let last_array = [|"";""|] in
  let get_start_of_input () = 
    input_buffer#get_iter_at_mark 
      (input_buffer#get_mark ~name:"start_of_input") 
  in
  ignore (input_buffer#connect#changed
	    ~callback:(fun () -> 
			 input_buffer#remove_tag_by_name 
			 ~start:(get_start_of_input())
			 ~stop:input_buffer#get_end_iter
			 "error"));

  let get_insert () = input_buffer#get_iter_at_mark (input_buffer#get_insert) in
  let highlight_slice start stop = 
    let offset = start#get_offset in
    let s = Glib.Convert.locale_from_utf8 (input_buffer#get_slice ~start ~stop ()) in
    let lb = Lexing.from_string s in
    try 
      while true do
	process_pending ();
	let b,e,o=Highlight.next_order lb in
	let start = input_buffer#get_iter_at ~char_offset:(offset + b) () in
	let stop = input_buffer#get_iter_at ~char_offset:(offset + e) () in
	input_buffer#apply_tag_by_name ~start ~stop o 
      done
    with End_of_file -> ()
      | _ -> ()
  in    
  let highlight_current_line () = 
    let i = get_insert () in
    ignore (i#set_line_offset 0);
    highlight_slice i (get_insert ())
  in
  let highlight_all () = 
    highlight_slice input_buffer#get_start_iter input_buffer#get_end_iter in      
  let rec show_goals () = 
    proof_view#get_buffer#set_text "";
    let s = Coq.get_curent_goals () in
    let last_shown_area = proof_buffer#create_tag
			    ~properties:[`BACKGROUND "light blue"]
			    ()
    in
    match s with 
      | [] -> proof_buffer#insert (Coq.print_no_goal ())
      | (hyps,(_,concl))::r -> 
	  let goal_nb = List.length s in
	  proof_buffer#insert (Printf.sprintf "%d subgoal%s\n" 
				 goal_nb
				 (if goal_nb<=1 then "" else "s"));
	  List.iter 
	    (fun (((coqident,ident),_,ast),(s,pr_ast)) -> 
	       let tag = proof_buffer#create_tag ()
	       in 
	       ignore
		 (tag#connect#event
		    ~callback:
		    (fun ~origin ev it ->
		       match GdkEvent.get_type ev with 
			 | `BUTTON_PRESS -> 
			     let ev = (GdkEvent.Button.cast ev) in
			     if (GdkEvent.Button.button ev) = 3 
			     then begin 
			       let loc_menu = GMenu.menu () in
			       let factory = new GMenu.factory loc_menu in
			       let add_coq_command cp ip = 
				 ignore (factory#add_item cp 
					   ~callback:
					   (fun () -> ignore
					      (insert_this_phrase_on_success 
						 true 
						 false 
						 (ip^"\n") 
						 (ip^"\n"))
					   )
					)
			       in
			       add_coq_command 
				 ("Clear "^ident^".")  
				 ("Clear "^ident^".");
			       add_coq_command 
				 ("Elim "^ident^".")
				 ("Elim "^ident^".");
			       add_coq_command 
				 ("Apply "^ident^".")
				 ("Apply "^ident^".");
			       add_coq_command 
				 ("Generalize "^ident^".")
				 ("Generalize "^ident^".");
			       add_coq_command 
				 ("Assumption.")
				 ("Assumption.");
			       add_coq_command	
				 ("Absurd <"^ident^">")
				 ("Absurd "^
				  pr_ast
				  ^".");
			       add_coq_command 
				 ("Discriminate "^ident^".")
				 ("Discriminate "^ident^".");
			       add_coq_command 
				 ("Injection "^ident^".")
				 ("Injection "^ident^".");
			       add_coq_command 
				 ("Rewrite "^ident^".")
				 ("Rewrite "^ident^".");
			       add_coq_command 
				 ("Rewrite <- "^ident^".")
				 ("Rewrite <- "^ident^".");
			       add_coq_command 
				 ("Inversion "^ident^".")
				 ("Inversion "^ident^".");
			       add_coq_command 
				 ("Inversion_clear "^ident^".")
				 ("Inversion_clear "^ident^".");
			       loc_menu#popup 
				 ~button:3
				 ~time:(GdkEvent.Button.time ev);
			     end
			 | `MOTION_NOTIFY -> 
			     proof_buffer#remove_tag
			     ~start:proof_buffer#get_start_iter
			     ~stop:proof_buffer#get_end_iter
			     last_shown_area;
			     let s,e = find_tag_limits tag 
					 (new GText.iter it) 
			     in
			     proof_buffer#apply_tag 
			       ~start:s 
			       ~stop:e 
			       last_shown_area;
			     ()
			 | _ -> ())
		 );
	       proof_buffer#insert ~tags:[tag] (s^"\n"))
	    hyps;
	  proof_buffer#insert ("--------------------------------------(1/"^
			       (string_of_int goal_nb)^
			       ")\n") 
	    ;
	  proof_buffer#insert concl;
	  proof_buffer#insert "\n";
	  let my_mark = proof_buffer#get_mark ~name:"end_of_conclusion" in
	  proof_buffer#move_mark
	    ~where:((proof_buffer#get_iter_at_mark proof_buffer#get_insert))
	    my_mark;
	  proof_buffer#insert "\n\n";
	  let i = ref 1 in
	  List.iter 
	    (function (_,(_,concl)) -> 
	       incr i;
	       proof_buffer#insert ("----------------------------------------("^
				    (string_of_int !i)^
				    "/"^
				    (string_of_int goal_nb)^
				    ")\n");
	       proof_buffer#insert concl;
	       proof_buffer#insert "\n\n";
	    )
	    r;
	  ignore (proof_view#scroll_to_mark my_mark)
  and send_to_coq phrase show_error localize = 
    try
      !push_info "Coq is computing";
      (out_some !status)#misc#draw None;
      input_view#set_editable false;
      can_break ();
      let r = Some (Coq.interp phrase) in
      cant_break ();
      input_view#set_editable true;
      !pop_info ();
      (out_some !status)#misc#draw None;
      insert_message (read_stdout ());
      r
    with e ->
      input_view#set_editable true;
      !pop_info ();
      (if show_error then
	 let (s,loc) = Coq.process_exn e in
	 assert (Glib.Utf8.validate s);
	 set_message s;
	 message_view#misc#draw None;
	 if localize then 
	   (match loc with 
	      | None -> ()
	      | Some (start,stop) -> 
		  let i = get_start_of_input() in 
		  let starti = i#copy in
		  ignore (starti#forward_chars start);
		  let stopi = i#copy in
		  ignore (stopi#forward_chars stop);
		  input_buffer#apply_tag_by_name "error"
   		    ~start:starti
		    ~stop:stopi
	   ));
      None
  and find_phrase_starting_at (start:GText.iter) = 
    let end_iter = start#copy in
    let lexbuf_function s count =
      try for i = 0 to (count-1) do
	let c = end_iter#get_char in
	if c='\000' then raise (Stop 0);
	s.[i] <- c;	
	if not (end_iter#forward_char ()) then 
	  raise (Stop (i+1))
      done;
	count
      with Stop x -> x
    in
    try
      Find_phrase.length := 0;
      let phrase = Find_phrase.next_phrase (Lexing.from_function lexbuf_function) in
      end_iter#set_offset (start#get_offset + !Find_phrase.length);
      Some (start,end_iter)
    with _ -> None
  and process_next_phrase display_goals = 
    clear_message ();
    match (find_phrase_starting_at (get_start_of_input ()))
    with None -> false
      | Some(start,stop) ->
	  let b = input_buffer in
	  let phrase = b#get_slice ~start ~stop () in
	  match send_to_coq phrase true true with
	    | Some ast ->
		begin
		  b#move_mark_by_name ~where:stop "start_of_input";
		  b#apply_tag_by_name "processed" ~start ~stop;
		  if ((get_insert())#compare) stop <= 0 then 
		    (b#place_cursor stop;
		     ignore (input_view#scroll_to_iter 
			       ~within_margin:0.2 (get_insert())));
		  let start_of_phrase_mark = b#create_mark start in
		  let end_of_phrase_mark = b#create_mark stop in
		  push
		    {start = start_of_phrase_mark;
		     stop = end_of_phrase_mark;
		     ast= ast};
		  if display_goals then
		    (try show_goals () with e -> ());
		  true;
		end
	    | None -> false
  and insert_this_phrase_on_success show_msg localize coqphrase insertphrase = 
    match send_to_coq coqphrase show_msg localize with
      | Some ast ->
	  begin
	    let stop = get_start_of_input () in
	    if stop#starts_line then
	      input_buffer#insert ~iter:stop insertphrase
	    else input_buffer#insert ~iter:stop ("\n"^insertphrase); 
	    let start = get_start_of_input () in
	    input_buffer#move_mark_by_name ~where:stop "start_of_input";
	    input_buffer#apply_tag_by_name "processed" ~start ~stop;
	    if ((get_insert())#compare) stop <= 0 then 
	      input_buffer#place_cursor stop;
	    let start_of_phrase_mark = input_buffer#create_mark start in
	    let end_of_phrase_mark = input_buffer#create_mark stop in
	    push
	      {start = start_of_phrase_mark;
	       stop = end_of_phrase_mark;
	       ast= ast};
	    (try show_goals () with e -> ());
	    true
	  end
      | None -> insert_message ("Unsuccesfully tried: "^coqphrase);
	  false
  in
  let process_until_iter_or_error stop =
    let start = (get_start_of_input ())#copy in
    input_buffer#apply_tag_by_name 
      ~start
      ~stop
      "to_process";
    while ((stop#compare (get_start_of_input ())>=0) && process_next_phrase false)
    do () done;
    (try show_goals () with _ -> ());
    input_buffer#remove_tag_by_name ~start ~stop "to_process" ;

  in  
  let process_until_insert_or_error () = 
    let stop = get_insert () in
    process_until_iter_or_error stop
  in  
  let reset_initial () = 
    Stack.iter 
      (function inf -> 
	 let start = input_buffer#get_iter_at_mark inf.start in
	 let stop = input_buffer#get_iter_at_mark inf.stop in
	 input_buffer#move_mark_by_name ~where:start "start_of_input";
	 input_buffer#remove_tag_by_name "processed" ~start ~stop;
	 input_buffer#delete_mark inf.start;
	 input_buffer#delete_mark inf.stop;
      ) 
      processed_stack;
    Stack.clear processed_stack;
    clear_message ();
    send_to_coq "\nReset Initial.\n" true true
  in
  let undo_last_step () = 
    try 
      let come_back_iter = input_buffer#get_iter_at_mark (top_top ()).start in
      ignore (reset_initial ());
      (*      message_buffer#insert "(* Replaying to undo *)\n" ();*)
      process_until_iter_or_error come_back_iter;
      input_buffer#place_cursor 
	(input_buffer#get_iter_at_mark 
	   (input_buffer#get_mark ~name:"start_of_input"));
      (*      message_buffer#insert "\n(* End of replay *)\n" ();*)
    with 
      | Size 0 -> !flash_info "Nothing to Undo"
      | Size 1 -> ignore (reset_initial ())
  in
  let (* TODO *) undo_just_before (i:GText.iter) =
    while (i#get_marks<>[] && (i#backward_char ())) do () done;
    ()
  in
  let undo_until_pointer () = 
    undo_just_before 
      (let win = match input_view#get_window `WIDGET with
	 | None -> assert false
	 | Some w -> w
       in
       let x,y = Gdk.Window.get_pointer_location win in
       let b_x,b_y = input_view#window_to_buffer_coords 
		       ~tag:`WIDGET 
		       ~x 
		       ~y 
       in
       input_view#get_iter_at_location ~x:b_x ~y:b_y)
  in
  let insert_command cp ip = 
    clear_message ();
    ignore (insert_this_phrase_on_success false false cp ip) in
  let insert_commands l = 
    clear_message ();
    ignore (List.exists (fun (cp,ip) -> 
			   insert_this_phrase_on_success false false cp ip) l)
  in
  let _ = input_view#event#connect#key_press 
	    (function k -> 
	       match GdkEvent.Key.state k with
		 | [`MOD1] | [`CONTROL;`MOD1] | [`MOD1;`CONTROL]-> 
		     let k = GdkEvent.Key.keyval k in
		     if GdkKeysyms._Down=k 
		     then ignore (process_next_phrase true) 
		     else if GdkKeysyms._Right=k 
		     then process_until_insert_or_error () 
		     else if GdkKeysyms._Left=k 
		     then (
		       ignore(reset_initial ());
		       process_until_insert_or_error ())
		     else if GdkKeysyms._r=k 
		     then ignore (reset_initial ())
		     else if GdkKeysyms._Up=k 
		     then ignore (undo_last_step ())
		     else if GdkKeysyms._Return=k
		     then ignore(
		       if (input_buffer#insert_interactive "\n") then
			 begin
			   let i= get_insert() in
			   ignore (i#backward_word_start ());
			   input_buffer#place_cursor i;
			   process_until_insert_or_error ()
			 end)
		     else if GdkKeysyms._a=k 
		     then insert_command "Progress Auto.\n" "Auto.\n"
		     else if GdkKeysyms._i=k 
		     then insert_command "Progress Intuition.\n" "Intuition.\n"
		     else if GdkKeysyms._t=k 
		     then insert_command "Progress Trivial.\n"  "Trivial.\n"
		     else if GdkKeysyms._o=k 
		     then insert_command "Omega.\n" "Omega.\n"
		     else if GdkKeysyms._s=k 
		     then insert_command "Progress Simpl.\n" "Simpl.\n"
		     else if GdkKeysyms._e=k 
		     then insert_command 
		       "Progress EAuto with *.\n" 
		       "EAuto with *.\n"
		     else if GdkKeysyms._asterisk=k 
		     then insert_command 
		       "Progress Auto with *.\n"
		       "Auto with *.\n"
		     else if GdkKeysyms._dollar=k 
		     then insert_commands 
		       ["Progress Trivial.\n","Trivial.\n";
			"Progress Auto.\n","Auto.\n";
			"Tauto.\n","Tauto.\n";
			"Omega.\n","Omega.\n";
			"Progress Auto with *.\n","Auto with *.\n";
			"Progress EAuto with *.\n","EAuto with *.\n";
			"Progress Intuition.\n","Intuition.\n";
		       ];
		     true 
		 | [] -> 
		     let k = GdkEvent.Key.keyval k in
		     if GdkKeysyms._Return=k
		     then
		       highlight_current_line ();
		     false
		 | [`CONTROL] -> 
		     let k = GdkEvent.Key.keyval k in
		     if GdkKeysyms._c=k
		     then break ();
		     false
		 | l -> false)
  in
  ignore
    ((out_some !load_m)#connect#activate
       (fun () -> 
	  match GToolbox.select_file ~title:"Load file" () with 
	    | None -> ()
	    | Some f -> 
		try
		  let b = Buffer.create 1024 in
		  with_file f ~f:(input_channel b);
		  let s = try_convert (Buffer.contents b) 
		  in
		  ignore (reset_initial ());
		  input_buffer#set_text s;
		  input_buffer#place_cursor input_buffer#get_start_iter;
		  highlight_all ();
		  last_filename := Some f;
		with e -> !flash_info "Load failed"
       ));
  ignore
    ((out_some !save_m)#connect#activate
       (fun () ->

	  try match !last_filename with 
	    | None -> 
		begin match GToolbox.select_file ~title:"Save file" ()
		with 
		  | None -> ()
		  | Some f -> 
		      try_export f (input_buffer#get_text ());
		      last_filename := Some f;
		end
	    | Some f -> try_export f (input_buffer#get_text ())
	  with e -> !flash_info "Save failed"
	    
       ));
  ignore
    ((out_some !rehighlight_m)#connect#activate
       highlight_all);
  let electric_handler () = 
    input_buffer#connect#insert_text ~callback:
      (fun it x -> 
	 begin try
	   if !last_index then begin
	     last_array.(0)<-x;
	     if (last_array.(1) ^ last_array.(0) = ".\n") then raise Found
	   end else begin
	     last_array.(1)<-x;
	     if (last_array.(0) ^ last_array.(1) = ".\n") then raise Found
	   end
	 with Found -> 
	   begin
	     ignore (process_next_phrase true)
	   end;
	 end;
	 last_index := not !last_index;)
  in
  ()

let main () = 
  let w = GWindow.window 
	    ~allow_grow:true ~allow_shrink:true ~width:window_width ~height:window_height ~title:"CoqIde" ()
  in
  w#misc#modify_font !general_font;
  let accel_group = GtkData.AccelGroup.create () in
  let _ = w#connect#destroy ~callback:(fun () -> exit 0) in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in
  let menubar = GMenu.menu_bar ~packing:vbox#pack () in
  let factory = new GMenu.factory menubar in
  let accel_group = factory#accel_group in
  let file_menu = factory#add_submenu "File" in
  let file_factory = new GMenu.factory file_menu ~accel_group in
  load_m := Some (file_factory#add_item "Open" ~key:GdkKeysyms._O);
  save_m := Some (file_factory#add_item "Save" ~key:GdkKeysyms._S);
  rehighlight_m := Some (file_factory#add_item "Rehighlight" 
			   ~key:GdkKeysyms._L);
  refresh_m := Some (file_factory#add_item "Restart all" ~key:GdkKeysyms._R);
  let quit_m = file_factory#add_item "Quit" ~key:GdkKeysyms._Q
		 ~callback:(fun () -> exit 0) in

  let configuration_menu = factory#add_submenu "Configuration" in
  let configuration_factory = new GMenu.factory configuration_menu ~accel_group
  in
(*  let show_discharged_m = configuration_factory#add_check_item 
			    "Show discharged proof" 
			    ~key:GdkKeysyms._D
			    ~callback:(fun b -> () (*show_discharged := b*)) 
  in*)
  let customize_colors_m =
    configuration_factory#add_item "Customize colors"
      ~callback:(fun () -> !flash_info "Not implemented")
  in
  let customize_fonts_m = 
    configuration_factory#add_item "Customize fonts"
      ~callback:(fun () -> !flash_info "Not implemented")
  in
  let hb = GPack.paned `HORIZONTAL  ~border_width:3 ~packing:vbox#add () in
  let _ = hb#set_position (window_width*6/10 ) in
  let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add1 () in 
  let sw1 = GBin.scrolled_window
	      ~vpolicy:`AUTOMATIC 
	      ~hpolicy:`AUTOMATIC
	      ~packing:fr1#add () in
  let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT ~packing:hb#add2 () in 
  let hb2 = GPack.paned `VERTICAL  ~border_width:3 ~packing:fr2#add () in
  hb2#set_position (window_height*7/10);
  let sw2 = GBin.scrolled_window 
	      ~vpolicy:`AUTOMATIC 
	      ~hpolicy:`AUTOMATIC
	      ~packing:(hb2#add) () in
  let sw3 = GBin.scrolled_window 
	      ~vpolicy:`AUTOMATIC 
	      ~hpolicy:`AUTOMATIC
	      ~packing:(hb2#add) () in
  let status_bar = GMisc.statusbar ~packing:vbox#pack () in
  status_bar#misc#modify_font !statusbar_font ;
  let status_context = status_bar#new_context "Messages" in
  ignore (status_context#push "Ready");
  status := Some status_bar;
  push_info := (fun s -> ignore (status_context#push s));
  pop_info := (fun () -> status_context#pop ());
  flash_info := (fun s -> status_context#flash ~delay:5000 s);
  let tv2 = GText.view ~packing:(sw2#add) () in
  let _ = tv2#misc#modify_font !lower_view_general_font in
  let _ = tv2#set_editable false in
  let b = GText.buffer () in 
  let tb2 = tv2#get_buffer in
  let tv1 = GText.view ~buffer:b ~packing:(sw1#add) () in
  let _ = tv1#misc#modify_font !upper_view_general_font in
  let _ = tv1#set_editable true in
  let tv3 = GText.view ~packing:(sw3#add) () in
  let _ = tv3#set_wrap_mode `WORD in
  let _ = tv3#misc#modify_font !lower_view_general_font in
  let _ = tv3#set_editable false in
  let _ = GtkBase.Widget.add_events tv2#as_widget [`POINTER_MOTION] in
  let _ = tv2#event#connect#motion_notify
	    ~callback:(fun e -> 
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
			 let tags = it#get_tags in
			 List.iter 
			   ( fun t ->
			       ignore (GtkText.Tag.event 
					 t#as_tag
					 tv2#as_widget
					 e 
					 it#as_textiter))
			   tags;
			 false)
  in
  b#place_cursor ~where:(b#get_start_iter);
	    (*  let _ =  refresh_m#connect#activate 
		~callback:(fun () -> analyze_all tv1 tv2 tv3) 
		in
	    *)
	    w#add_accel_group accel_group;
    (* Remove default pango menu for textviews *)
    ignore (tv1#event#connect#button_press ~callback:
	      (fun ev -> GdkEvent.Button.button ev = 3));
    ignore (tv2#event#connect#button_press ~callback:
	      (fun ev -> GdkEvent.Button.button ev = 3));
    ignore (tv3#event#connect#button_press ~callback:
	      (fun ev -> GdkEvent.Button.button ev = 3));
    tv1#misc#grab_focus ();
    tv2#misc#set_can_focus false;
    tv3#misc#set_can_focus false;
    ignore (tv1#get_buffer#create_mark 
	      ~name:"start_of_input" 
	      tv1#get_buffer#get_start_iter);
    ignore (tv2#get_buffer#create_mark 
	      ~name:"end_of_conclusion" 
	      tv2#get_buffer#get_start_iter);
    ignore (tv1#get_buffer#create_tag 
	      ~name:"to_process" 
	      ~properties:[`BACKGROUND "light green" ;`EDITABLE false] ());
    ignore (tv1#get_buffer#create_tag 
	      ~name:"processed" 
	      ~properties:[`BACKGROUND "green" ;`EDITABLE false] ());
    ignore (tv1#get_buffer#create_tag 
	      ~name:"error" 
	      ~properties:[`UNDERLINE `DOUBLE ; `FOREGROUND "red"] ());
    ignore (tv1#get_buffer#create_tag 
	      ~name:"kwd" 
	      ~properties:[`FOREGROUND "blue"] ());
    ignore (tv1#get_buffer#create_tag 
	      ~name:"decl" 
	      ~properties:[`FOREGROUND "orange red"] ());
    ignore (tv1#get_buffer#create_tag 
	      ~name:"comment" 
	      ~properties:[`FOREGROUND "brown"] ());
    ignore (tv1#get_buffer#create_tag 
	      ~name:"reserved" 
	      ~properties:[`FOREGROUND "dark red"] ());
    ignore (tv3#get_buffer#create_tag 
	      ~name:"error" 
	      ~properties:[`FOREGROUND "red"] ());
    w#show ();
    analyze_all tv1 tv2 tv3

let start () = 
  cant_break ();
  Coq.init ();
  ignore (GtkMain.Main.init ());
  Glib.Message.set_log_handler ~domain:"Gtk" ~levels:[`ERROR;`FLAG_FATAL;
						      `WARNING;`CRITICAL]
    (fun ~level msg ->
         failwith ("Coqide internal error: " ^ msg)
    );
  main ();
  Sys.catch_break true;
    try 
      GMain.Main.main ()
    with 
    Sys.Break -> prerr_endline "Interrupted." ; ()
