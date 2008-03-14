open Util;;
open System;;
open Pp;;
open Libnames;;
open Library;;
open Ascent;;
open Vtp;;
open Xlate;;
open Line_parser;;
open Pcoq;;
open Vernacexpr;;
open Mltop;;

type parsed_tree =
  | P_cl of ct_COMMAND_LIST
  | P_c of ct_COMMAND
  | P_t of ct_TACTIC_COM
  | P_f of ct_FORMULA
  | P_id of ct_ID
  | P_s of ct_STRING
  | P_i of ct_INT;;

let print_parse_results n msg =
  Pp.msg
  ( str "message\nparsed\n" ++
    int n ++
    str "\n" ++
    (match msg with
     | P_cl x -> fCOMMAND_LIST x
     | P_c x -> fCOMMAND x
     | P_t x -> fTACTIC_COM x
     | P_f x -> fFORMULA x
     | P_id x -> fID x
     | P_s x -> fSTRING x
     | P_i x -> fINT x) ++
    str "e\nblabla\n");
  flush stdout;;

let ctf_SyntaxErrorMessage reqid pps =
 fnl () ++ str "message" ++ fnl () ++ str "syntax_error" ++ fnl () ++
   int reqid ++ fnl () ++
   pps ++ fnl () ++ str "E-n-d---M-e-s-s-a-g-e" ++ fnl ();;
let ctf_SyntaxWarningMessage reqid pps =
  fnl () ++  str "message" ++ fnl () ++ str "syntax_warning" ++ fnl () ++
  int reqid ++ fnl () ++ pps ++ fnl () ++ str "E-n-d---M-e-s-s-a-g-e" ++ fnl();;

let ctf_FileErrorMessage reqid pps =
  fnl () ++ str "message" ++ fnl () ++ str "file_error" ++ fnl () ++
  int reqid ++ fnl () ++ pps ++ fnl () ++ str "E-n-d---M-e-s-s-a-g-e" ++
  fnl ();;

let execute_when_necessary v =
 (match v with
  | VernacOpenCloseScope sc -> Vernacentries.interp v
  | VernacRequire (_,_,l) ->
      (try 
	Vernacentries.interp v
       with _ ->
	 let l=prlist_with_sep spc pr_reference l in
	 msgnl (str "Reinterning of " ++ l ++ str " failed"))
  | VernacRequireFrom (_,_,f) ->
      (try 
	Vernacentries.interp v
       with _ ->
	 msgnl (str "Reinterning of " ++ Util.pr_str f ++ str " failed"))
  | _ -> ()); v;;

let parse_to_dot =
  let rec dot st = match Stream.next st with
    | ("", ".") -> ()
    | ("EOI", "") -> raise End_of_file
    | _ -> dot st in
    Gram.Entry.of_parser "Coqtoplevel.dot" dot;;

let rec discard_to_dot stream =
  try Gram.Entry.parse parse_to_dot (Gram.parsable stream) with
  | Stdpp.Exc_located(_, Token.Error _) -> discard_to_dot stream;;

let rec decompose_string_aux s n =
    try let index = String.index_from s n '\n' in
            (String.sub s n (index - n))::
            (decompose_string_aux s (index + 1))
    with Not_found -> [String.sub s n ((String.length s) - n)];;

let decompose_string s n =
  match decompose_string_aux s n with
      ""::tl -> tl
    | a -> a;;

let make_string_list file_chan fst_pos snd_pos =
    let len = (snd_pos - fst_pos) in
    let s = String.create len in
    begin
      seek_in file_chan fst_pos;
      really_input file_chan s 0 len;
      decompose_string s 0;
    end;;

let rec get_sub_aux string_list snd_pos =
    match string_list with
      [] -> []
    | s::l ->
      let len = String.length s in
        if len >= snd_pos then
          if snd_pos < 0 then
            []
          else
            [String.sub s 0 snd_pos]
        else
          s::(get_sub_aux l (snd_pos - len - 1));;

let rec get_substring_list string_list fst_pos snd_pos =
  match string_list with
    [] -> []
  | s::l -> 
    let len = String.length s in
    if fst_pos > len then
       get_substring_list l (fst_pos - len - 1) (snd_pos - len - 1)
    else
       (* take into account the fact that carriage returns are not in the *)
       (* strings. *)
       let fst_pos2 = if fst_pos = 0 then 1 else fst_pos in
       if snd_pos > len then
         String.sub s (fst_pos2 - 1) (len + 1 - fst_pos2)::
         (get_sub_aux l (snd_pos - len - 2))
       else
         let gap = (snd_pos - fst_pos2) in
         if gap < 0 then
            []
         else
            [String.sub s (fst_pos2 - 1) gap];;

(* When parsing a list of commands, we try to recover error messages for
   each individual command. *)

type parse_result =
  | ParseOK of Vernacexpr.vernac_expr located option
  | ParseError of string * string list

let embed_string s =
  CT_coerce_STRING_OPT_to_VARG (CT_coerce_STRING_to_STRING_OPT (CT_string s))

let make_parse_error_item s l =
  CT_user_vernac (CT_ident s, CT_varg_list (List.map embed_string l))

let parse_command_list reqid stream string_list =
    let rec parse_whole_stream () =
    let this_pos = Stream.count stream in
    let first_ast = 
        try ParseOK (Gram.Entry.parse Pcoq.main_entry (Gram.parsable stream))
        with
        | (Stdpp.Exc_located(l, Stream.Error txt)) as e -> 
          begin
             msgnl (ctf_SyntaxWarningMessage reqid (Cerrors.explain_exn e));
             try
                discard_to_dot stream;
                msgnl (str "debug" ++ fnl () ++ int this_pos ++ fnl () ++
		       int (Stream.count stream));
		ParseError ("PARSING_ERROR",
                  get_substring_list string_list this_pos
		    (Stream.count stream))
             with End_of_file -> ParseOK None
           end
        | e-> 
          begin
            discard_to_dot stream;
	    ParseError ("PARSING_ERROR2",
	      get_substring_list string_list this_pos (Stream.count stream))
          end in
    match first_ast with
    | ParseOK (Some (loc,ast)) ->
        let _ast0 = (execute_when_necessary ast) in
          (try xlate_vernac ast
	  with e ->
	    make_parse_error_item "PARSING_ERROR2" 
		     (get_substring_list string_list this_pos
		       (Stream.count stream)))::parse_whole_stream()
    | ParseOK None -> []
    | ParseError (s,l) -> 
	(make_parse_error_item s l)::parse_whole_stream()
 in
    match parse_whole_stream () with
    | first_one::tail -> (P_cl (CT_command_list(first_one, tail)))
    | [] -> raise (UserError ("parse_string", (str "empty text.")));;

(*When parsing a string using a phylum, the string is first transformed
  into a Coq Ast using the regular Coq parser, then it is transformed into
  the right ascent term using xlate functions, then it is transformed into
  a stream, using the right vtp function. There is a special case for commands,
  since some of these must be executed!*)
let parse_string_action reqid phylum char_stream string_list =
 try let msg =
      match phylum with
      | "COMMAND_LIST" ->
        parse_command_list reqid char_stream string_list
      | "COMMAND" ->
       P_c
        (xlate_vernac
        (execute_when_necessary
        (Gram.Entry.parse Pcoq.Vernac_.vernac_eoi (Gram.parsable char_stream))))
      | "TACTIC_COM" ->
       P_t
        (xlate_tactic (Gram.Entry.parse Pcoq.Tactic.tactic_eoi 
                         (Gram.parsable char_stream)))
      | "FORMULA" ->
       P_f
        (xlate_formula
	   (Gram.Entry.parse 
              (Pcoq.eoi_entry Pcoq.Constr.lconstr) (Gram.parsable char_stream)))
      | "ID" -> P_id (CT_ident
                        (Libnames.string_of_qualid 
			 (snd 
			       (Gram.Entry.parse  (Pcoq.eoi_entry Pcoq.Prim.qualid)
						 (Gram.parsable char_stream)))))
      | "STRING" ->
	  P_s
         (CT_string (Gram.Entry.parse Pcoq.Prim.string 
                  (Gram.parsable char_stream)))
      | "INT" ->
	  P_i (CT_int (Gram.Entry.parse Pcoq.Prim.natural
                              (Gram.parsable char_stream)))
      | _ -> error "parse_string_action : bad phylum" in
      print_parse_results reqid msg
 with
 | Stdpp.Exc_located(l,Match_failure(_,_,_)) ->
    flush_until_end_of_stream char_stream;
    msgnl (ctf_SyntaxErrorMessage reqid
              (Cerrors.explain_exn 
                 (Stdpp.Exc_located(l,Stream.Error "match failure"))))
 | e ->
    flush_until_end_of_stream char_stream;
    msgnl (ctf_SyntaxErrorMessage reqid (Cerrors.explain_exn e));;


let quiet_parse_string_action char_stream =
 try let _ = 
         Gram.Entry.parse Pcoq.Vernac_.vernac_eoi (Gram.parsable char_stream) in
     ()
 with
 | _ -> flush_until_end_of_stream char_stream; ();;


let parse_file_action reqid file_name =
 try let file_chan = open_in file_name in
     (* file_chan_err, stream_err are the channel and stream  used to 
        get the text when a syntax error occurs *)
     let file_chan_err = open_in file_name in 
     let stream = Stream.of_channel file_chan in
     let _stream_err = Stream.of_channel file_chan_err in
     let rec discard_to_dot () =
       try Gram.Entry.parse parse_to_dot (Gram.parsable stream)
       with Stdpp.Exc_located(_,Token.Error _) -> discard_to_dot() in
       match let rec parse_whole_file () =
	 let this_pos = Stream.count stream in
           match 
             try
	       ParseOK(Gram.Entry.parse Pcoq.main_entry (Gram.parsable stream))
             with
               | Stdpp.Exc_located(l,Stream.Error txt) -> 
                   msgnl (ctf_SyntaxWarningMessage reqid
			    (str "Error with file" ++ spc () ++
			     str file_name ++ fnl () ++
			     Cerrors.explain_exn 
				 (Stdpp.Exc_located(l,Stream.Error txt))));
		   (try 
		      begin
                      	discard_to_dot ();
                    	ParseError ("PARSING_ERROR",
				   (make_string_list file_chan_err this_pos 
			       	      (Stream.count stream)))
		      end
                    with End_of_file -> ParseOK None)
               | e ->
                   begin
                     Gram.Entry.parse parse_to_dot (Gram.parsable stream);
                     ParseError ("PARSING_ERROR2",
			       (make_string_list file_chan this_pos
				  (Stream.count stream)))
                   end
		   
             with
               | ParseOK (Some (_,ast)) ->
		   let _ast0=(execute_when_necessary ast) in 
		   let term =
                     (try xlate_vernac ast
		      with e ->
                    	print_string ("translation error between " ^
				      (string_of_int this_pos) ^
				      " " ^
				      (string_of_int (Stream.count stream)) ^
				      "\n");
			make_parse_error_item "PARSING_ERROR2"
			  (make_string_list file_chan_err this_pos
			    (Stream.count stream))) in 
		     term::parse_whole_file ()
               | ParseOK None -> []
	       | ParseError (s,l) -> 
		   (make_parse_error_item s l)::parse_whole_file () in
         parse_whole_file () with
	   | first_one :: tail ->
	       print_parse_results reqid
		 (P_cl (CT_command_list (first_one, tail)))
	   | [] -> raise (UserError ("parse_file_action", str "empty file."))
       with
	 | Stdpp.Exc_located(l,Match_failure(_,_,_)) ->
	     msgnl
	       (ctf_SyntaxErrorMessage reqid
		  (str "Error with file" ++ spc () ++ str file_name ++ 
		   fnl () ++
		     Cerrors.explain_exn
		       (Stdpp.Exc_located(l,Stream.Error "match failure"))))
	 | e ->
	     msgnl
	       (ctf_SyntaxErrorMessage reqid
		  (str "Error with file" ++ spc () ++ str file_name ++
		   fnl () ++ Cerrors.explain_exn e));;

let add_rec_path_action reqid string_arg ident_arg =
  let directory_name = expand_path_macros string_arg in
    begin
      add_rec_path directory_name (Libnames.dirpath_of_string ident_arg)
    end;;
	

let add_path_action reqid string_arg =
  let directory_name = expand_path_macros string_arg in
    begin
      add_path directory_name Names.empty_dirpath
    end;;

let print_version_action () =
  msgnl (mt ());
  msgnl (str "$Id$");;

let load_syntax_action reqid module_name =
 msg (str "loading " ++ str module_name ++ str "... ");
 try
      (let qid = Libnames.make_short_qualid (Names.id_of_string module_name) in
      require_library [dummy_loc,qid] None;
      msg (str "opening... ");
      Declaremods.import_module false (Nametab.locate_module qid); 
      msgnl (str "done" ++ fnl ());
      ())
 with
 | UserError (label, pp_stream) ->
 (*This one may be necessary to make sure that the message won't be indented *)
 msgnl (mt ());
 msgnl
  (fnl () ++ str "error while loading syntax module " ++ str module_name ++
   str ": " ++ str label ++ fnl () ++ pp_stream)
 | e ->
  msgnl (mt ());
  msgnl
   (fnl () ++ str "message" ++ fnl () ++ str "load_error" ++ fnl () ++
    int reqid ++ fnl ());
  ();;

let coqparser_loop inchan =
 (parser_loop : (unit -> unit) *
                (int -> string -> char Stream.t -> string list -> unit) *
                (char Stream.t -> unit) * (int -> string -> unit) *
                (int -> string -> unit) * (int -> string -> string -> unit) *
                (int -> string -> unit) -> in_channel -> unit)
 (print_version_action, parse_string_action, quiet_parse_string_action, parse_file_action,
 add_path_action, add_rec_path_action, load_syntax_action) inchan;;

if !Sys.interactive then ()
 else 
Libobject.relax true;
(let coqdir = 
   try Sys.getenv "COQDIR"
   with Not_found -> 
     let coqdir = Coq_config.coqlib in
       if Sys.file_exists coqdir then
	 coqdir
       else
	 (msgnl (str "could not find the value of COQDIR"); exit 1) in
     begin
       add_rec_path (Filename.concat coqdir "theories")
	 (Names.make_dirpath [Nameops.coq_root]);
       add_rec_path (Filename.concat coqdir "contrib")
	 (Names.make_dirpath [Nameops.coq_root])
     end;
(let vernacrc =
   try
     Sys.getenv "VERNACRC"
   with
       Not_found -> 
	 List.fold_left 
	   (fun s1 s2 -> (Filename.concat s1 s2))
	   coqdir [ "contrib"; "interface"; "vernacrc"] in
   try
     (Gramext.warning_verbose := false;
      coqparser_loop (open_in vernacrc))
   with
     | End_of_file -> ()
     | e ->
	 (msgnl (Cerrors.explain_exn e);
	  msgnl (str "could not load the VERNACRC file"));
	 try
	   msgnl (str vernacrc)
	 with
	     e -> ());
(try let user_vernacrc =
   try Some(Sys.getenv "USERVERNACRC")
   with
     | Not_found ->
	 msgnl (str "no .vernacrc file"); None in
   (match user_vernacrc with
      	Some f -> coqparser_loop (open_in f)
      | None -> ())
 with
   | End_of_file -> ()
   | e ->
       msgnl (Cerrors.explain_exn e);
       msgnl (str "error in your .vernacrc file"));
msgnl (str "Starting Centaur Specialized Parser Loop");
try
  coqparser_loop stdin
with 
  | End_of_file -> ()
  | e -> msgnl(Cerrors.explain_exn e))
