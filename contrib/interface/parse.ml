open Util;;

open System;;

open Pp;;

open Coqast;;

open Library;;

open Ascent;;

open Vtp;;

open Xlate;;

open Line_parser;;

open Pcoq;;

type parsed_tree =
  | P_cl of ct_COMMAND_LIST
  | P_c of ct_COMMAND
  | P_t of ct_TACTIC_COM
  | P_f of ct_FORMULA
  | P_id of ct_ID
  | P_s of ct_STRING
  | P_i of ct_INT;;

let print_parse_results n msg =
  print_string "message\nparsed\n";
  print_int n;
  print_string "\n";
  (match msg with
  | P_cl x -> fCOMMAND_LIST x
  | P_c x -> fCOMMAND x
  | P_t x -> fTACTIC_COM x
  | P_f x -> fFORMULA x
  | P_id x -> fID x
  | P_s x -> fSTRING x
  | P_i x -> fINT x);
  print_string "e\nblabla\n";
  flush stdout;;

let ctf_SyntaxErrorMessage reqid pps =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "syntax_error"; 'fNL; 'iNT reqid; 'fNL;
   pps; 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;
let ctf_SyntaxWarningMessage reqid pps =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "syntax_warning"; 'fNL; 'iNT reqid; 'fNL;
   pps; 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;

let ctf_FileErrorMessage reqid pps =
 [< 'fNL; 'sTR "message"; 'fNL; 'sTR "file_error"; 'fNL; 'iNT reqid; 'fNL;
   pps; 'fNL; 'sTR "E-n-d---M-e-s-s-a-g-e"; 'fNL >];;

(*In the code for CoqV6.2, the require_module call is encapsulated in
  a function "without_mes_ambig".  Here I have supposed that this
  function has no effect on parsing *)
let try_require_module import specif name fname =
 try Library.require_module (if specif = "UNSPECIFIED" then None
  else Some (specif = "SPECIFICATION")) name fname (import = "IMPORT")
 with
 | e -> mSGNL [< 'sTR "Reinterning of "; 'sTR name; 'sTR " failed" >];;

let execute_when_necessary ast =
 (match ast with
  | Node (_, "GRAMMAR", ((Nvar (_, s)) :: ((Node (_, "ASTLIST", al)) :: []))) ->
   Metasyntax.add_grammar_obj s al
  | Node (_, "TOKEN", ((Str (_, s)) :: [])) -> Metasyntax.add_token_obj s
  | Node (_, "Require",
            ((Str (_, import)) ::
              ((Str (_, specif)) :: ((Nvar (_, mname)) :: [])))) ->
   try_require_module import specif mname None
  | Node (_, "RequireFrom",
            ((Str (_, import)) ::
              ((Str (_, specif)) ::
                ((Nvar (_, mname)) :: ((Str (_, file_name)) :: []))))) ->
   try_require_module import specif mname (Some file_name)
  | _ -> ()); ast;;

let parse_to_dot =
  let rec dot = parser
      [< '("", ".") >] -> ()
    | [< '("EOI", "") >] -> raise End_of_file
    | [< '_; s >] -> dot s
  in Gram.Entry.of_parser "Coqtoplevel.dot" dot;;

let rec discard_to_dot stream =
  try Gram.Entry.parse parse_to_dot (Gram.parsable stream) with
  | Stdpp.Exc_located(_, Token.Error _) -> discard_to_dot stream;;

let rec decompose_string s n =
    try let index = String.index_from s n '\n' in
            (Ast.str (String.sub s n (index - n)))::
            (decompose_string s (index + 1))
    with Not_found -> [Ast.str(String.sub s n ((String.length s) - n))];;

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
let parse_command_list reqid stream string_list =
    let rec parse_whole_stream () =
    let this_pos = Stream.count stream in
    let first_ast = 
        try Gram.Entry.parse Pcoq.main_entry (Gram.parsable stream)
        with
        | (Stdpp.Exc_located(l, Stream.Error txt)) as e -> 
          begin
             mSGNL (ctf_SyntaxWarningMessage reqid (Errors.explain_exn e));
             try
                discard_to_dot stream;
                mSGNL [< 'sTR "debug"; 'fNL; 'iNT this_pos; 'fNL; 'iNT 
                  (Stream.count stream) >];
                Some( Node(l, "PARSING_ERROR",
                        List.map Ast.str
                        (get_substring_list string_list this_pos
                            (Stream.count stream))))
             with End_of_file -> None
           end
        | e-> 
          begin
            discard_to_dot stream;
            Some(Node((0,0), "PARSING_ERROR2",
                   List.map Ast.str
		   (get_substring_list string_list this_pos
                     (Stream.count stream))))
          end in
    match first_ast with
    | Some ast ->
        let ast0 = (execute_when_necessary ast) in
          xlate_vernac ast::parse_whole_stream()
    | None -> [] in
    match parse_whole_stream () with
    | first_one::tail -> (P_cl (CT_command_list(first_one, tail)))
    | [] -> raise (UserError ("parse_string", [< 'sTR "empty text." >]));;

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
        (Gram.Entry.parse Pcoq.Constr.constr_eoi (Gram.parsable char_stream)))
      | "ID" -> P_id (xlate_id 
                       (Gram.Entry.parse Pcoq.Prim.ident 
                              (Gram.parsable char_stream)))
      | "STRING" ->
	  P_s
         (xlate_string (Gram.Entry.parse Pcoq.Prim.string 
                  (Gram.parsable char_stream)))
      | "INT" ->
	  P_i (xlate_int (Gram.Entry.parse Pcoq.Prim.number
                              (Gram.parsable char_stream)))
      | _ -> error "parse_string_action : bad phylum" in
      print_parse_results reqid msg
 with
 | Stdpp.Exc_located(l,Match_failure(_,_,_)) ->
    flush_until_end_of_stream char_stream;
    mSGNL (ctf_SyntaxErrorMessage reqid
              (Errors.explain_exn 
                 (Stdpp.Exc_located(l,Stream.Error "match failure"))))
 | e ->
    flush_until_end_of_stream char_stream;
    mSGNL (ctf_SyntaxErrorMessage reqid (Errors.explain_exn e));;


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
     let stream_err = Stream.of_channel file_chan_err in
     match let rec parse_whole_file () =
            let this_pos = Stream.count stream in
            match 
              try
                let this_ast = 
                     Gram.Entry.parse Pcoq.main_entry (Gram.parsable stream) in
                this_ast
              with
            | Stdpp.Exc_located(l,Stream.Error txt ) -> 
                 mSGNL (ctf_SyntaxWarningMessage reqid
                [< 'sTR "Error with file"; 'sPC; 'sTR file_name; 'fNL;
                   Errors.explain_exn 
                      (Stdpp.Exc_located(l,Stream.Error txt)) >]);
                 let rec discard_to_dot () =
                 try Gram.Entry.parse parse_to_dot (Gram.parsable stream)
                 with Stdpp.Exc_located(_,Token.Error _) -> discard_to_dot()
                 in (try 
                     discard_to_dot ();
                        Some( Node(l, "PARSING_ERROR",
                       (make_string_list file_chan_err this_pos 
                       (Stream.count stream))))
                 with End_of_file -> None)
            | e ->
                  begin
                  Gram.Entry.parse parse_to_dot (Gram.parsable stream);
                  Some( Node((0,0), "PARSING_ERROR2",
                       (make_string_list file_chan this_pos 
                       (Stream.count stream))))
                  end

            with
            | Some ast -> let ast0=(execute_when_necessary ast) in 
                 xlate_vernac ast::parse_whole_file ()
            | None -> [] in
           parse_whole_file () with
      | first_one :: tail ->
       print_parse_results reqid
          (P_cl (CT_command_list (first_one, tail)))
      | [] -> raise (UserError ("parse_file_action", [< 'sTR "empty file." >]))
 with
 | Stdpp.Exc_located(l,Match_failure(_,_,_)) ->
 mSGNL
  (ctf_SyntaxErrorMessage reqid
  [< 'sTR "Error with file"; 'sPC; 'sTR file_name; 'fNL;
  Errors.explain_exn (Stdpp.Exc_located(l,Stream.Error "match failure")) >])
 | e ->
 mSGNL
  (ctf_SyntaxErrorMessage reqid
  [< 'sTR "Error with file"; 'sPC; 'sTR file_name; 'fNL;
  Errors.explain_exn e >]);;

(* This function is taken from Mltop.add_path *)

let add_path dir coq_dirpath =
  if coq_dirpath = [] then anomaly "add_path: empty path in library";
  if exists_dir dir then
    begin
      Library.add_load_path_entry
        { directory = dir; coq_dirpath = coq_dirpath };
      Nametab.push_library_root (List.hd coq_dirpath)
    end
  else
    wARNING [< 'sTR ("Cannot open " ^ dir) >]

let add_rec_path dir coq_dirpath =
  if coq_dirpath = [] then anomaly "add_path: empty path in library";
  let dirs = all_subdirs dir (Some coq_dirpath) in
  if dirs <> [] then
    begin
      List.iter Library.add_load_path_entry dirs;
      Nametab.push_library_root (List.hd coq_dirpath)
    end
    else
      wARNING [< 'sTR ("Cannot open " ^ dir) >];;

let add_path_action reqid string_arg =
  let directory_name = glob string_arg in
  let alias = Filename.basename directory_name in
    begin
      add_path directory_name [alias]
    end;;

let print_version_action () =
  mSGNL [< >];
  mSGNL [< 'sTR "$Id$" >];;

let load_syntax_action reqid module_name =
 mSG [< 'sTR "loading "; 'sTR module_name; 'sTR "... " >];
 try (load_module module_name None;
      mSG [< 'sTR "opening... ">];
      import_module module_name; 
      mSGNL [< 'sTR "done"; 'fNL >];
      ())
 with
 | UserError (label, pp_stream) ->
 (*This one may be necessary to make sure that the message won't be indented *)
 mSGNL [< >];
 mSGNL
  [< 'fNL; 'sTR "error while loading syntax module "; 'sTR module_name;
  'sTR ": "; 'sTR label; 'fNL; pp_stream >]
 | e ->
  mSGNL [< >];
  mSGNL
   [< 'fNL; 'sTR "message"; 'fNL; 'sTR "load_error"; 'fNL; 'iNT reqid; 'fNL >];
  ();;

let coqparser_loop inchan =
 (parser_loop : (unit -> unit) *
                (int -> string -> char Stream.t -> string list -> unit) *
                (char Stream.t -> unit) * (int -> string -> unit) *
                (int -> string -> unit) * (int -> string -> unit) ->
                in_channel -> unit)
 (print_version_action, parse_string_action, quiet_parse_string_action, parse_file_action,
 add_path_action, load_syntax_action) inchan;;

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
	 (mSGNL [< 'sTR "could not find the value of COQDIR" >]; exit 1) in
     begin
       add_rec_path (Filename.concat coqdir "theories") [Nametab.coq_root];
       add_path (Filename.concat coqdir "tactics") [Nametab.coq_root];
       add_rec_path (Filename.concat coqdir "contrib") [Nametab.coq_root];
       List.iter (fun {directory=a} -> mSGNL [< 'sTR a >]) (get_load_path())
     end;
(try 
  (match create_entry (get_univ "nat") "number" ETast with
     (Ast number) ->
      Gram.extend number None
	[None, None, 
	 [[Gramext.Stoken ("INT", "")],
	 Gramext.action 
	    (fun s loc ->
		 Node((0,0),"XTRA",[Str((0,0),"omega_integer_for_ctcoq");
				 Num((0,0),int_of_string s)]))]]
   | _ -> mSGNL [< 'sTR "unpredicted behavior of Grammar.extend" >])

 with
   e -> mSGNL [< 'sTR "could not add a parser for numbers" >]);
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
      Esyntax.warning_verbose := false;
      coqparser_loop (open_in vernacrc))
   with
     | End_of_file -> ()
     | e ->
	 (mSGNL (Errors.explain_exn e);
	  mSGNL [< 'sTR "could not load the VERNACRC file" >]);
	 try
	   mSGNL [< 'sTR vernacrc >]
	 with
	     e -> ());
(try let user_vernacrc =
   try Some(Sys.getenv "USERVERNACRC")
   with
     | Not_found as e ->
	 mSGNL [< 'sTR "no .vernacrc file" >]; None in
   (match user_vernacrc with
      	Some f -> coqparser_loop (open_in f)
      | None -> ())
 with
   | End_of_file -> ()
   | e ->
       mSGNL (Errors.explain_exn e);
       mSGNL [< 'sTR "error in your .vernacrc file" >]);
mSGNL [< 'sTR "Starting Centaur Specialized Parser Loop" >];
try
  coqparser_loop stdin
with 
  | End_of_file -> ()
  | e -> mSGNL(Errors.explain_exn e))
