
(* $Id$ *)

(* Parsing of vernacular. *)

open Pp
open Util
open System
open Coqast
open Vernacinterp

(* The functions in this module may raise (unexplainable!) exceptions.
   Use the module Coqtoplevel, which catches these exceptions
   (the exceptions are explained only at the toplevel). *)

exception DuringCommandInterp of Coqast.loc * exn

(* Like Exc_located, but specifies the outermost file read, the filename
   associated to the location of the error, and the error itself. *)

exception Error_in_file of string * (string * Coqast.loc) * exn

(* Specifies which file is read. The intermediate file names are
   discarded here. The Drop exception becomes an error. We forget
   if the error ocurred during interpretation or not *)

let raise_with_file file exc =
  let (cmdloc,re) =
    match exc with
      | DuringCommandInterp(loc,e) -> (loc,e)
      | e -> (Ast.dummy_loc,e) 
  in
  let (inner,inex) =
    match re with
      | Error_in_file (_, (f,loc), e) when loc <> Ast.dummy_loc ->
          ((f, loc), e)
      | Stdpp.Exc_located (loc, e) when loc <> Ast.dummy_loc ->
          ((file, loc), e)
      | _ -> ((file,cmdloc), re)
  in 
  raise (Error_in_file (file, inner, disable_drop inex))

let real_error = function
  | Stdpp.Exc_located (_, e) -> e
  | Error_in_file (_, _, e) -> e
  | e -> e

(* Opening and closing a channel. Open it twice when verbose: the first
   channel is used to read the commands, and the second one to print them.
   Note: we could use only one thanks to seek_in, but seeking on and on in
   the file we parse seems a bit risky to me.  B.B.  *)

let open_file_twice_if verbosely fname =
  let _,longfname = find_file_in_path (Library.get_load_path ()) fname in
  let in_chan = open_in longfname in
  let verb_ch = if verbosely then Some (open_in longfname) else None in
  let po = Pcoq.Gram.parsable (Stream.of_channel in_chan) in
  (in_chan, longfname, (po, verb_ch))

let close_input in_chan (_,verb) =
  try 
    close_in in_chan;
    match verb with
      | Some verb_ch -> close_in verb_ch
      | _ -> ()
  with _ -> ()

let verbose_phrase verbch loc =
  match verbch with
    | Some ch ->
	let len = snd loc - fst loc in
	let s = String.create len in
        seek_in ch (fst loc);
        really_input ch s 0 len;
        message s;
        pp_flush()
    | _ -> ()

exception End_of_input
  
let parse_phrase (po, verbch) =
  match Pcoq.Gram.Entry.parse Pcoq.main_entry po with
    | Some com -> verbose_phrase verbch (Ast.loc com); com
    | None -> raise End_of_input

(* vernac parses the given stream, executes interpfun on the syntax tree it
 * parses, and is verbose on "primitives" commands if verbosely is true *)

let just_parsing = ref false

let rec vernac interpfun input =
  let com = parse_phrase input in
  let rec interp com =
    match com with
      | Node (_,"LoadFile",[Str(_, verbosely); Str(_,fname)]) ->
          let verbosely = verbosely = "Verbose" in
          raw_load_vernac_file verbosely (make_suffix fname ".v")
            
      | Node (_,"CompileFile",[Str(_,verbosely); Str(_,only_spec);
			       Str (_,mname); Str(_,fname)]) ->
          let verbosely = verbosely = "Verbose" in
          let only_spec = only_spec = "Specification" in
          States.with_heavy_rollback (* to roll back in case of error *)
            (raw_compile_module verbosely only_spec mname)
            (make_suffix fname ".v")
	    
      | Node(_,"VernacList",l) ->
	  List.iter interp l

      | Node(_,"Time",[v]) ->
	  let tstart = System.get_time() in
          interp v;
	  let tend = System.get_time() in
          mSGNL [< 'sTR"Finished transaction in " ;
                   System.fmt_time_difference tstart tend >]
	    
      | _ -> if not !just_parsing then interpfun com
  in 
  try
    interp com
  with e -> 
    raise (DuringCommandInterp (Ast.loc com, e))
    
and raw_load_vernac_file verbosely s =
  let _ = read_vernac_file verbosely s in ()

and raw_compile_module verbosely only_spec mname file =
  Library.import_module mname; (* ??? *)
  let lfname = read_vernac_file verbosely file in
  let base = Filename.chop_suffix lfname ".v" in
  Pfedit.check_no_pending_proofs ();
  if only_spec then
    failwith ".vi not yet implemented"
  else 
    Discharge.save_module_to mname base

and read_vernac_file verbosely s =
  let interpfun =
    if verbosely then 
      Vernacinterp.interp
    else 
      Options.silently Vernacinterp.interp 
  in
  let (in_chan, fname, input) = open_file_twice_if verbosely s in
  try
    (* we go out of the following infinite loop when a End_of_input is
     * raised, which means that we raised the end of the file being loaded *)
    while true do vernac interpfun input; pp_flush () done; fname
  with e ->   (* whatever the exception *)
    close_input in_chan input;    (* we must close the file first *)
    match real_error e with
      | End_of_input -> fname
      | _ -> raise_with_file fname e

(* raw_do_vernac : char Stream.t -> unit
 * parses and executes one command of the vernacular char stream *)

let raw_do_vernac po =
  vernac (States.with_heavy_rollback Vernacinterp.interp) (po,None)

(* Load a vernac file. Errors are annotated with file and location *)
let load_vernac verb file =
  try 
    raw_load_vernac_file verb file
  with e -> 
    raise_with_file file e
