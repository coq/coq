(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* Parsing of vernacular. *)

open Pp
open Util
open Options
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
          let verbosely = (verbosely = "Verbose") in
          let _ = read_vernac_file verbosely (make_suffix fname ".v") in
          ()
            
      | Node(_,"VernacList",l) ->
	  List.iter interp l

      | Node(_,"Time",[v]) ->
	  let tstart = System.get_time() in
          interp v;
	  let tend = System.get_time() in
          msgnl (str"Finished transaction in " ++
                   System.fmt_time_difference tstart tend)
	    
      | _ -> if not !just_parsing then interpfun com
  in 
  try
    interp com
  with e -> 
    raise (DuringCommandInterp (Ast.loc com, e))

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
 * parses and executes one command of the vernacular char stream.
 * Marks the end of the command in the lib_stk to make vernac undoing
 * easier. *)

let raw_do_vernac po =
  vernac (States.with_heavy_rollback Vernacinterp.interp) (po,None);
  Lib.mark_end_of_command()

(* Load a vernac file. Errors are annotated with file and location *)
let load_vernac verb file =
  try 
    let _ = read_vernac_file verb file in ()
  with e -> 
    raise_with_file file e

(* Compile a vernac file (f is assumed without .v suffix) *)
let compile verbosely f =
  try
    let s = Filename.basename f in
    let m = Names.id_of_string s in
    let _,longf = find_file_in_path (Library.get_load_path ()) (f^".v") in
    let ldir0 = Library.find_logical_path (Filename.dirname longf) in
    let ldir = Libnames.extend_dirpath ldir0 m in
    Termops.set_module ldir; (* Just for universe naming *)
    Lib.start_module ldir;
    if !dump then dump_string ("F" ^ Names.string_of_dirpath ldir ^ "\n");
    let _ = load_vernac verbosely longf in
    let mid = Lib.end_module m in
    assert (mid = ldir);
    Library.save_module_to ldir (longf^"o")
  with e ->
    raise_with_file f e
