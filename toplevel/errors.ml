
(* $Id$ *)

open Pp
open Util
open Ast
open Indtypes
open Type_errors
open Lexer

let print_loc loc =
  if loc = dummy_loc then 
    [< 'sTR"<unknown>" >]
  else 
    [< 'iNT (fst loc); 'sTR"-"; 'iNT (snd loc) >]

let guill s = "\""^s^"\""

let where s =
  if !Options.debug then  [< 'sTR"in "; 'sTR s; 'sTR":"; 'sPC >] else [<>]

(* assumption : explain_sys_exn does NOT end with a 'FNL anymore! *)

let rec explain_exn_default = function
  | Stream.Failure -> [< 'sTR"Error: uncaught Parse.Failure." >]
  | Stream.Error txt -> hOV 0 [< 'sTR"Syntax error: "; 'sTR txt >]
  | Token.Error txt -> hOV 0 [< 'sTR"Lexer error: "; 'sTR txt >]
  | Sys_error msg -> hOV 0 [< 'sTR"OS error: " ; 'sTR msg >]
  | UserError(s,pps) -> hOV 1 [< 'sTR"Error: "; where s; pps >]
	
  | Out_of_memory -> [< 'sTR"Out of memory" >]
  | Stack_overflow -> [< 'sTR"Stack overflow" >]
	  
  | Ast.No_match s -> hOV 0 [< 'sTR"Ast matching error : "; 'sTR s >]
	
  | Anomaly (s,pps) -> hOV 1 [< 'sTR"System Anomaly: "; where s; pps >]
	  
  | Match_failure(filename,pos1,pos2) ->
      hOV 1 [< 'sTR"Match failure in file " ;
	       'sTR filename ; 'sTR " from char #" ;
	       'iNT pos1 ; 'sTR " to #" ; 'iNT pos2 >]

  | Not_found -> [< 'sTR"Search error." >]

  | Failure s -> hOV 0 [< 'sTR "System Error (Failure): " ; 'sTR (guill s) >]

  | Invalid_argument s -> hOV 0 [< 'sTR"Invalid argument: " ; 'sTR (guill s) >]

  | Sys.Break -> hOV 0 [< 'fNL; 'sTR"User Interrupt." >]

  | TypeError(k,ctx,te) -> hOV 0 (Himsg.explain_type_error k ctx te)

  | InductiveError e -> hOV 0 (Himsg.explain_inductive_error e)

  | Logic.RefinerError e -> hOV 0 (Himsg.explain_refiner_error e)

  | Stdpp.Exc_located (loc,exc) ->
      hOV 0 [< if loc = Ast.dummy_loc then [<>]
               else [< 'sTR"At location "; print_loc loc; 'sTR":"; 'fNL >];
               explain_exn_default exc >]

  | Lexer.Error Illegal_character -> [< 'sTR "Illegal character." >]
	
  | Lexer.Error Unterminated_comment -> [< 'sTR "Unterminated comment." >]
	
  | Lexer.Error Unterminated_string -> [< 'sTR "Unterminated string." >]
	
  | reraise ->
      flush_all();
      (try Printexc.print raise reraise with _ -> ());
      flush_all();
      [< 'sTR "Please report." >]

let raise_if_debug e =
  if !Options.debug then raise e

let explain_exn_function = ref explain_exn_default

let explain_exn e = !explain_exn_function e
