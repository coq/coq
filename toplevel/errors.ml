(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Ast
open Indtypes
open Type_errors
open Pretype_errors
open Lexer

let print_loc loc =
  if loc = dummy_loc then 
    [< 'sTR"<unknown>" >]
  else 
    [< 'iNT (fst loc); 'sTR"-"; 'iNT (snd loc) >]

let guill s = "\""^s^"\""

let where s =
  if !Options.debug then  [< 'sTR"in "; 'sTR s; 'sTR":"; 'sPC >] else [<>]

let report () = [< 'sTR "."; 'sPC; 'sTR "Please report." >]

(* assumption : explain_sys_exn does NOT end with a 'FNL anymore! *)

let rec explain_exn_default = function
  | Stream.Failure -> 
      hOV 0 [< 'sTR "Anomaly: Uncaught Stream.Failure." >]
  | Stream.Error txt -> 
      hOV 0 [< 'sTR "Syntax error: "; 'sTR txt >]
  | Token.Error txt -> 
      hOV 0 [< 'sTR "Syntax error: "; 'sTR txt >]
  | Sys_error msg -> 
      hOV 0 [< 'sTR "Error: OS: "; 'sTR msg >]
  | UserError(s,pps) -> 
      hOV 1 [< 'sTR"Error: "; where s; pps >]
  | Out_of_memory -> 
      hOV 0 [< 'sTR "Out of memory" >]
  | Stack_overflow -> 
      hOV 0 [< 'sTR "Stack overflow" >]
  | Ast.No_match s -> 
      hOV 0 [< 'sTR "Anomaly: Ast matching error: "; 'sTR s; report () >]
  | Anomaly (s,pps) -> 
      hOV 1 [< 'sTR "Anomaly: "; where s; pps; report () >]
  | Match_failure(filename,pos1,pos2) ->
      hOV 1 [< 'sTR "Anomaly: Match failure in file ";
	       'sTR (guill filename); 'sTR " from char #";
	       'iNT pos1; 'sTR " to #"; 'iNT pos2;
	       report () >]
  | Not_found -> 
      hOV 0 [< 'sTR "Anomaly: Search error"; report () >]
  | Failure s -> 
      hOV 0 [< 'sTR "Anomaly: Failure "; 'sTR (guill s); report () >]
  | Invalid_argument s -> 
      hOV 0 [< 'sTR "Anomaly: Invalid argument "; 'sTR (guill s); report () >]
  | Sys.Break -> 
      hOV 0 [< 'fNL; 'sTR"User Interrupt." >]
  | Univ.UniverseInconsistency -> 
      hOV 0 [< 'sTR "Error: Universe Inconsistency." >]
  | TypeError(k,ctx,te) -> 
      hOV 0 [< 'sTR "Error:"; 'sPC; Himsg.explain_type_error k ctx te >]
  | PretypeError(ctx,te) ->
      hOV 0 [< 'sTR "Error:"; 'sPC; Himsg.explain_pretype_error ctx te >]
  | InductiveError e -> 
      hOV 0 [< 'sTR "Error:"; 'sPC; Himsg.explain_inductive_error e >]
  | Cases.PatternMatchingError (env,e) -> 
      hOV 0
	[< 'sTR "Error:"; 'sPC; Himsg.explain_pattern_matching_error env e >]
  | Logic.RefinerError e -> 
      hOV 0 [< 'sTR "Error:"; 'sPC; Himsg.explain_refiner_error e >]
  | Nametab.GlobalizationError q ->
      hOV 0 [< 'sTR "Error:"; 'sPC;
	       'sTR "The reference"; 'sPC; Nametab.pr_qualid q;
	       'sPC ; 'sTR "was not found"; 
	       'sPC ; 'sTR "in the current"; 'sPC ; 'sTR "environment" >]
  | Tacmach.FailError i ->
      hOV 0 [< 'sTR "Error: Fail tactic always fails (level "; 
	       'iNT i; 'sTR")." >]
  | Stdpp.Exc_located (loc,exc) ->
      hOV 0 [< if loc = Ast.dummy_loc then [<>]
               else [< 'sTR"At location "; print_loc loc; 'sTR":"; 'fNL >];
               explain_exn_default exc >]
  | Lexer.Error Illegal_character -> 
      hOV 0 [< 'sTR "Syntax error: Illegal character." >]
  | Lexer.Error Unterminated_comment -> 
      hOV 0 [< 'sTR "Syntax error: Unterminated comment." >]
  | Lexer.Error Unterminated_string -> 
      hOV 0 [< 'sTR "Syntax error: Unterminated string." >]
  | Lexer.Error Undefined_token -> 
      hOV 0 [< 'sTR "Syntax error: Undefined token." >]
  | Lexer.Error (Bad_token s) -> 
      hOV 0 [< 'sTR "Syntax error: Bad token"; 'sPC; 'sTR s; 'sTR "." >]
  | Assert_failure (s,b,e) ->
      hOV 0 [< 'sTR "Anomaly: assert failure"; 'sPC;
	       if s <> "" then 
		 [< 'sTR ("(file \"" ^ s ^ "\", characters "); 
		    'iNT b; 'sTR "-"; 'iNT e; 'sTR ")" >]
	       else
		 [< >];
	       report () >]
  | reraise ->
      hOV 0 [< 'sTR "Anomaly: Uncaught exception "; 
	       'sTR (Printexc.to_string reraise); report () >]

let raise_if_debug e =
  if !Options.debug then raise e

let explain_exn_function = ref explain_exn_default

let explain_exn e = !explain_exn_function e
