(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Line_oriented_parser
open Vernac
open Vernacexpr

(* The toplevel parsing loop we propose here is more robust to printing
   errors.  The philosophy is that all commands should be individually wrapped
   in predefined markers.  If there is a parsing error, everything down to
   the closing marker will be discarded.  Also there is always an aknowledge
   message associated to a wrapped command. *)


(* It is also possible to have break signals sent by other programs.  However,
   there are some operations that should not be interrupted, especially, those
   operations that are outputing data.
*)

let break_happened = ref false

(* Before outputing any data, output_results makes sure that no interrupt
   is going to disturb the process. *)
let output_results_nl stream =
    let _ = Sys.signal Sys.sigint
       (Sys.Signal_handle(fun i -> break_happened := true;()))
  in
  msgnl stream

let rearm_break () =
  let _ = Sys.signal Sys.sigint (Sys.Signal_handle(fun _ -> raise Sys.Break)) in
    ()

let check_break () =
  if !break_happened then begin
    break_happened := false;
    raise Sys.Break
  end

(* All commands are acknowledged. *)

let global_request_id = ref 013

let acknowledge_command_ref =
   ref(fun request_id command_count opt_exn
      -> (fnl () ++ str "acknowledge command number " ++
           int request_id ++ fnl () ++
         str "successfully executed " ++ int command_count ++ fnl () ++
           str "error message" ++ fnl () ++
         (match opt_exn with
           Some e -> Cerrors.explain_exn e
         | None -> (mt ())) ++ fnl () ++
         str "E-n-d---M-e-s-s-a-g-e" ++ fnl ()))

let set_acknowledge_command f =
  acknowledge_command_ref := f

let acknowledge_command request_id = !acknowledge_command_ref request_id

(* The markers are chosen to be likely to be different from any existing text. *)

let start_marker = ref "protected_loop_start_command"
let end_marker = ref "protected_loop_end_command"
let start_length = ref (String.length !start_marker)
let start_marker_buffer = ref (String.make !start_length ' ')

let set_start_marker s =
  start_marker := s;
  start_length := String.length s;
  start_marker_buffer := String.make !start_length ' '

let set_end_marker s =
  end_marker := s

exception E_with_rank of int * exn

let rec parse_one_command_group input_channel =
  let count = ref 0 in
  let this_line = input_line input_channel in
  if (String.length this_line) >= !start_length then begin
    String.blit this_line 0 !start_marker_buffer 0 !start_length;
    if !start_marker_buffer = !start_marker then
      let req_id_line = input_line input_channel in
      	begin
	  (try
            global_request_id := int_of_string req_id_line
	  with
            | e -> failwith ("could not parse the request identifier |"^
                             req_id_line ^ "|")) ;
	  let count_line = input_line input_channel in
	    begin
	      (try
		count := int_of_string count_line
	      with
		| e -> failwith("could not parse the count|" ^ count_line
				^ "|"));
	      let stream_tail =
	      	Stream.from
		  (line_oriented_channel_to_option
		     !end_marker input_channel) in
	      	begin
		  check_break();
		  rearm_break();
		  let rec execute_n_commands rank =
		    if rank = !count then
		      None
		    else
		      let first_cmd_status =
                      	try
			  raw_do_vernac
			    (Pcoq.Gram.parsable stream_tail);
		      	None
		      	with e -> Some(rank,e) in
		      	match first_cmd_status with
			    None ->
			      execute_n_commands (rank + 1)
			  | v -> v in
		  let r = execute_n_commands 0 in
		    (match r with
			 None ->
			   output_results_nl
			     (acknowledge_command
			      	!global_request_id !count None)
		       | Some(rank, e) ->
			   (match e with
                    	     | DuringCommandInterp(a,e1)
			     | Stdpp.Exc_located (a,DuringSyntaxChecking e1) ->
				  output_results_nl
				    (acknowledge_command
				       !global_request_id rank (Some e1))
			      | e ->
				  output_results_nl
				    (acknowledge_command
				       !global_request_id rank (Some e))));
		    rearm_break();
		    flush_until_end_of_stream stream_tail
	      	end
	    end
	end
    else
      parse_one_command_group input_channel
  end else
    parse_one_command_group input_channel

let protected_loop input_chan =
  let rec explain_and_restart e =
    begin
      output_results_nl(Cerrors.explain_exn e);
      rearm_break();
      looprec input_chan;
    end
  and looprec input_chan =
    try
      while true do parse_one_command_group input_chan done
    with
      | Vernacexpr.Drop -> raise Vernacexpr.Drop
      | Vernacexpr.Quit -> exit 0
      | End_of_file -> exit 0
      | DuringCommandInterp(loc, Vernacexpr.Quit) -> raise Vernacexpr.Quit
      | DuringCommandInterp(loc, Vernacexpr.Drop) -> raise Vernacexpr.Drop
      | DuringCommandInterp(loc, e)
      | Stdpp.Exc_located (loc,DuringSyntaxChecking e) ->
	  explain_and_restart e
      | e -> explain_and_restart e in
    begin
      msgnl (str "Starting Centaur Specialized loop");
      looprec input_chan
    end
