
(* $Id$ *)

open Pp
open Line_oriented_parser
open Vernac

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

let output_results_nl stream =
  let _ = 
    Sys.signal Sys.sigint
      (Sys.Signal_handle (fun _ -> break_happened := true;()))
  in
  mSGNL stream

let rearm_break () =
  let _ = 
    Sys.signal Sys.sigint (Sys.Signal_handle(fun _ -> raise Sys.Break)) in
  ()

let check_break () =
  if !break_happened then begin
    break_happened := false;
    raise Sys.Break
  end

(* All commands are acknowledged. *)

let global_request_id = ref 013

let acknowledge_command request_id =
  [< 'fNL; 'sTR "message"; 'fNL; 'sTR "acknowledge"; 'fNL; 
     'iNT request_id; 'fNL; 'sTR "***"; 'fNL >]

(* The markers are chosen to be likely to be different from any
  existing text. *)

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

let rec parse_one_command input_channel =
  let this_line = input_line input_channel in
  if ((String.length this_line) >= !start_length) then begin
    String.blit this_line 0 !start_marker_buffer 0 !start_length;
    if !start_marker_buffer = !start_marker then
      let snd_line = input_line input_channel in
      begin 
	try
          global_request_id := int_of_string snd_line
	with
          | e -> failwith ("could not parse the request identifier |"^
                           snd_line ^ "|") 
      end;
      let stream_tail =
        Stream.from
          (line_oriented_channel_to_option !end_marker input_channel) in
      begin
	try
	  check_break();
          rearm_break();
          raw_do_vernac (Pcoq.Gram.parsable stream_tail);
          output_results_nl(acknowledge_command !global_request_id);
          rearm_break();
        with
          | e -> begin flush_until_end_of_stream stream_tail; raise e end
      end;
      flush_until_end_of_stream stream_tail
    else
      parse_one_command input_channel
  end else
    parse_one_command input_channel

let protected_loop input_chan =
  let rec explain_and_restart e =
    output_results_nl(Errors.explain_exn e);
    rearm_break();
    looprec input_chan;
  and looprec input_chan =
    try 
      while true do parse_one_command input_chan done
    with
      | Vernacinterp.Drop -> raise Vernacinterp.Drop
      | Vernacinterp.Quit -> exit 0
      | End_of_file -> exit 0
      | DuringCommandInterp(loc, Vernacinterp.Quit) -> raise Vernacinterp.Quit
      | DuringCommandInterp(loc, Vernacinterp.Drop) -> raise Vernacinterp.Drop
      | DuringCommandInterp(loc, e) ->
	  explain_and_restart e
      | e -> explain_and_restart e 
  in
  mSGNL [<'sTR "Starting Centaur Specialized loop" >];
  looprec input_chan
