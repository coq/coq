(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

let line_oriented_channel_to_option stop_string input_channel =
  let count = ref 0 in
  let buff = ref "" in
  let current_length = ref 0 in
  fun i -> 
    if (i - !count) >= !current_length then begin
      count := !count + !current_length + 1;
      buff := input_line input_channel;
      if !buff = stop_string then
        None
      else begin
        current_length := String.length !buff;
        Some '\n'
      end
    end else
      Some (String.get !buff (i - !count))

let flush_until_end_of_stream char_stream =
  Stream.iter (function _ -> ()) char_stream
