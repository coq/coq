(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open BenchUtil

let time_regex = Str.regexp {|^Chars \([0-9]+\) - \([0-9]+\) [^ ]+ \([0-9.]+\) secs|}

let rec parse_loop filech acc =
  match input_line filech with
  | exception End_of_file ->
    List.rev acc
  | l ->
    if not (Str.string_match time_regex l 0) then
      parse_loop filech acc
    else
      let b = int_of_string @@ Str.matched_group 1 l
      and e = int_of_string @@ Str.matched_group 2 l
      and t = Str.matched_group 3 l in
      let v = { start_char = b; stop_char = e; }, { str = t; q = Q.of_string t } in
      parse_loop filech (v :: acc)

let parse ~file =
  let ch = open_in file in
  let v = parse_loop ch [] in
  close_in ch;
  v
