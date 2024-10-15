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

module Compat = struct

  (* stdlib version needs ocaml >= 4.13 *)
  let str_fold_left f x a =
    let open String in
    let r = ref x in
    for i = 0 to length a - 1 do
      r := f !r (unsafe_get a i)
    done;
    !r

  (* stdlib version needs ocaml >= 4.13 *)
  let str_for_all p s =
    let open String in
    let n = length s in
    let rec loop i =
      if i = n then true
      else if p (unsafe_get s i) then loop (succ i)
      else false in
    loop 0

end
open Compat

let source_substring source start stop =
  (* substring from start to stop inclusive, both 1-based *)
  (* start=0 is the same as start=1 *)
  let start = if start = 0 then 1 else start in
  let len = stop - start + 1 (* +1 for inclusive *) in
  String.sub source (start-1) len

let count_newlines s = str_fold_left (fun n c -> if c = '\n' then n+1 else n) 0 s

let is_white_char = function ' '|'\n'|'\t' -> true | _ -> false

let rec join_loop ~dummy ~source ~last_end ~lines acc = function
  | [] ->
    let sourcelen = String.length source in
    let acc = if last_end + 1 <= sourcelen then
        let text = source_substring source (last_end+1) sourcelen in
        if str_for_all is_white_char text then acc
        else
          ({ chars = { start_char = last_end+1; stop_char = sourcelen; };
             line = lines+1; text}, dummy)
          :: acc
      else
        acc
    in
    List.rev acc
  | (loc,v) :: rest ->
    let acc, lines, last_end =
      if loc.start_char > last_end + 1 then
        let text = source_substring source (last_end + 1) (loc.start_char - 1) in
        (* if only spaces since last command, include them in the next command
           typically "Module Foo.\n  Cmd." *)
        if not (str_for_all is_white_char text) then
          let n = count_newlines text in
          let acc =
            ({ chars = { start_char = last_end + 1; stop_char = loc.start_char - 1; };
               line = lines; text }, dummy)
            :: acc
          in
          acc, (lines+n), loc.start_char - 1
        else acc, lines, last_end
      else acc, lines, last_end
    in
    let text = source_substring source (last_end+1) loc.stop_char in
    let lines, n = if text <> "" && text.[0] = '\n' then lines+1, 1 else lines, 0 in
    let n = count_newlines text - n in
    let acc =
      ({ chars = { start_char = last_end + 1; stop_char = loc.stop_char; };
         line = lines; text }, v)
      :: acc
    in
    join_loop ~dummy ~source ~last_end:loc.stop_char ~lines:(lines + n) acc rest

let join_to_source ~dummy ~source vals =
  join_loop ~dummy ~source ~last_end:(-1) ~lines:1 [] vals
