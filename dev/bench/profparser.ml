(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr fmt

module YB = Yojson.Basic

let assoc a b : YB.t = CList.assoc_f String.equal a b

(* Profile files can be large, we want to parse 1 record at a time and
   only keep the info we're interested in (ie the "command" events).

   The yojson API isn't great for this so we rely on there being 1
   value / line starting at line 2.
*)

let rec find_cmds ~fname ~lnum acc ch =
  let l = input_line ch in
  let is_last = l.[String.length l - 1] <> ',' in
  (* yojson doesn't like the trailing comma so remove it *)
  let l = if is_last then l else String.sub l 0 (String.length l - 1) in
  let v = YB.from_string ~fname ~lnum l in
  let acc = match v with
    | `Assoc l -> begin match assoc "name" l with
        | `String "command" -> (lnum,l) :: acc
        | _ -> acc
      end
    | _ -> die "File %S line %d: unrecognised value\n" fname lnum
  in
  if is_last then acc else find_cmds ~fname ~lnum:(lnum + 1) acc ch

let read_file fname =
  let ch = open_in fname in
  try
    (* ignore initial line *)
    let _ = input_line ch in
    let cmds = find_cmds ~fname ~lnum:2 [] ch in
    close_in ch;
    cmds
  with e -> close_in ch; raise e

open BenchUtil

let force_string lnum = function
  | `String s -> s
  | _ -> die "line %d: malformed value (expected string)\n" lnum

let get_ts (lnum, l) = match assoc "ts" l with
  | `Int ts -> ts
  | _ -> die "line %d: malformed ts\n" lnum

let get_src_info (lnum, l) = match assoc "args" l with
  | `Assoc l ->
    let hdr = force_string lnum (assoc "cmd" l) in
    let line = match assoc "line" l with
      | `Int l -> l
      | `String l -> int_of_string l
      | _ -> die "line %d: malformed line number\n" lnum
    in
    hdr, line
  | _ -> die "line %d: malformed args\n" lnum

let hdr_regex = Str.regexp {|^Chars \([0-9]+\) - \([0-9]+\) |}

let get_src_chars ~lnum hdr =
  if not (Str.string_match hdr_regex hdr 0) then die "line %d: malformed command header" lnum
  else
    { start_char = int_of_string @@ Str.matched_group 1 hdr;
      stop_char = int_of_string @@ Str.matched_group 2 hdr; }

let mk_measure start stop =
  let time = stop - start in
  (* time unit is microsecond *)
  let timeq = Q.(div (of_int time) (of_int 1000000)) in
  let timef = (float_of_int time) /. 1e6 in
  let str =
    (* 3 significant digits *)
    if timef > 100. then Printf.sprintf "%.0f" timef
    else if timef > 10. then Printf.sprintf "%.1f" timef
    else if timef > 1. then Printf.sprintf "%.2f" timef
    else if timef > 0.1 then Printf.sprintf "%.3f" timef
    else if timef > 0.01 then Printf.sprintf "%.4f" timef
    else if timef > 0.001 then Printf.sprintf "%.5f" timef
    else Printf.sprintf "%.6f" timef
  in
  { str;
    q = timeq; }

let rec process_cmds acc = function
  | [] -> acc
  | end_event :: start_event :: rest ->
    let hdr, line = get_src_info start_event in
    let start_ts = get_ts start_event in
    let end_ts = get_ts end_event in
    let src_chars = get_src_chars ~lnum:(fst start_event) hdr in
    process_cmds ((src_chars, mk_measure start_ts end_ts) :: acc) rest
  | [_] -> die "ill parenthesized events\n"

let parse ~file =
  let cmds = read_file file in
  let cmds = process_cmds [] cmds in
  cmds
