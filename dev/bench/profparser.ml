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

   We use undocumented Yojson.Basic.read_comma to detect the end.
*)

let rec find_cmds acc (lstate,lex as ch) =
  let v = YB.from_lexbuf lstate ~stream:true lex in
  let fname = Option.get lstate.Yojson.fname in
  let lnum = lstate.Yojson.lnum in
  let is_last = try YB.read_comma lstate lex; false with Yojson.Json_error _ -> true in
  let acc = match v with
    | `Assoc l -> begin match assoc "name" l with
        | `String "command" -> (lnum,l) :: acc
        | _ -> acc
      end
    | _ -> die "File %S line %d: unrecognised value\n" fname lnum
  in
  if is_last then acc else find_cmds acc ch

type 'ch channel = {
  open_in : string -> 'ch;
  close_in : 'ch -> unit;
  really_input : 'ch -> Bytes.t -> int -> int -> unit;
  input : 'ch -> Bytes.t -> int -> int -> int;
}

let file_channel = {
  open_in = open_in;
  close_in = close_in;
  really_input = really_input;
  input = input;
}

let gzip_channel = {
  open_in = Gzip.open_in;
  close_in = Gzip.close_in;
  really_input = Gzip.really_input;
  input = Gzip.input;
}

type any_channel = AnyChannel : 'ch channel -> any_channel

let channel_for fname =
  if CString.is_suffix ".json" fname then AnyChannel file_channel
  else AnyChannel gzip_channel

let input_exactly ch_fns ch expected =
  let buf = Bytes.create (String.length expected) in
  ch_fns.really_input ch buf 0 (String.length expected);
  assert (Bytes.to_string buf = expected)

let read_file fname =
  let AnyChannel ch_fns = channel_for fname in
  let ch = ch_fns.open_in fname in
  try
    (* ignore initial line *)
    let () = input_exactly ch_fns ch {|{ "traceEvents": [|} in
    let lex = Lexing.from_function ~with_positions:false (fun buf n -> ch_fns.input ch buf 0 n) in
    let lstate = Yojson.init_lexer ~fname ~lnum:2 () in
    let cmds = find_cmds [] (lstate,lex) in
    ch_fns.close_in ch;
    cmds
  with e -> ch_fns.close_in ch; raise e

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
