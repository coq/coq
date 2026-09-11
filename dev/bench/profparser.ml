(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr (fmt^^"\n%!")

module YB = Yojson.Basic
module YBU = YB.Util

let assoc a b : YB.t = CList.assoc_f String.equal a b

let rec assocs keys (obj : YB.t) =
  match keys, obj with
  | [], _ -> obj
  | k :: keys, `Assoc entries ->
    let obj = assoc k entries in
    assocs keys obj
  | _, _ ->
    die "Not an object"

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
    | _ -> die "File %S line %d: unrecognised value" fname lnum
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
  | _ -> die "line %d: malformed value (expected string)" lnum

let get_ts (lnum, l) = match assoc "ts" l with
  | `Int ts -> ts
  | _ -> die "line %d: malformed ts" lnum

let get_src_info (lnum, l) = match assoc "args" l with
  | `Assoc l ->
    let hdr = force_string lnum (assoc "cmd" l) in
    let line = match assoc "line" l with
      | `Int l -> l
      | `String l -> int_of_string l
      | _ -> die "line %d: malformed line number" lnum
    in
    hdr, line
  | _ -> die "line %d: malformed args" lnum

let hdr_regex = Str.regexp {|^Chars \([0-9]+\) - \([0-9]+\) |}

let get_src_chars ~lnum hdr =
  if not (Str.string_match hdr_regex hdr 0) then die "line %d: malformed command header" lnum
  else
    { start_char = int_of_string @@ Str.matched_group 1 hdr;
      stop_char = int_of_string @@ Str.matched_group 2 hdr; }

let mk_memory (lnum, l) =
  let args = assoc "args" l in
  try Some {
      major_words = YBU.(to_string @@ member "major_words" args) ;
      minor_words = YBU.(to_string @@ member "minor_words" args);
      major_collect = YBU.(to_int @@ member "major_collect" args);
      minor_collect = YBU.(to_int @@ member "minor_collect" args);
      heap_words =
        (try Some YBU.(to_int @@ member "heap_words" args)
         with YBU.Type_error _ -> None);
    }
  with YBU.Type_error (msg,_) -> die "line %d: %s" lnum msg

type gc_boundary = {
  major_collections : int;
  minor_collections : int;
  major_words : int option;
  instructions : int option;
}

type gc_boundaries = {
  start_boundary : gc_boundary;
  stop_boundary : gc_boundary;
}

let mk_gc_boundaries (lnum, l) =
  let args = match assoc "args" l with
    | `Assoc args -> args
    | _ -> die "line %d: malformed args" lnum
  in
  match CList.assoc_f_opt String.equal "gc_boundaries" args with
  | None -> None
  | Some (`Assoc boundaries) ->
    let get name =
      match CList.assoc_f_opt String.equal name boundaries with
      | Some (`Int i) -> i
      | Some _ | None ->
        die "line %d: malformed gc_boundaries.%s" lnum name
    in
    let get_optional name =
      match CList.assoc_f_opt String.equal name boundaries with
      | None -> None
      | Some (`Int i) -> Some i
      | Some _ -> die "line %d: malformed gc_boundaries.%s" lnum name
    in
    let get_pair start_name stop_name =
      match get_optional start_name, get_optional stop_name with
      | None, None -> None, None
      | Some start, Some stop -> Some start, Some stop
      | Some _, None | None, Some _ ->
        die "line %d: gc_boundaries.%s and gc_boundaries.%s must occur together"
          lnum start_name stop_name
    in
    let major_words_start, major_words_stop =
      get_pair "major_words_start" "major_words_stop"
    in
    let instr_start, instr_stop = get_pair "instr_start" "instr_stop" in
    Some {
      start_boundary = {
        major_collections = get "major_collect_start";
        minor_collections = get "minor_collect_start";
        major_words = major_words_start;
        instructions = instr_start;
      };
      stop_boundary = {
        major_collections = get "major_collect_stop";
        minor_collections = get "minor_collect_stop";
        major_words = major_words_stop;
        instructions = instr_stop;
      };
    }
  | Some _ -> die "line %d: malformed gc_boundaries" lnum

let checked_delta ~lnum ~name start stop =
  let delta = stop - start in
  if delta < 0 then die "line %d: gc_boundaries.%s decreased within the span" lnum name;
  delta

let check_gc_boundaries ~lnum memory instructions = function
  | None -> ()
  | Some boundaries ->
    let start = boundaries.start_boundary in
    let stop = boundaries.stop_boundary in
    let major =
      checked_delta ~lnum ~name:"major_collect" start.major_collections stop.major_collections
    in
    let minor =
      checked_delta ~lnum ~name:"minor_collect" start.minor_collections stop.minor_collections
    in
    memory |> Option.iter (fun memory ->
        if major <> memory.major_collect || minor <> memory.minor_collect then
          die "line %d: GC boundaries do not match the span collection counts" lnum);
    begin match start.major_words, stop.major_words with
      | Some start, Some stop ->
        ignore (checked_delta ~lnum ~name:"major_words" start stop : int)
      | None, None -> ()
      | Some _, None | None, Some _ -> assert false
    end;
    match start.instructions, stop.instructions with
    | Some start, Some stop ->
      let boundary_instructions = checked_delta ~lnum ~name:"instr" start stop in
      begin match instructions with
        | Some instructions when instructions = boundary_instructions -> ()
        | Some _ -> die "line %d: GC boundaries do not match the span instruction count" lnum
        | None -> die "line %d: GC boundaries have instruction counts but the span does not" lnum
      end
    | None, None -> ()
    | Some _, None | None, Some _ -> assert false

let mk_time start stop =
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

let get_instr (lnum, l) =
  let args = assoc "args" l in
  try Some YBU.(to_int @@ member "instr" args)
  with YBU.Type_error _ -> None

type command = {
  loc : char_loc;
  data : data;
  gc_boundaries : gc_boundaries option;
}

let rec process_cmds acc = function
  | [] -> acc
  | end_event :: start_event :: rest ->
    let start_ts = get_ts start_event in
    let end_ts = get_ts end_event in
    let hdr_line =
      (* TRANSITIONARY: The src info is either in the start or end event
         depending on the exact commit that generated the profiles.
      *)
      try
        Some (get_src_info start_event)
      with
      | Not_found ->
        try
          Some (get_src_info end_event)
        with
        | Not_found ->
          (* TRANSITIONARY: new versions produce command spans even for commands
             without src info. They must have [skip:1] in the end event. *)
          match assocs ["args"; "skip"] (`Assoc (snd end_event)) with
          | `Int 1 ->
            None
          | _ | exception _ ->
          die "Could not find src info in either start (ts=%i) or end (ts=%i) event and the end event does not have [skip:1]" start_ts end_ts
    in
    begin
      match hdr_line with
      | None -> process_cmds acc rest
      | Some (hdr, line) ->
      let loc = get_src_chars ~lnum:(fst start_event) hdr in
      let time = mk_time start_ts end_ts in
      let memory = mk_memory end_event in
      let instructions = get_instr end_event in
      let gc_boundaries = mk_gc_boundaries end_event in
      let () =
        check_gc_boundaries ~lnum:(fst end_event) memory instructions gc_boundaries
      in
      let data = {
        time;
        memory;
        instructions;
        gc_before = None;
        gc_after = None;
      } in
      process_cmds ({ loc; data; gc_boundaries; } :: acc) rest
    end
  | [_] -> die "ill parenthesized events"

let gc_gap ~file left right =
  match left.gc_boundaries, right.gc_boundaries with
  | Some left_boundaries, Some right_boundaries ->
    let start = left_boundaries.stop_boundary in
    let stop = right_boundaries.start_boundary in
    let checked_delta name start stop =
      let delta = stop - start in
      if delta < 0 then
        die "File %S: GC boundary counter %s decreased between commands ending at character %d and starting at character %d"
          file name left.loc.stop_char right.loc.start_char;
      delta
    in
    let major =
      checked_delta "major_collect" start.major_collections stop.major_collections
    in
    let minor =
      checked_delta "minor_collect" start.minor_collections stop.minor_collections
    in
    let major_words = match start.major_words, stop.major_words with
      | Some start, Some stop -> Some (checked_delta "major_words" start stop)
      | None, _ | _, None -> None
    in
    let instructions = match start.instructions, stop.instructions with
      | Some start, Some stop ->
        ignore (checked_delta "instr" start stop : int);
        Some { start; stop }
      | None, _ | _, None -> None
    in
    Some { major; minor; major_words; instructions }
  | None, _ | _, None -> None

let add_gc_edges ~file commands =
  let rec loop before acc = function
    | [] -> List.rev acc
    | command :: rest ->
      let after = match rest with
        | [] -> None
        | next :: _ -> gc_gap ~file command next
      in
      let data = { command.data with gc_before = before; gc_after = after; } in
      loop after ((command.loc, data) :: acc) rest
  in
  loop None [] commands

let parse ~file =
  let cmds = read_file file in
  let cmds = process_cmds [] cmds in
  add_gc_edges ~file cmds
