(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Benchlib
open BenchUtil

let profile =
  {|{ "traceEvents": [
{ "name": "command", "ph": "B", "ts": 100, "pid": 1, "tid": 1,
  "args": { "cmd": "Chars 0 - 1 First", "line": "1" } },
{ "name": "command", "ph": "E", "ts": 110, "pid": 1, "tid": 1,
  "args": {
    "major_words": "100 w", "minor_words": "0 w",
    "major_collect": 1, "minor_collect": 2, "heap_words": 100,
    "instr": 100,
    "gc_boundaries": {
      "major_collect_start": 10, "minor_collect_start": 100,
      "major_collect_stop": 11, "minor_collect_stop": 102,
      "major_words_start": 1000, "major_words_stop": 1100,
      "instr_start": 10000, "instr_stop": 10100
    }
  } },
{ "name": "command", "ph": "B", "ts": 120, "pid": 1, "tid": 1,
  "args": { "cmd": "Chars 2 - 3 Second", "line": "2" } },
{ "name": "command", "ph": "E", "ts": 130, "pid": 1, "tid": 1,
  "args": {
    "major_words": "100 w", "minor_words": "0 w",
    "major_collect": 0, "minor_collect": 1, "heap_words": 100,
    "instr": 100,
    "gc_boundaries": {
      "major_collect_start": 11, "minor_collect_start": 105,
      "major_collect_stop": 11, "minor_collect_stop": 106,
      "major_words_start": 1150, "major_words_stop": 1250,
      "instr_start": 10150, "instr_stop": 10250
    }
  } }
], "displayTimeUnit": "us" }
|}

let legacy_profile =
  {|{ "traceEvents": [
{ "name": "command", "ph": "B", "ts": 100, "pid": 1, "tid": 1,
  "args": { "cmd": "Chars 0 - 1 First", "line": "1" } },
{ "name": "command", "ph": "E", "ts": 110, "pid": 1, "tid": 1,
  "args": {
    "major_words": "0 w", "minor_words": "0 w",
    "major_collect": 0, "minor_collect": 0, "heap_words": 100,
    "gc_boundaries": {
      "major_collect_start": 10, "minor_collect_start": 100,
      "major_collect_stop": 10, "minor_collect_stop": 100
    }
  } },
{ "name": "command", "ph": "B", "ts": 120, "pid": 1, "tid": 1,
  "args": { "cmd": "Chars 2 - 3 Second", "line": "2" } },
{ "name": "command", "ph": "E", "ts": 130, "pid": 1, "tid": 1,
  "args": {
    "major_words": "0 w", "minor_words": "0 w",
    "major_collect": 0, "minor_collect": 0, "heap_words": 100,
    "gc_boundaries": {
      "major_collect_start": 11, "minor_collect_start": 102,
      "major_collect_stop": 11, "minor_collect_stop": 102
    }
  } }
], "displayTimeUnit": "us" }
|}

let with_profile contents f =
  let file = Filename.temp_file "profparser" ".json" in
  let ch = open_out_bin file in
  output_string ch contents;
  close_out ch;
  Fun.protect ~finally:(fun () -> Sys.remove file) (fun () -> f file)

let expect_gap ~major ~minor ~major_words = function
  | Some gap ->
    assert (gap.major = major);
    assert (gap.minor = minor);
    assert (gap.major_words = major_words);
    gap
  | None -> assert false

let expect_instructions ~start ~stop = function
  | Some instructions ->
    assert (instructions.start = start);
    assert (instructions.stop = stop)
  | None -> assert false

let () = with_profile profile @@ fun file ->
  match Profparser.parse ~file with
  | [(_, first); (_, second)] ->
    assert (first.gc_before = None);
    let gap = expect_gap ~major:0 ~minor:3 ~major_words:(Some 50) first.gc_after in
    expect_instructions ~start:10100 ~stop:10150 gap.instructions;
    assert (first.gc_after = second.gc_before);
    assert (second.gc_after = None)
  | _ -> assert false

let () = with_profile legacy_profile @@ fun file ->
  match Profparser.parse ~file with
  | [(_, first); (_, second)] ->
    assert (first.gc_before = None);
    let gap = expect_gap ~major:1 ~minor:2 ~major_words:None first.gc_after in
    assert (gap.instructions = None);
    assert (first.gc_after = second.gc_before);
    assert (second.gc_after = None)
  | _ -> assert false
