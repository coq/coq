(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let die fmt = Printf.kfprintf (fun _ -> exit 1) stderr fmt

type char_loc = {
  start_char : int;
  stop_char : int;
}

type source_loc = {
  chars : char_loc;
  line : int;
  text : string;
}

let same_char_locs a b = a.start_char = b.start_char && a.stop_char = b.stop_char

type measure = { str: string; q: Q.t; }

let dummy_measure = { str="0"; q=Q.zero; }

let combine_related_data data =
  let nvals = Array.length (snd (data.(0))) in
  let fname0, data0 = data.(0) in
  let () =
    Array.iter (fun (fname, v) ->
        if nvals <> Array.length v
        then die "Mismatch between %s and %s: different measurement counts\n" fname0 fname)
      data
  in
  Array.init nvals (fun i ->
      let loc0, _ = data0.(i) in
      let data = data |> Array.map (fun (fname, fdata) ->
          let floc, v = fdata.(i) in
          if same_char_locs loc0 floc then v
          else die "Mismatch between %s and %s (measurement %d)\n" fname0 fname (i+1))
      in
      loc0, data)

let read_whole_file f =
  let sourcelen = (Unix.stat f).st_size in
  let ch = try open_in f with Sys_error e -> die "Could not open %s: %s" f e in
  let s = really_input_string ch sourcelen in
  close_in ch;
  s
