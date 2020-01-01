(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a t = {
  mutable valid : bool;
  filename : string;
}

let finaliser (s : 'a t) =
  if s.valid then
    let () = Sys.remove s.filename in
    s.valid <- false

let make (v : 'a) : 'a t =
  let file, chan = Filename.open_temp_file "coqopaque" "" in
  let () = Marshal.to_channel chan v [] in
  let () = flush chan in
  let () = close_out chan in
  let s = { filename = file; valid = true } in
  let () = Gc.finalise finaliser s in
  s

let get (s : 'a t) =
  (* Data on disk *)
  let ()  = assert s.valid in
  let chan = open_in s.filename in
  let v = Marshal.from_channel chan in
  let () = close_in chan in
  v

let delete (s : 'a t) =
  let ()  = assert s.valid in
  finaliser s

let serialize s ch =
  let () = assert s.valid in
  let inch = open_in_bin s.filename in
  let buf = Bytes.create 1024 in
  let b = ref true in
  while !b do
    let len = input inch buf 0 1024 in
    if Int.equal len 0 then b := false
    else
      output ch buf 0 len
  done;
  close_in inch
