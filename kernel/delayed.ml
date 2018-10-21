(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(** Serialized objects loaded on-the-fly *)

exception Faulty of string

type 'a t = {
  del_file : string;
  del_off : int;
  del_digest : Digest.t;
}

let in_delayed f ch =
  let pos = pos_in ch in
  let _, digest = System.skip_in_segment f ch in
  ({ del_file = f; del_digest = digest; del_off = pos; }, digest)

(** Fetching a table of opaque terms at position [pos] in file [f],
    expecting to find first a copy of [digest]. *)

let raw_intern_library f =
  System.with_magic_number_check
    (System.raw_intern_state Coq_config.vo_magic_number) f

let fetch del =
  let { del_digest = digest; del_file = f; del_off = pos; } = del in
  try
    let ch = raw_intern_library f in
    let () = seek_in ch pos in
    let obj, _, digest' = System.marshal_in_segment f ch in
    let () = close_in ch in
    if not (String.equal digest digest') then raise (Faulty f);
    obj
  with e when CErrors.noncritical e -> raise (Faulty f)
