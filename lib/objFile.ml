(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open System

let magic_number = 0x436F7121l (* "Coq!" *)

let error_corrupted file s =
  CErrors.user_err (str file ++ str ": " ++ str s ++ str ". Try to rebuild it.")

let open_trapping_failure name =
  try open_out_bin name
  with e when CErrors.noncritical e ->
    CErrors.user_err (str "Can't open " ++ str name ++ spc() ++ str "(" ++ CErrors.print e ++ str ").")

(*

int32: big-endian, 4 bytes
int64: big-endian, 8 bytes

-- string --
int32 | length of the next field
data  |

-- segment summary --
string | name
int64  | absolute position
int64  | length (without hash)
hash   | MD5 (16 bytes)

-- segment --
...  | binary data
hash | MD5 (16 bytes)

-- summary --
int32 | number of segment summaries
s1    |
...   | segment summaries
sn    |

-- vo --
int32   | magic number
int32   | Coq version
int64   | absolute position of the summary
...     | segments
summary |

*)

type 'a segment = {
  name : string;
  pos : int64;
  len : int64;
  hash : Digest.t;
}

type in_handle = {
  in_filename : string;
  in_channel : in_channel;
  in_segments : Obj.t segment CString.Map.t;
}

type out_handle = {
  out_filename : string;
  out_channel : out_channel;
  mutable out_segments : Obj.t segment CString.Map.t;
}

type 'a id = { id : string }

let make_id id = { id }

let input_segment_summary ch =
  let nlen = input_int32 ch in
  let name = really_input_string ch (Int32.to_int nlen) in
  let pos = input_int64 ch in
  let len = input_int64 ch in
  let hash = Digest.input ch in
  { name; pos; len; hash }

let output_segment_summary ch seg =
  let nlen = Int32.of_int (String.length seg.name) in
  let () = output_int32 ch nlen in
  let () = output_string ch seg.name in
  let () = output_int64 ch seg.pos in
  let () = output_int64 ch seg.len in
  let () = Digest.output ch seg.hash in
  ()

let rec input_segment_summaries ch n accu =
  if Int32.equal n 0l then accu
  else
    let s = input_segment_summary ch in
    let accu = CString.Map.add s.name s accu in
    input_segment_summaries ch (Int32.pred n) accu

let marshal_in_segment (type a) h ~segment : a * Digest.t =
  let { in_channel = ch } = h in
  let s = CString.Map.find segment.id h.in_segments in
  let () = LargeFile.seek_in ch s.pos in
  let (v : a) = marshal_in h.in_filename ch in
  let () = assert (Int64.equal (LargeFile.pos_in ch) (Int64.add s.pos s.len)) in
  let h = Digest.input ch in
  let () = assert (String.equal h s.hash) in
  (v, s.hash)

let marshal_out_segment h ~segment v =
  let { out_channel = ch } = h in
  let () = assert (not (CString.Map.mem segment.id h.out_segments)) in
  let pos = LargeFile.pos_out ch in
  let () = Marshal.to_channel ch v [] in
  let () = flush ch in
  let pos' = LargeFile.pos_out ch in
  let len = Int64.sub pos' pos in
  let hash =
    let in_ch = open_in_bin h.out_filename in
    let () = LargeFile.seek_in in_ch pos in
    let digest = Digest.channel in_ch (Int64.to_int len) in
    let () = close_in in_ch in
    digest
  in
  let () = Digest.output ch hash in
  let s = { name = segment.id; pos; len; hash } in
  let () = h.out_segments <- CString.Map.add segment.id s h.out_segments in
  ()

let marshal_out_binary h ~segment =
  let { out_channel = ch } = h in
  let () = assert (not (CString.Map.mem segment.id h.out_segments)) in
  let pos = LargeFile.pos_out ch in
  let finish () =
    let () = flush ch in
    let pos' = LargeFile.pos_out ch in
    let len = Int64.sub pos' pos in
    let hash =
      let in_ch = open_in_bin h.out_filename in
      let () = LargeFile.seek_in in_ch pos in
      let digest = Digest.channel in_ch (Int64.to_int len) in
      let () = close_in in_ch in
      digest
    in
    let () = Digest.output ch hash in
    let s = { name = segment.id; pos; len; hash } in
    h.out_segments <- CString.Map.add segment.id s h.out_segments
  in
  ch, finish

let open_in ~file =
  try
    let ch = open_in_bin file in
    let magic = input_int32 ch in
    let version = input_int32 ch in
    let () =
      if not (Int32.equal magic magic_number) then
        let e = { filename = file; actual = magic; expected = magic_number } in
        raise (Bad_magic_number e)
    in
    let () =
      let expected = Coq_config.vo_version in
      if not (Int32.equal version expected) then
        let e = { filename = file; actual = version; expected } in
        raise (Bad_version_number e)
    in
    let summary_pos = input_int64 ch in
    let () = LargeFile.seek_in ch summary_pos in
    let nsum = input_int32 ch in
    let seg = input_segment_summaries ch nsum CString.Map.empty in
    { in_filename = file; in_channel = ch; in_segments = seg }
  with
  | End_of_file -> error_corrupted file "premature end of file"
  | Failure s | Sys_error s -> error_corrupted file s

let close_in ch =
  close_in ch.in_channel

let get_segment (type a) ch ~(segment : a id) : a segment =
  (CString.Map.find segment.id ch.in_segments :> a segment)

let segments ch = ch.in_segments

let open_out ~file =
  let ch = open_trapping_failure file in
  let () = output_int32 ch magic_number in
  let () = output_int32 ch Coq_config.vo_version in
  let () = output_int64 ch 0L (* placeholder *) in
  { out_channel = ch; out_segments = CString.Map.empty; out_filename = file }

let close_out { out_channel = ch; out_segments = seg } =
  let () = flush ch in
  let pos = LargeFile.pos_out ch in
  (* Write the segment summary *)
  let () = output_int32 ch (Int32.of_int (CString.Map.cardinal seg)) in
  let iter _ s = output_segment_summary ch s in
  let () = CString.Map.iter iter seg in
  (* Overwrite the position place holder *)
  let () = LargeFile.seek_out ch 8L in
  let () = output_int64 ch pos in
  let () = flush ch in
  close_out ch

module Delayed = struct

  exception Faulty of string * string * string

  let () = CErrors.register_handler Pp.(function
      | Faulty (file,what,dp) ->
        let pp =
          str "The file " ++ str file ++ str " (bound to " ++ str dp ++
          str ") is corrupted,\ncannot load some " ++ str what ++ str " in it.\n"
        in
        Some pp
      | _-> None)

  type 'a delayed = {
    del_what : 'a id;
    (* None: non verbose mode *)
    del_whatname : string option;
    del_whatfor : string;
    del_file : string;
    del_off : int64;
    del_digest : Digest.t;
  }

  type 'a node = ToFetch of 'a delayed | Fetched of ('a,exn) result

  type 'a t = 'a node ref

  let in_delayed ~file ~what ~whatfor ch ~segment =
    let seg = get_segment ch ~segment in
    let digest = seg.hash in
    { del_what = segment; del_whatname = what; del_whatfor = whatfor;
      del_file = file; del_digest = digest; del_off = seg.pos; }

  let make ~file ~what ~whatfor ch ~segment =
    let del = in_delayed ~file ~what ~whatfor ch ~segment in
    ref (ToFetch del)

  (** Fetching a table of opaque terms at position [pos] in file [f],
      expecting to find first a copy of [digest]. *)

  let fetch_delayed ~verbose del =
    let { del_what = what; del_whatname = whatname; del_whatfor = whatfor;
          del_digest = digest; del_file = f; del_off = pos; } = del in
    let () = match whatname with
      | None -> ()
      | Some whatname ->
        Flags.if_verbose
          Feedback.msg_info
          Pp.(str"Fetching " ++ str whatname ++ str" from disk for " ++ str whatfor)
    in
    let ch = open_in_bin f in
    let obj, digest' =
      try
        let () = LargeFile.seek_in ch pos in
        let obj = System.marshal_in f ch in
        let digest' = Digest.input ch in
        obj, digest'
      with e -> Stdlib.close_in ch; raise e
    in
    Stdlib.close_in ch;
    if not (String.equal digest digest') then Error (Faulty (f,what.id,whatfor))
    else Ok obj

  let eval ~verbose r = match !r with
    | Fetched v -> v
    | ToFetch del ->
      let v = fetch_delayed ~verbose del in
      let () = r := Fetched v in
      v

  let eval ~verbose r =
    match eval ~verbose r with
    | Ok v -> v
    | Error e -> raise e

  let return v = ref (Fetched (Ok v))

end
