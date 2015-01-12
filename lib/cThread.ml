(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type thread_ic = in_channel

let prepare_in_channel_for_thread_friendly_io ic =
  Unix.set_nonblock (Unix.descr_of_in_channel ic); ic

let safe_wait_timed_read fd time =
  try Thread.wait_timed_read fd time
  with Unix.Unix_error (Unix.EINTR, _, _) ->
    (** On Unix, the above function may raise this exception when it is
        interrupted by a signal. (It uses Unix.select internally.) *)
    false

let thread_friendly_read_fd fd s ~off ~len =
  let rec loop () =
    try Unix.read fd s off len
    with Unix.Unix_error((Unix.EWOULDBLOCK|Unix.EAGAIN|Unix.EINTR),_,_) ->
      while not (safe_wait_timed_read fd 1.0) do Thread.yield () done;
      loop ()
  in 
    loop ()

let thread_friendly_read ic s ~off ~len =
  try
    let fd = Unix.descr_of_in_channel ic in
    thread_friendly_read_fd fd s ~off ~len
  with Unix.Unix_error _ -> 0

let really_read_fd fd s off len =
  let i = ref 0 in
  while !i < len do
    let off = off + !i in
    let len = len - !i in
    let r = thread_friendly_read_fd fd s ~off ~len in
    if r = 0 then raise End_of_file;
    i := !i + r
  done

let thread_friendly_really_read ic s ~off ~len =
  try
    let fd = Unix.descr_of_in_channel ic in
    really_read_fd fd s off len
  with Unix.Unix_error _ -> raise End_of_file

let thread_friendly_really_read_line ic =
  try
    let fd = Unix.descr_of_in_channel ic in
    let b = Buffer.create 1024 in
    let s = String.make 1 '\000' in
    while s <> "\n" do
      let n = thread_friendly_read_fd fd s ~off:0 ~len:1 in
      if n = 0 then raise End_of_file;
      if s <> "\n" then Buffer.add_string b s;
    done;
    Buffer.contents b
  with Unix.Unix_error _ -> raise End_of_file

let thread_friendly_input_value ic =
  try
    let fd = Unix.descr_of_in_channel ic in
    let header = String.create Marshal.header_size in
    really_read_fd fd header 0 Marshal.header_size;
    let body_size = Marshal.data_size header 0 in
    let msg = String.create (body_size + Marshal.header_size) in
    String.blit header 0 msg 0 Marshal.header_size;
    really_read_fd fd msg Marshal.header_size body_size;
    Marshal.from_string msg 0
  with Unix.Unix_error _ -> raise End_of_file

