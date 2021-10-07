(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type thread_ic = in_channel

let prepare_in_channel_for_thread_friendly_io ic = ic

let thread_friendly_read_fd fd s ~off ~len =
  let rec loop () =
    try Unix.read fd s off len
    with Unix.Unix_error(Unix.EINTR,_,_) -> loop ()
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

let really_read_fd_2_oc fd oc len =
  let i = ref 0 in
  let size = 4096 in
  let s = Bytes.create size in
  while !i < len do
    let len = len - !i in
    let r = thread_friendly_read_fd fd s ~off:0 ~len:(min len size) in
    if r = 0 then raise End_of_file;
    i := !i + r;
    output oc s 0 r;
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
    let s = Bytes.make 1 '\000' in
    let endl = Bytes.of_string "\n" in
    (* Bytes.equal is in 4.03.0 *)
    while Bytes.compare s endl <> 0 do
      let n = thread_friendly_read_fd fd s ~off:0 ~len:1 in
      if n = 0 then raise End_of_file;
      if Bytes.compare s endl <> 0 then Buffer.add_bytes b s;
    done;
    Buffer.contents b
  with Unix.Unix_error _ -> raise End_of_file

let thread_friendly_input_value ic =
  try
    let fd = Unix.descr_of_in_channel ic in
    let header = Bytes.create Marshal.header_size in
    really_read_fd fd header 0 Marshal.header_size;
    let body_size = Marshal.data_size header 0 in
    let desired_size = body_size + Marshal.header_size in
    if desired_size <= Sys.max_string_length then begin
      let msg = Bytes.create desired_size in
      Bytes.blit header 0 msg 0 Marshal.header_size;
      really_read_fd fd msg Marshal.header_size body_size;
      Marshal.from_bytes msg 0
    end else begin
      (* Workaround for 32 bit systems and data > 16M *)
      let name, oc =
        Filename.open_temp_file ~mode:[Open_binary] "coq" "marshal" in
      try
        output oc header 0 Marshal.header_size;
        really_read_fd_2_oc fd oc body_size;
        close_out oc;
        let ic = open_in_bin name in
        let data = Marshal.from_channel ic in
        close_in ic;
        Sys.remove name;
        data
      with e -> Sys.remove name; raise e
    end
  with Unix.Unix_error _ | Sys_error _ -> raise End_of_file

(* On the ocaml runtime used in some opam-for-windows version the
 * [Thread.sigmask] API raises Invalid_argument "not implemented",
 * hence we protect the call and turn the exception into a no-op *)
let mask_sigalrm f x =
  begin try ignore(Thread.sigmask Unix.SIG_BLOCK [Sys.sigalrm])
  with Invalid_argument _ -> () end;
  f x

let create f x =
  Thread.create (mask_sigalrm f) x

(*
  Atomic mutex lock taken from https://gitlab.com/gadmm/memprof-limits/-/blob/master/src/thread_map.ml#L23-34
  Critical sections :
   - Mutex.lock does not poll on leaving the blocking section
     since 4.12.
   - Never inline, to avoid theoretically-possible reorderings with
     flambda.
     (workaround to the lack of masking)
*)

(* We inline the call to Mutex.unlock to avoid polling in bytecode mode *)
external unlock: Mutex.t -> unit = "caml_mutex_unlock"

let[@inline never] with_lock m ~scope =
  let () = Mutex.lock m (* BEGIN ATOMIC *) in
  match (* END ATOMIC *) scope () with
  | (* BEGIN ATOMIC *) x -> unlock m ; (* END ATOMIC *) x
  | (* BEGIN ATOMIC *) exception e -> unlock m ; (* END ATOMIC *) raise e
