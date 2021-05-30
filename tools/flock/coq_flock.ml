(* Simple OCaml version of flock *)

let fail msg =
  Format.eprintf "coq_flock: %s@\n%!" msg;
  exit 1

(* operations for flock *)
module Flock : sig
  type operation

  val lock_sh : operation
  val lock_ex : operation
  val lock_un : operation

  val flock : Unix.file_descr -> operation -> int
end = struct

  type operation = int

  let lock_sh = 0
  let lock_ex = 1
  let lock_un = 2

  external flock : Unix.file_descr -> int -> int = "coq_flock"
end


(* flock file command args, we parse the arguments and extract the
   command to be sent to Unix.create_process *)
let parse_args () =
  let l = Array.length Sys.argv in
  if l < 3 then
    fail "wrong number of arguments, use 'coq_flock file command args'"
  else
    let file_lock = Sys.argv.(1) in
    let command = Sys.argv.(2) in
    let arguments = Array.make (l-2) "" in
    Array.set arguments 0 command;
    Array.blit Sys.argv 3 arguments 1 (l-3);
    file_lock, command, arguments

let lock f =
  let fd = Unix.openfile f Unix.[O_CREAT;O_RDWR] 0o644 in
  let res = Flock.(flock fd lock_ex) in
  if res <> 0 then fail "flock syscall error!" else fd

let unlock fid =
  let _res = Flock.(flock fid lock_un) in
  Unix.close fid

let exec_program fid command args =
  let pid = Unix.create_process command args Unix.stdin Unix.stdout Unix.stderr in
  let _pid, status = Unix.waitpid [] pid in
  unlock fid;
  (* It is critical that we don't raise after this point, otherwise we
     will double-free the lock *)
  match status with
  | Unix.WEXITED 0 -> ()
  | Unix.WSTOPPED _ -> ()
  | Unix.WEXITED 127 ->
    (* per create_process documentation *)
    fail ("Couldn't execute program " ^ command)
  | Unix.WEXITED err ->
    exit err
  | Unix.WSIGNALED s ->
    Unix.kill (Unix.getpid ()) s

let main () =
  let file_lock, command, args = parse_args () in
  let fid = lock file_lock in
  try exec_program fid command args
  with exn -> unlock fid; raise exn

let _ =
  try main ()
  with exn ->
    let msg = Printexc.to_string exn in
    fail msg
