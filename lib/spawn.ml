(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let proto_version = 0
let prefer_sock = Sys.os_type = "Win32"
let accept_timeout = 2.0

let pr_err s = Printf.eprintf "(Spawn  ,%d) %s\n%!" (Unix.getpid ()) s
let prerr_endline s = if !Flags.debug then begin pr_err s end else ()

type req = ReqDie | ReqStats | Hello of int * int
type resp = RespStats of Gc.stat

module type Control = sig
  type handle

  val kill : handle -> unit
  val stats : handle -> Gc.stat
  val wait : handle -> Unix.process_status
  val unixpid : handle -> int
  val uid : handle -> string
  val is_alive : handle -> bool

end

module type Empty = sig end

module type MainLoopModel = sig
  type async_chan
  type condition
  type watch_id

  val add_watch : callback:(condition list -> bool) -> async_chan -> watch_id
  val remove_watch : watch_id -> unit
  val read_all : async_chan -> string
  val async_chan_of_file : Unix.file_descr -> async_chan
  val async_chan_of_socket : Unix.file_descr -> async_chan
end

(* Common code *)
let assert_ b s = if not b then Errors.anomaly (Pp.str s)

let mk_socket_channel () =
  let open Unix in
  let s = socket PF_INET SOCK_STREAM 0 in
  bind s (ADDR_INET (inet_addr_loopback,0));
  listen s 1;
  match getsockname s with
  | ADDR_INET(host, port) ->
      s, string_of_inet_addr host ^":"^ string_of_int port
  | _ -> assert false

let accept s =
  let r, _, _ = Unix.select [s] [] [] accept_timeout in
  if r = [] then raise (Failure (Printf.sprintf
    "The spawned process did not connect back in %2.1fs" accept_timeout));
  let cs, _ = Unix.accept s in
  Unix.close s;
  let cin, cout = Unix.in_channel_of_descr cs, Unix.out_channel_of_descr cs in
  set_binary_mode_in cin true;
  set_binary_mode_out cout true;
  cs, cin, cout

let handshake cin cout =
  try
    output_value cout (Hello (proto_version,Unix.getpid ())); flush cout;
    match input_value cin with
    | Hello(v, pid) when v = proto_version ->
        prerr_endline (Printf.sprintf "Handshake with %d OK" pid);
        pid
    | _ -> raise (Failure "handshake protocol")
  with
  | Failure s | Invalid_argument s | Sys_error s ->
      pr_err ("Handshake failed: "  ^ s); raise (Failure "handshake")
  | End_of_file ->
      pr_err "Handshake failed: End_of_file"; raise (Failure "handshake")

let spawn_sock env prog args =
  let main_sock, main_sock_name = mk_socket_channel () in
  let extra = [| prog; "-main-channel"; main_sock_name |] in
  let args = Array.append extra args in
  prerr_endline ("EXEC: " ^ String.concat " " (Array.to_list args));
  let pid =
    Unix.create_process_env prog args env Unix.stdin Unix.stdout Unix.stderr in
  if pid = 0 then begin
    Unix.sleep 1; (* to avoid respawning like crazy *)
    raise (Failure "create_process failed")
  end;
  let cs, cin, cout = accept main_sock in
  pid, cin, cout, cs

let spawn_pipe env prog args =
  let master2worker_r,master2worker_w = Unix.pipe () in
  let worker2master_r,worker2master_w = Unix.pipe () in
  let extra = [| prog; "-main-channel"; "stdfds" |] in
  let args = Array.append extra args in
  Unix.set_close_on_exec master2worker_w;
  Unix.set_close_on_exec worker2master_r;
  prerr_endline ("EXEC: " ^ String.concat " " (Array.to_list args));
  let pid =
    Unix.create_process_env
      prog args env master2worker_r worker2master_w Unix.stderr in
  if pid = 0 then begin
    Unix.sleep 1; (* to avoid respawning like crazy *)
    raise (Failure "create_process failed")
  end;
  prerr_endline ("PID " ^ string_of_int pid);
  Unix.close master2worker_r;
  Unix.close worker2master_w;
  let cin = Unix.in_channel_of_descr worker2master_r in
  let cout = Unix.out_channel_of_descr master2worker_w in
  set_binary_mode_in cin true;
  set_binary_mode_out cout true;
  pid, cin, cout, worker2master_r

let filter_args args =
  let rec aux = function
    | "-control-channel" :: _ :: rest -> aux rest
    | "-main-channel" :: _ :: rest -> aux rest
    | x :: rest -> x :: aux rest
    | [] -> [] in
  Array.of_list (aux (Array.to_list args))

let spawn_with_control prefer_sock env prog args =
  let control_sock, control_sock_name = mk_socket_channel () in
  let extra = [| "-control-channel"; control_sock_name |] in
  let args = Array.append extra (filter_args args) in
  let (pid, cin, cout, s), is_sock =
    if Sys.os_type <> "Unix" || prefer_sock
    then spawn_sock env prog args, true
    else spawn_pipe env prog args, false in
  let _, oob_resp, oob_req = accept control_sock in
  pid, oob_resp, oob_req, cin, cout, s, is_sock

let output_death_sentence pid oob_req =
  prerr_endline ("death sentence for " ^ pid);
  try output_value oob_req ReqDie; flush oob_req
  with e -> prerr_endline ("death sentence: " ^ Printexc.to_string e)

(* spawn a process and read its output asynchronously *)
module Async(ML : MainLoopModel) = struct

type process = {
  cin  : in_channel;
  cout : out_channel;
  oob_resp : in_channel;
  oob_req  : out_channel;
  gchan : ML.async_chan;
  pid : int;
  mutable watch : ML.watch_id option;
  mutable alive : bool;
}

type callback = ML.condition list -> read_all:(unit -> string) -> bool
type handle = process

let is_alive p = p.alive
let uid { pid; } = string_of_int pid
let unixpid { pid; } = pid

let kill ({ pid = unixpid; oob_req; cin; cout; alive; watch } as p) =
  p.alive <- false;
  if not alive then prerr_endline "This process is already dead"
  else begin try
    Option.iter ML.remove_watch watch;
    output_death_sentence (uid p) oob_req;
    close_in_noerr cin;
    close_out_noerr cout;
    if Sys.os_type = "Unix" then Unix.kill unixpid 9;
    p.watch <- None
  with e -> prerr_endline ("kill: "^Printexc.to_string e) end

let spawn ?(prefer_sock=prefer_sock) ?(env=Unix.environment ())
    prog args callback
=
  let pid, oob_resp, oob_req, cin, cout, main, is_sock =
    spawn_with_control prefer_sock env prog args in
  Unix.set_nonblock main;
  let gchan =
    if is_sock then ML.async_chan_of_socket main
    else ML.async_chan_of_file main in
  let alive, watch = true, None in
  let p = { cin; cout; gchan; pid; oob_resp; oob_req; alive; watch } in
  p.watch <- Some (
    ML.add_watch ~callback:(fun cl ->
      try
        let live = callback cl ~read_all:(fun () -> ML.read_all gchan) in
        if not live then kill p;
        live
      with e when Errors.noncritical e ->
        pr_err ("Async reader raised: " ^ (Printexc.to_string e));
        kill p;
        false) gchan
  );
  p, cout

let stats { oob_req; oob_resp; alive } =
  assert_ alive "This process is dead";
  output_value oob_req ReqStats;
  flush oob_req;
  input_value oob_resp

let rec wait p =
  try snd (Unix.waitpid [] p.pid)
  with
  | Unix.Unix_error (Unix.EINTR, _, _) -> wait p
  | Unix.Unix_error _ -> Unix.WEXITED 0o400

end

module Sync(T : Empty) = struct

type process = {
  cin  : in_channel;
  cout : out_channel;
  oob_resp : in_channel;
  oob_req  : out_channel;
  pid : int;
  mutable alive : bool;
}

type handle = process

let spawn ?(prefer_sock=prefer_sock) ?(env=Unix.environment ()) prog args =
  let pid, oob_resp, oob_req, cin, cout, _, _ =
    spawn_with_control prefer_sock env prog args in
  { cin; cout; pid; oob_resp; oob_req; alive = true }, cin, cout

let is_alive p = p.alive
let uid { pid; } = string_of_int pid
let unixpid { pid = pid; } = pid

let kill ({ pid = unixpid; oob_req; cin; cout; alive } as p) =
  p.alive <- false;
  if not alive then prerr_endline "This process is already dead"
  else begin try
    output_death_sentence (uid p) oob_req;
    close_in_noerr cin;
    close_out_noerr cout;
    if Sys.os_type = "Unix" then Unix.kill unixpid 9;
  with e -> prerr_endline ("kill: "^Printexc.to_string e) end

let stats { oob_req; oob_resp; alive } =
  assert_ alive "This process is dead";
  output_value oob_req ReqStats;
  flush oob_req;
  let RespStats g = input_value oob_resp in g

let wait { pid = unixpid } =
  try snd (Unix.waitpid [] unixpid)
  with Unix.Unix_error _ -> Unix.WEXITED 0o400

end
