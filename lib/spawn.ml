(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let proto_version = 0
let prefer_sock = Sys.os_type = "Win32"
let accept_timeout = 10.0

let pr_err s = Printf.eprintf "(Spawn  ,%d) %s\n%!" (Unix.getpid ()) s
let prerr_endline s = if !Flags.debug then begin pr_err s end else ()

type req = ReqDie | Hello of int * int

module type Control = sig
  type handle

  val kill : handle -> unit
  val wait : handle -> Unix.process_status
  val unixpid : handle -> int
  val uid : handle -> string
  val is_alive : handle -> bool

end

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

(* According to http://caml.inria.fr/mantis/view.php?id=5325
 * you can't use the same socket for both writing and reading (may change
 * in 4.03 *)
let mk_socket_channel () =
  let open Unix in
  let sr = socket PF_INET SOCK_STREAM 0 in
  bind sr (ADDR_INET (inet_addr_loopback,0)); listen sr 1;
  let sw = socket PF_INET SOCK_STREAM 0 in
  bind sw (ADDR_INET (inet_addr_loopback,0)); listen sw 1;
  match getsockname sr, getsockname sw with
  | ADDR_INET(host, portr), ADDR_INET(_, portw) ->
      (sr, sw),
      string_of_inet_addr host
        ^":"^ string_of_int portr ^":"^ string_of_int portw
  | _ -> assert false

let accept (sr,sw) =
  let r, _, _ = Unix.select [sr] [] [] accept_timeout in
  if r = [] then raise (Failure (Printf.sprintf
    "The spawned process did not connect back in %2.1fs" accept_timeout));
  let csr, _ = Unix.accept sr in
  Unix.close sr;
  let cin = Unix.in_channel_of_descr csr in
  set_binary_mode_in cin true;
  let w, _, _ = Unix.select [sw] [] [] accept_timeout in
  if w = [] then raise (Failure (Printf.sprintf
    "The spawned process did not connect back in %2.1fs" accept_timeout));
  let csw, _ = Unix.accept sw in
  Unix.close sw;
  let cout = Unix.out_channel_of_descr csw in
  set_binary_mode_out cout true;
  (csr, csw), cin, cout

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
  pid, cin, cout, (worker2master_r, master2worker_w)

let filter_args args =
  let rec aux = function
    | "-control-channel" :: _ :: rest -> aux rest
    | "-main-channel" :: _ :: rest -> aux rest
    | x :: rest -> x :: aux rest
    | [] -> [] in
  Array.of_list (aux (Array.to_list args))

let spawn_with_control prefer_sock env prog args =
  (* on non-Unix systems we create a control channel *)
  let not_Unix = Sys.os_type <> "Unix" in
  let args = filter_args args in
  let args, control_sock =
    if not_Unix then
      let control_sock, control_sock_name = mk_socket_channel () in
      let extra = [| "-control-channel"; control_sock_name |] in
      Array.append extra args, Some control_sock
    else
      args, None in
  let (pid, cin, cout, s), is_sock =
    if not_Unix (* pipes only work well on Unix *) || prefer_sock
    then spawn_sock env prog args, true
    else spawn_pipe env prog args, false in
  let oob_resp, oob_req =
    if not_Unix then
      let _, oob_resp, oob_req = accept (Option.get control_sock) in
      Some oob_resp, Some oob_req
    else
      None, None in
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
  oob_resp : in_channel option;
  oob_req  : out_channel option;
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

let kill ({ pid = unixpid; oob_resp; oob_req; cin; cout; alive; watch } as p) =
  p.alive <- false;
  if not alive then prerr_endline "This process is already dead"
  else begin try
    Option.iter ML.remove_watch watch;
    Option.iter (output_death_sentence (uid p)) oob_req;
    close_in_noerr cin;
    close_out_noerr cout;
    Option.iter close_in_noerr oob_resp;
    Option.iter close_out_noerr oob_req;
    if Sys.os_type = "Unix" then Unix.kill unixpid 9;
    p.watch <- None
  with e -> prerr_endline ("kill: "^Printexc.to_string e) end

let spawn ?(prefer_sock=prefer_sock) ?(env=Unix.environment ())
    prog args callback
=
  let pid, oob_resp, oob_req, cin, cout, main, is_sock =
    spawn_with_control prefer_sock env prog args in
  Unix.set_nonblock (fst main);
  let gchan =
    if is_sock then ML.async_chan_of_socket (fst main)
    else ML.async_chan_of_file (fst main) in
  let alive, watch = true, None in
  let p = { cin; cout; gchan; pid; oob_resp; oob_req; alive; watch } in
  p.watch <- Some (
    ML.add_watch ~callback:(fun cl ->
      try
        let live = callback cl ~read_all:(fun () -> ML.read_all gchan) in
        if not live then kill p;
        live
      with e when CErrors.noncritical e ->
        pr_err ("Async reader raised: " ^ (Printexc.to_string e));
        kill p;
        false) gchan
  );
  p, cout

let rec wait p =
  (* On windows kill is not reliable, so wait may never return. *) 
  if Sys.os_type = "Unix" then 
    try snd (Unix.waitpid [] p.pid)
    with
    | Unix.Unix_error (Unix.EINTR, _, _) -> wait p
    | Unix.Unix_error _ -> Unix.WEXITED 0o400
  else Unix.WEXITED 0o400

end

module Sync () = struct

type process = {
  cin  : in_channel;
  cout : out_channel;
  oob_resp : in_channel option;
  oob_req  : out_channel option;
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

let kill ({ pid = unixpid; oob_req; oob_resp; cin; cout; alive } as p) =
  p.alive <- false;
  if not alive then prerr_endline "This process is already dead"
  else begin try
    Option.iter (output_death_sentence (uid p)) oob_req;
    close_in_noerr cin;
    close_out_noerr cout;
    Option.iter close_in_noerr oob_resp;
    Option.iter close_out_noerr oob_req;
    if Sys.os_type = "Unix" then Unix.kill unixpid 9;
  with e -> prerr_endline ("kill: "^Printexc.to_string e) end

let rec wait p =
  (* On windows kill is not reliable, so wait may never return. *) 
  if Sys.os_type = "Unix" then 
    try snd (Unix.waitpid [] p.pid)
    with
    | Unix.Unix_error (Unix.EINTR, _, _) -> wait p
    | Unix.Unix_error _ -> Unix.WEXITED 0o400
  else Unix.WEXITED 0o400

end
