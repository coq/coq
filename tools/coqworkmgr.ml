(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CoqworkmgrApi

let debug = ref false

type party = {
          sock     : Unix.file_descr;
          cout     : out_channel;
  mutable tokens   : int;
          priority : priority;
}

let answer party msg =
  output_string party.cout (print_response msg); flush party.cout

let mk_socket_channel () =
  let open Unix in
  let s = socket PF_INET SOCK_STREAM 0 in
  bind s (ADDR_INET (inet_addr_loopback,0));
  listen s 1;
  match getsockname s with
  | ADDR_INET(host, port) ->
      s, string_of_inet_addr host ^":"^ string_of_int port
  | _ -> assert false

module Queue : sig
  type t
  val is_empty : t -> bool
  val push : int * party -> t -> unit
  val pop : t -> int * party
  val create : unit -> t
end = struct
  type t = (int * party) list ref
  let create () = ref []
  let is_empty q = !q = []
  let rec split acc = function
    | [] -> List.rev acc, []
    | (_, { priority = Low }) :: _ as l -> List.rev acc, l
    | x :: xs -> split (x :: acc) xs
  let push (_,{ priority } as item) q =
    if priority = Low then q := !q @ [item]
    else
      let high, low = split [] !q in
      q := high @ (item :: low)
  let pop q = match !q with x :: xs -> q := xs; x | _ -> assert false
end

let read_fd fd s ~off ~len =
  let rec loop () =
    try Unix.read fd s off len
    with Unix.Unix_error(Unix.EAGAIN,_,_) -> loop ()
  in 
    loop ()

let really_read_fd fd s off len =
  let i = ref 0 in
  while !i < len do
    let off = off + !i in
    let len = len - !i in
    let r = read_fd fd s ~off ~len in
    if r = 0 then raise End_of_file;
    i := !i + r
  done

let raw_input_line fd =
  try
    let b = Buffer.create 80 in
    let s = Bytes.make 1 '\000' in
    let endl = Bytes.of_string "\n" in
    let endr = Bytes.of_string "\r" in
    while Bytes.compare s endl <> 0 do
      really_read_fd fd s 0 1;
      if Bytes.compare s endl <> 0 && Bytes.compare s endr <> 0
      then Buffer.add_bytes b s;
    done;
    Buffer.contents b
  with Unix.Unix_error _ -> raise End_of_file

let accept s =
  let cs, _ = Unix.accept s in
  let cout = Unix.out_channel_of_descr cs in
  set_binary_mode_out cout true;
  match parse_request (raw_input_line cs) with
  | Hello p -> { sock=cs; cout; tokens=0; priority=p }
  | _ -> (try Unix.close cs with _ -> ()); raise End_of_file

let parse s = ()

let parties = ref []

let max_tokens = ref 2
let cur_tokens = ref 0

let queue = Queue.create ()

let rec allocate n party =
  let extra = min n (!max_tokens - !cur_tokens) in
  cur_tokens := !cur_tokens + extra;
  party.tokens <- party.tokens + extra;
  answer party (Tokens extra)

and de_allocate n party =
  let back = min party.tokens n in
  party.tokens <- party.tokens - back;
  cur_tokens := min (!cur_tokens - back) !max_tokens;
  eventually_dequeue ()

and eventually_dequeue () =
  if Queue.is_empty queue || !cur_tokens >= !max_tokens then ()
  else
    let req, party = Queue.pop queue in
    if List.exists (fun { sock } -> sock = party.sock) !parties
    then allocate req party
    else eventually_dequeue ()

let chat s =
  let party =
    try List.find (fun { sock } -> sock = s) !parties
    with Not_found -> Printf.eprintf "Internal error"; exit 1 in
  try
    match parse_request (raw_input_line party.sock) with
    | Get n ->
        if !cur_tokens < !max_tokens then allocate n party     
        else Queue.push (n,party) queue
    | TryGet n ->
        if !cur_tokens < !max_tokens then allocate n party     
        else answer party Noluck
    | GiveBack n -> de_allocate n party
    | Ping ->
        answer party (Pong (!cur_tokens,!max_tokens,Unix.getpid ()));
        raise End_of_file
    | Hello _ -> raise End_of_file
  with Failure _ | ParseError | Sys_error _ | End_of_file ->
    (try Unix.close party.sock with _ -> ());
    parties := List.filter (fun { sock } -> sock <> s) !parties;
    de_allocate party.tokens party;
    eventually_dequeue ()

let check_alive s =
  match CoqworkmgrApi.connect s with
  | Some s ->
      let cout = Unix.out_channel_of_descr s in
      set_binary_mode_out cout true;
      output_string cout (print_request (Hello Low)); flush cout;
      output_string cout (print_request Ping); flush cout;
      begin match Unix.select [s] [] [] 1.0 with
      | [s],_,_ ->
          let cin = Unix.in_channel_of_descr s in
          set_binary_mode_in cin true;
          begin match parse_response (input_line cin) with
          | Pong (n,m,pid) -> n, m, pid
          | _ -> raise Not_found
          end
      | _ -> raise Not_found
      end
  | _ -> raise Not_found

let main () =
  let args = [
    "-j",Arg.Set_int max_tokens, "max number of concurrent jobs";
    "-d",Arg.Set debug, "do not detach (debug)"] in
  let usage =
    "Prints on stdout an env variable assignment to be picked up by coq\n"^
    "instances in order to limit the maximum number of concurrent workers.\n"^
    "The default value is 2.\n"^
    "Usage:" in
  Arg.parse args (fun extra ->
    Arg.usage args ("Unexpected argument "^extra^".\n"^usage))
    usage;
  try
    let sock = Sys.getenv "COQWORKMGR_SOCK" in
    if !debug then Printf.eprintf "Contacting %s\n%!" sock;
    let cur, max, pid = check_alive sock in
    Printf.printf "COQWORKMGR_SOCK=%s\n%!" sock;
    Printf.eprintf
      "coqworkmgr already up and running (pid=%d, socket=%s, j=%d/%d)\n%!"
      pid sock cur max;
    exit 0
  with Not_found | Failure _ | Invalid_argument _ | Unix.Unix_error _ ->
  if !debug then Printf.eprintf "No running instance. Starting a new one\n%!";
  let master, str = mk_socket_channel () in
  if not !debug then begin
    let pid = Unix.fork () in
    if pid <> 0 then begin
      Printf.printf "COQWORKMGR_SOCK=%s\n%!" str;
      exit 0 
    end else begin
      ignore(Unix.setsid ());
      Unix.close Unix.stdin;
      Unix.close Unix.stdout;
    end;
  end else begin
    Printf.printf "COQWORKMGR_SOCK=%s\n%!" str;
  end;
  Sys.catch_break true;
  try
    while true do
      if !debug then
        Printf.eprintf "Status: #parties=%d tokens=%d/%d \n%!"
          (List.length !parties) !cur_tokens !max_tokens;
      let socks = master :: List.map (fun { sock } -> sock) !parties in
      let r, _, _ = Unix.select socks [] [] (-1.0) in
      List.iter (fun s ->
        if s = master then begin
          try parties := accept master :: !parties
          with _ -> ()
        end else chat s)
      r
    done;
    exit 0
  with Sys.Break ->
    if !parties <> [] then begin
      Printf.eprintf "Some coq processes still need me\n%!";
      exit 1;
    end else
      exit 0

let () = main ()
