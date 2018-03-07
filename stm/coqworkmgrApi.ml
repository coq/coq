(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let debug = false

type priority = Low | High

(* Default priority *)
let async_proofs_worker_priority = ref Low

let string_of_priority = function Low -> "low" | High -> "high"
let priority_of_string = function
  | "low" -> Low
  | "high" -> High
  | _ -> raise (Invalid_argument "priority_of_string")

type request =
  | Hello of priority
  | Get of int
  | TryGet of int
  | GiveBack of int
  | Ping

type response =
  | Tokens of int
  | Noluck
  | Pong of int * int * int

exception ParseError

(* make it work with telnet: strip trailing \r  *)
let strip_r s =
  let len = String.length s in
  if s.[len - 1] <> '\r' then s else String.sub s 0 (len - 1)

let positive_int_of_string n =
  try
    let n = int_of_string n in
    if n <= 0 then raise ParseError else n
  with Invalid_argument _ | Failure _ -> raise ParseError

let parse_request s =
  if debug then Printf.eprintf "parsing '%s'\n" s;
  match Str.split (Str.regexp " ") (strip_r s) with
  | [ "HELLO"; "LOW" ] -> Hello Low
  | [ "HELLO"; "HIGH" ] -> Hello High
  | [ "GET"; n ] -> Get (positive_int_of_string n)
  | [ "TRYGET"; n ] -> TryGet (positive_int_of_string n)
  | [ "GIVEBACK"; n ] -> GiveBack (positive_int_of_string n)
  | [ "PING" ] -> Ping
  | _ -> raise ParseError

let parse_response s =
  if debug then Printf.eprintf "parsing '%s'\n" s;
  match Str.split (Str.regexp " ") (strip_r s) with
  | [ "TOKENS"; n ] -> Tokens (positive_int_of_string n)
  | [ "NOLUCK" ] -> Noluck
  | [ "PONG"; n; m; p ] ->
      let n = try int_of_string n with _ -> raise ParseError in
      let m = try int_of_string m with _ -> raise ParseError in
      let p = try int_of_string p with _ -> raise ParseError in
      Pong (n,m,p)
  | _ -> raise ParseError
       
let print_request = function
  | Hello Low -> "HELLO LOW\n"
  | Hello High -> "HELLO HIGH\n"
  | Get n -> Printf.sprintf "GET %d\n" n
  | TryGet n -> Printf.sprintf "TRYGET %d\n" n
  | GiveBack n -> Printf.sprintf "GIVEBACK %d\n" n
  | Ping -> "PING\n"

let print_response = function
  | Tokens n -> Printf.sprintf "TOKENS %d\n" n
  | Noluck -> "NOLUCK\n"
  | Pong (n,m,p) -> Printf.sprintf "PONG %d %d %d\n" n m p

let connect s =
  try
    match Str.split (Str.regexp ":") s with
    | [ h; p ] ->
        let open Unix in
        let s = socket PF_INET SOCK_STREAM 0 in
        connect s (ADDR_INET (inet_addr_of_string h,int_of_string p));
        Some s
    | _ -> None
  with Unix.Unix_error _ -> None

let manager = ref None

let option_map f = function None -> None | Some x -> Some (f x)

let init p =
  try
    let sock = Sys.getenv "COQWORKMGR_SOCK" in
    manager := option_map (fun s -> 
      let cout = Unix.out_channel_of_descr s in
      set_binary_mode_out cout true;
      let cin = Unix.in_channel_of_descr s in
      set_binary_mode_in cin true;
      output_string cout (print_request (Hello p)); flush cout;
      cin, cout) (connect sock)
  with Not_found | End_of_file -> ()

let with_manager f g =
  try
    match !manager with
    | None -> f ()
    | Some (cin, cout) -> g cin cout
  with
  | ParseError | End_of_file -> manager := None; f ()

let get n =
  with_manager
  (fun () -> n)
  (fun cin cout ->
    output_string cout (print_request (Get n));
    flush cout;
    let l = input_line cin in
    match parse_response l with
    | Tokens m -> m
    | _ -> raise (Failure "coqworkmgr protocol error"))

let tryget n =
  with_manager
  (fun () -> Some n)
  (fun cin cout ->
    output_string cout (print_request (TryGet n));
    flush cout;
    let l = input_line cin in
    match parse_response l with
    | Tokens m -> Some m
    | Noluck -> None
    | _ -> raise (Failure "coqworkmgr protocol error"))

let giveback n =
  with_manager
  (fun () -> ())
  (fun cin cout ->
    output_string cout (print_request (GiveBack n));
    flush cout)

