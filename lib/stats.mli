[@@@ocaml.warning "-33"]
open Loc
[@@@ocaml.warning "+33"]

val parser_action : string -> int -> string -> int -> int -> unit

val lookahead : string -> string -> int -> int -> unit

(*
type list_type =
  [ SList1
  | SList1Sep
  | SList0
  | Slist0Sep
  | Opt
  ]
*)

val got_list :  string -> int -> string -> unit

val got_token : string -> unit

val got_loc : Loc.t -> string -> unit

val check_stack : string -> unit

type ptree =
[ `Token of string * Loc.t option
(* `Prod: printed prodn name, (file, line, char in line) of prodn definition *)
| `Prod of string * (string * int * int) * ptree list
]

val get_stack : unit -> ptree list

val set_stack : ptree list -> unit

val set_ename : string -> unit

val start_Parse_cmd : unit -> bool

val end_Parse_cmd : bool -> unit

val print : bool ref  (* todo: remove *)

val enable : bool ref

val cnt : int ref
