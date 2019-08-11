[@@@ocaml.warning "-33"]
open Loc
[@@@ocaml.warning "+33"]

val parser_action : string -> int -> string -> int -> unit

val lookahead : string -> string -> int -> unit

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

val check_stack : unit -> unit

type ptree =
[ `Token of string
| `Prod of string * ptree list
]

val get_stack : unit -> ptree list

val set_stack : ptree list -> unit

val print : bool ref

val enable : bool ref

val cnt : int ref
