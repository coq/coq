
(*i*)
open Pp
open Names
open Term
open Environ
(*i*)

val term : constr Grammar.Entry.e

type command =
  | Definition of identifier * constr option * constr
  | Parameter of identifier * constr
  | Variable of identifier * constr
  | Inductive of 
      (identifier * constr) list *
      (identifier * constr * (identifier * constr) list) list
  | Check of constr

val command : command Grammar.Entry.e

val pr_term : path_kind -> env -> constr -> std_ppcmds
