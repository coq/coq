
(* $Id$ *)

(*i*)
open Names
open Term
open Environ
(*i*)

val dbize_op : 
  Coqast.loc -> string -> Coqast.t list -> pseudo_constr list -> pseudo_constr
val dbize    : unit assumptions -> Coqast.t -> pseudo_constr

val absolutize_cci : unsafe_env -> pseudo_constr -> pseudo_constr
val dbize_cci      : unsafe_env -> Coqast.t -> pseudo_constr
val absolutize_fw  : unsafe_env -> pseudo_constr -> pseudo_constr
val dbize_fw       : unsafe_env -> Coqast.t -> pseudo_constr

val raw_pseudo_constr_of_com : unsafe_env -> Coqast.t -> pseudo_constr
val raw_fpseudo_constr_of_com : unsafe_env -> Coqast.t -> pseudo_constr
val raw_pseudo_constr_of_compattern : unsafe_env -> Coqast.t -> pseudo_constr

val globalize_command : Coqast.t -> Coqast.t
val globalize_ast     : Coqast.t -> Coqast.t
