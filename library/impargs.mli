
(* $Id$ *)

(*i*)
open Names
open Term
open Inductive
(*i*)

(*s Implicit arguments. Here we store the implicit arguments. Notice that we 
    are outside the kernel, which knows nothing about implicit arguments. *)

type implicits =
  | Impl_auto of int list
  | Impl_manual of int list
  | No_impl

val make_implicit_args : bool -> unit
val is_implicit_args : unit -> bool
val implicitely : ('a -> 'b) -> 'a -> 'b
val with_implicits : bool -> ('a -> 'b) -> 'a -> 'b

val list_of_implicits : implicits -> int list

(*s Computation of implicits (done using the global environment). *)

val declare_var_implicits : section_path -> unit
val declare_constant_implicits : section_path -> unit
val declare_inductive_implicits : section_path -> unit

(*s Access to already computed implicits. *)

val constant_implicits : section_path -> implicits
val inductive_implicits : inductive_path -> implicits
val constructor_implicits : constructor_path -> implicits

val constructor_implicits_list : constructor_path -> int list
val inductive_implicits_list : inductive_path -> int list
val constant_implicits_list : section_path -> int list

val implicits_of_var : section_path -> int list

val is_implicit_constant : section_path -> bool
val is_implicit_inductive_definition : section_path -> bool
val is_implicit_var : section_path -> bool

val implicits_of_global : global_reference -> int list

(*s Rollback. *)

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
