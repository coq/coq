
(*i $Id$ i*)

(*i*)
open Names
open Term
open Environ
open Inductive
(*i*)

(*s Implicit arguments. Here we store the implicit arguments. Notice that we 
    are outside the kernel, which knows nothing about implicit arguments. *)

val make_implicit_args : bool -> unit
val is_implicit_args : unit -> bool
val implicitely : ('a -> 'b) -> 'a -> 'b
val with_implicits : bool -> ('a -> 'b) -> 'a -> 'b

(*s An [implicits_list] is a list of positions telling which arguments
    of a reference can be automatically infered *)
type implicits_list = int list

(* Computation of the positions of arguments automatically inferable
   for an object of the given type in the given env *)
val compute_implicits : env -> 'a Evd.evar_map -> types -> implicits_list

(*s Computation of implicits (done using the global environment). *)

val declare_var_implicits : variable_path -> unit
val declare_constant_implicits : constant_path -> unit
val declare_mib_implicits : mutual_inductive_path -> unit
val declare_implicits : global_reference -> unit

(* Manual declaration of which arguments are expected implicit *)
val declare_manual_implicits : global_reference -> implicits_list -> unit

(*s Access to already computed implicits. *)

val constructor_implicits_list : constructor_path -> implicits_list
val inductive_implicits_list : inductive_path -> implicits_list
val constant_implicits_list : constant_path -> implicits_list

val implicits_of_var : variable_path -> implicits_list

val is_implicit_constant : constant_path -> bool
val is_implicit_inductive_definition : inductive_path -> bool
val is_implicit_var : variable_path -> bool

val implicits_of_global : global_reference -> implicits_list

(*s Rollback. *)

type frozen_t
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit
