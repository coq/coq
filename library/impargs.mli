
(* $Id$ *)

(*i*)
open Names
(*i*)

(* Implicit arguments. Here we store the implicit arguments. Notice that we 
   are outside the kernel, which knows nothing about implicit arguments. *)

type implicits =
  | Impl_auto of int list
  | Impl_manual of int list
  | No_impl

val implicit_args : bool ref

val declare_constant_implicits : section_path -> unit
val declare_constant_manual_implicits : section_path -> int list -> unit
val constant_implicits : section_path -> implicits

val declare_inductive_implicits : section_path -> unit
val inductive_implicits : section_path * int -> implicits
val constructor_implicits : (section_path * int) * int -> implicits


