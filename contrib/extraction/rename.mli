
(* Renaming issues. *)

open Names
open Term
open Miniml

type renaming_function = Idset.t -> name -> identifier

module type Renaming = sig
  val rename_type_parameter : renaming_function
  val rename_type : renaming_function
  val rename_term : renaming_function
  val rename_global_type : renaming_function
  val rename_global_constructor : renaming_function
  val rename_global_term : renaming_function
end

module Make : functor(R : Renaming) -> sig

end
