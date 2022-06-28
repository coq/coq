(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

type t = A of string | Path of Path.t

(** Similar to [Path.adjust] , noop for [A] case *)
val adjust : lvl:int -> t -> t

val to_string : t -> string

module List : sig
  val to_string : t list -> string
end
