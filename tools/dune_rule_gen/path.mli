(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

type t

(** [make path] build a path from a string *)
val make : string -> t

(** [relative path s] append [s] to [path] to build [path/s] *)
val relative : t -> string -> t

(** [basename path] returns the basename *)
val basename : t -> string

(** [adjust ~lvl path] adjusts a path to refer to [lvl] lower
   directories, that is to say [adjust ~lvl:2 p] will do [../../p] *)
val adjust : lvl:int -> t -> t

(** [add_extension ext p] builds [p^ext] *)
val add_extension : ext:string -> t -> t

val replace_ext : ext:string -> t -> t

val to_string : t -> string

val compare : t -> t -> int
val pp : Format.formatter -> t -> unit

(* Hack for coqdep, see comments in the implementation *)
val coqdep_fixup_dir : t -> t
