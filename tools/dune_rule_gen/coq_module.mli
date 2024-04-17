(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(* (c) MINES ParisTech 2018-2019                                        *)
(* (c) INRIA 2020-2022                                                  *)
(* Written by: Emilio Jesús Gallego Arias                               *)
(* Written by: Rudi Grinberg                                            *)
(************************************************************************)

type t

val make : source:Path.t -> prefix:string list -> name:string -> t
val source : t -> Path.t
val prefix : t -> string list

val prefix_to_dir : string list -> string

(** We support two build modes for now *)
module Rule_type : sig

  type native = Disabled | Coqc | CoqNative
  type t =
    | Regular of { native : native }

  val native_coqc : t -> bool
end

(** Return the native object files for a module *)
val native_obj_files : tname:string list -> t -> string list

(** Return the object files for a module *)
val obj_files :
  tname:string list
  -> rule:Rule_type.t
  -> t
  -> string list

(** Return pairs of object files and install locations  *)
val install_files :
  tname:string list
  -> rule:Rule_type.t
  -> t
  -> (string * string) list

val pp : Format.formatter -> t -> unit

val with_timing : bool
