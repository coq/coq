(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(* (c) MINES ParisTech 2018-2019                                        *)
(* (c) INRIA 2020-2022                                                  *)
(* Written by: Emilio Jesús Gallego Arias                               *)
(* Written by: Rudi Grinberg                                            *)
(************************************************************************)

(** theory kind *)
module Boot_type : sig

  type t =
      Stdlib
    (** Standard library *)
    | NoInit
    (** Standalone library (without Coq's stdlib) *)
    | Regular of Path.t option
    (** Regular library, path controls where the Coq stdlib is *)

end

module Context : sig
  type t

  val make :
    root_lvl:int
    -> tname:string list
    -> user_flags:Arg.t list
    -> rule:Coq_module.Rule_type.t
    -> boot:Boot_type.t
    -> async:bool
    -> dir_info:Coq_module.t Dir_info.t
    -> package:string
    -> split:bool
    -> t

end

(** [gen_vo_rules root_lvl rule flags tname boot] Builds dune rules
   for the *current* directory, assuming that we will do [-R
   . tname]. The parameter [boot] controls the kind of the current
   theory. [root_lvl] tells the rule generator how many levels up the
   root Coq sources are. [flags] add extra flags to coqc, such as
   `-async on` *)
val vo_rules :
  dir_info :Coq_module.t Dir_info.t
  -> cctx:Context.t
  -> Dune_file.Rule.t list Dune_file.Subdir.t list

val coqnative_rules :
  dir_info :Coq_module.t Dir_info.t
  -> cctx:Context.t
  -> Dune_file.Rule.t list Dune_file.Subdir.t list

val install_rules :
  dir_info :Coq_module.t Dir_info.t
  -> cctx:Context.t
  -> Dune_file.Install.t list Dune_file.Subdir.t list

val vio2vo_rules :
  dir_info :Coq_module.t Dir_info.t
  -> cctx:Context.t
  -> Dune_file.Rule.t list Dune_file.Subdir.t list
