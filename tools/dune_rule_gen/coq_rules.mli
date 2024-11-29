(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(* (c) MINES ParisTech 2018-2019                                        *)
(* (c) INRIA 2020-2022                                                  *)
(* Written by: Emilio Jesús Gallego Arias                               *)
(* Written by: Rudi Grinberg                                            *)
(************************************************************************)

module Theory : sig
  (** A theory binding; directories should be relative to Coq's
      sources root *)
  type t =
    { directory : Path.t
    (** Directory of the theory *)
    ; dirname: string list
    (** Coq's logical path *)
    ; implicit : bool
    (** Use -R or -Q *)
    ; deps : string list
    (** Adds as -Q user-contrib/X X *)
    }
end

(** theory kind *)
module Boot_type : sig

  type t =
      Corelib
    (** Standard library *)
    | NoInit
    (** Standalone library (without Coq's core lib, for example the prelude) *)
    | Regular of Theory.t
    (** Regular library, qualified with -Q, path controls where the
        Coq init is *)

end

module Context : sig
  type t

  (** *)
  val make :
    root_lvl:int
    -> theory:Theory.t
    -> user_flags:Arg.t list
    -> boot:Boot_type.t
    -> rule:Coq_module.Rule_type.t (* quick, native, etc... *)
    -> async:bool
    -> dir_info:Coq_module.t Dir_info.t (* contents of the directory scan *)
    -> split:bool (* whether we are building rocq-runtime + rocq-core or only rocq-core *)
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
