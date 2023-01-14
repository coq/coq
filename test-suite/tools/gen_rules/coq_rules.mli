(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

val vfile_header :
  dir:string -> ?name:string -> string -> String.t list

module Compilation : sig

  module Kind : sig
    type t =
    | Vo
    | Vos
    | Vok
    | Vio
    | Vio2vo
    | Coqtop
    | Coqchk
    | Native
  end

  module Output : sig
    type t =
    | None
    | MainJob
    | MainJobWithExit
    | MainJobModTime
  end

end

val check_dir :
  out:Format.formatter ->
  cctx:(string -> String.t list) ->
  ?ignore:string list ->
  ?copy_csdp_cache:string ->
  ?args:String.t list ->
  ?base_deps:string list ->
  ?deps:(string -> string list) ->
  ?envs:(string * string) list ->
  ?exit_codes:int list ->
  ?output:Compilation.Output.t ->
  ?kind:Compilation.Kind.t ->
  dir:string ->
  unit -> unit
