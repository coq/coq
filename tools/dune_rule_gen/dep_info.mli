(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

type t

(** [make ~cctx:args ~base_dir ~dir_info] compute dependency
   information for Coq modules in [dir_info] *)
val make : args:Arg.t list -> dir_info:Coq_module.t Dir_info.t -> t

(** [lookup di filename] return deps of filename *)
val lookup : dep_info:t -> Path.t -> Coqdeplib.Dep_info.Dep.t list
