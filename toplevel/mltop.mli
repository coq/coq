(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* If there is a toplevel under Coq, it is described by the following 
   record. *)
type toplevel = { 
  load_obj : string -> unit;
  use_file : string -> unit;
  add_dir  : string -> unit;
  ml_loop  : unit -> unit }

(* Determines the behaviour of Coq with respect to ML files (compiled 
   or not) *) 
type kind_load=
  | WithTop of toplevel
  | WithoutTop
  | Native

(*Sets and initializes the kind of loading*)
val set : kind_load -> unit
val get : unit -> kind_load

(*Resets the kind of loading*)
val remove : unit -> unit

(*Tests if an Ocaml toplevel runs under Coq*)
val is_ocaml_top : unit -> bool

(*Tests if we can load ML files*)
val enable_load : unit -> bool

(*Starts the Ocaml toplevel loop *)
val ocaml_toploop : unit -> unit

(*Dynamic loading of .cmo*)
val dir_ml_load : string -> unit

(*Dynamic interpretation of .ml*)
val dir_ml_use : string -> unit

(*Adds a path to the ML paths*)
val add_ml_dir : string -> unit
val add_rec_ml_dir : string -> unit

(*Adds a path to the Coq and ML paths*)
val add_path : (*unix_path:*)string -> (*coq_root:*)Names.dir_path -> unit
val add_rec_path : (*unix_path:*)string -> (*coq_root:*)Names.dir_path -> unit

val add_init_with_state : (unit -> unit) -> unit
val init_with_state : unit -> unit

(* List of modules linked to the toplevel *)
val add_known_module : string -> unit
val module_is_known : string -> bool
val load_object : string -> string -> unit

(* Summary of Declared ML Modules *)
val get_loaded_modules : unit -> string list
val add_loaded_module : string -> unit
val init_ml_modules : unit -> unit
val unfreeze_ml_modules : string list -> unit

type ml_module_object = { mnames: string list }
val inMLModule : ml_module_object -> Libobject.obj
val outMLModule : Libobject.obj -> ml_module_object

val declare_ml_modules : string list -> unit
val print_ml_path : unit -> unit

val print_ml_modules : unit -> unit
