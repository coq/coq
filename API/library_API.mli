(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

(************************************************************************)
(* Modules from library/                                                *)
(************************************************************************)

module Univops :
sig
  val universes_of_constr : Term.constr -> Univ.universe_set
  val restrict_universe_context : Univ.universe_context_set -> Univ.universe_set -> Univ.universe_context_set
end

module Nameops :
sig
  val atompart_of_id : Names.Id.t -> string

  val pr_id : Names.Id.t -> Pp.std_ppcmds
  [@@ocaml.deprecated "alias of API.Names.Id.print"]

  val pr_name : Names.Name.t -> Pp.std_ppcmds
  [@@ocaml.deprecated "alias of API.Names.Name.print"]

  val name_fold : (Names.Id.t -> 'a -> 'a) -> Names.Name.t -> 'a -> 'a
  val name_app : (Names.Id.t -> Names.Id.t) -> Names.Name.t -> Names.Name.t
  val add_suffix : Names.Id.t -> string -> Names.Id.t
  val increment_subscript : Names.Id.t -> Names.Id.t
  val make_ident : string -> int option -> Names.Id.t
  val out_name : Names.Name.t -> Names.Id.t
  val pr_lab : Names.Label.t -> Pp.std_ppcmds
  module Name :
  sig
    include module type of struct include Names.Name end
    val get_id : t -> Names.Id.t
    val fold_right : (Names.Id.t -> 'a -> 'a) -> t -> 'a -> 'a
  end
end

module Libnames :
sig

  open Util
  open Names

  type full_path
  val pr_path : full_path -> Pp.std_ppcmds
  val make_path : Names.DirPath.t -> Names.Id.t -> full_path
  val eq_full_path : full_path -> full_path -> bool
  val dirpath : full_path -> Names.DirPath.t
  val path_of_string : string -> full_path

  type qualid
  val make_qualid : Names.DirPath.t -> Names.Id.t -> qualid
  val qualid_eq : qualid -> qualid -> bool
  val repr_qualid : qualid -> Names.DirPath.t * Names.Id.t
  val pr_qualid : qualid -> Pp.std_ppcmds
  val string_of_qualid : qualid -> string
  val qualid_of_string : string -> qualid
  val qualid_of_path : full_path -> qualid
  val qualid_of_dirpath : Names.DirPath.t -> qualid
  val qualid_of_ident : Names.Id.t -> qualid

  type reference =
    | Qualid of qualid Loc.located
    | Ident of Names.Id.t Loc.located
  val loc_of_reference : reference -> Loc.t option
  val qualid_of_reference : reference -> qualid Loc.located
  val pr_reference : reference -> Pp.std_ppcmds

  val is_dirpath_prefix_of : Names.DirPath.t -> Names.DirPath.t -> bool
  val split_dirpath : Names.DirPath.t -> Names.DirPath.t * Names.Id.t
  val dirpath_of_string : string -> Names.DirPath.t
  val pr_dirpath : Names.DirPath.t -> Pp.std_ppcmds

  val string_of_path : full_path -> string
  val basename : full_path -> Names.Id.t

  type object_name = full_path * Names.KerName.t
  type object_prefix = Names.DirPath.t * (Names.ModPath.t * Names.DirPath.t)

  module Dirset : Set.S with type elt = DirPath.t
  module Dirmap : Map.ExtS with type key = DirPath.t and module Set := Dirset
  module Spmap  : CSig.MapS with type key = full_path
end

module Globnames :
sig

  open Util

  type global_reference =
    | VarRef of Names.Id.t
    | ConstRef of Names.Constant.t
    | IndRef of Names.inductive
    | ConstructRef of Names.constructor

  type extended_global_reference =
                                 | TrueGlobal of global_reference
                                 | SynDef of Names.KerName.t

  (* Long term: change implementation so that only 1 kind of order is needed.
   * Today: _env ones are fine grained, which one to pick depends.  Eg.
   *   - conversion rule are implemented by the non_env ones
   *   - pretty printing (of user provided names/aliases) are implemented by
   *     the _env ones
   *)
  module Refset : CSig.SetS with type elt = global_reference
  module Refmap : Map.ExtS
    with type key = global_reference and module Set := Refset

  module Refset_env : CSig.SetS with type elt = global_reference
  module Refmap_env : Map.ExtS
    with type key = global_reference and module Set := Refset_env

  module RefOrdered :
  sig
    type t = global_reference
    val compare : t -> t -> int
  end

  val pop_global_reference : global_reference -> global_reference
  val eq_gr : global_reference -> global_reference -> bool
  val destIndRef : global_reference -> Names.inductive

  val encode_mind : Names.DirPath.t -> Names.Id.t -> Names.MutInd.t
  val encode_con : Names.DirPath.t -> Names.Id.t -> Names.Constant.t

  val global_of_constr : Constr.t -> global_reference

  val subst_global : Mod_subst.substitution -> global_reference -> global_reference * Constr.t
  val destConstructRef : global_reference -> Names.constructor

  val reference_of_constr : Constr.t -> global_reference
  [@@ocaml.deprecated "alias of API.Globnames.global_of_constr"]

  val is_global : global_reference -> Constr.t -> bool
end

module Libobject :
sig
  type obj
  type 'a substitutivity =
                         | Dispose
                           | Substitute of 'a
                         | Keep of 'a
                         | Anticipate of 'a

  type 'a object_declaration =   {
                                   object_name : string;
                                   cache_function : Libnames.object_name * 'a -> unit;
                                   load_function : int -> Libnames.object_name * 'a -> unit;
                                   open_function : int -> Libnames.object_name * 'a -> unit;
                                   classify_function : 'a -> 'a substitutivity;
                                   subst_function :  Mod_subst.substitution * 'a -> 'a;
                                   discharge_function : Libnames.object_name * 'a -> 'a option;
                                   rebuild_function : 'a -> 'a
                                 }
  val declare_object : 'a object_declaration -> ('a -> obj)
  val default_object : string -> 'a object_declaration
  val object_tag : obj -> string
end

module Summary :
sig

  type frozen
  type marshallable

  type 'a summary_declaration =
    { freeze_function : marshallable -> 'a;
      unfreeze_function : 'a -> unit;
      init_function : unit -> unit; }

  val ref : ?freeze:(marshallable -> 'a -> 'a) -> name:string -> 'a -> 'a ref
  val declare_summary : string -> 'a summary_declaration -> unit
  module Local :
  sig
    type 'a local_ref
    val ref : ?freeze:('a -> 'a) -> name:string -> 'a -> 'a local_ref
    val (:=) : 'a local_ref -> 'a -> unit
    val (!) : 'a local_ref -> 'a
  end
end

module Nametab :
sig
  exception GlobalizationError of Libnames.qualid

  type ltac_constant = Names.KerName.t

  val global : Libnames.reference -> Globnames.global_reference
  val global_of_path : Libnames.full_path -> Globnames.global_reference
  val shortest_qualid_of_global : Names.Id.Set.t -> Globnames.global_reference -> Libnames.qualid
  val path_of_global : Globnames.global_reference -> Libnames.full_path
  val locate_extended : Libnames.qualid -> Globnames.extended_global_reference
  val full_name_module : Libnames.qualid -> Names.DirPath.t
  val locate_tactic : Libnames.qualid -> Names.KerName.t
  val pr_global_env : Names.Id.Set.t -> Globnames.global_reference -> Pp.std_ppcmds
  val shortest_qualid_of_tactic : Names.KerName.t -> Libnames.qualid
  val basename_of_global : Globnames.global_reference -> Names.Id.t

  type visibility =
    | Until of int
    | Exactly of int

  val push_tactic : visibility -> Libnames.full_path -> Names.KerName.t -> unit
  val error_global_not_found : ?loc:Loc.t -> Libnames.qualid -> 'a
  val shortest_qualid_of_module : Names.ModPath.t -> Libnames.qualid
  val dirpath_of_module : Names.ModPath.t -> Names.DirPath.t
  val locate_module : Libnames.qualid -> Names.ModPath.t
  val dirpath_of_global : Globnames.global_reference -> Names.DirPath.t
  val locate : Libnames.qualid -> Globnames.global_reference
  val locate_constant : Libnames.qualid -> Names.Constant.t
end

module Global :
sig
  val env : unit -> Environ.env
  val lookup_mind : Names.MutInd.t -> Declarations.mutual_inductive_body
  val lookup_constant  : Names.Constant.t -> Declarations.constant_body
  val lookup_module    : Names.ModPath.t -> Declarations.module_body
  val lookup_modtype   : Names.ModPath.t -> Declarations.module_type_body
  val lookup_inductive : Names.inductive -> Declarations.mutual_inductive_body * Declarations.one_inductive_body
  val constant_of_delta_kn : Names.KerName.t -> Names.Constant.t
  val register :
    Retroknowledge.field -> Constr.t -> Constr.t -> unit
  val env_of_context : Environ.named_context_val -> Environ.env
  val is_polymorphic : Globnames.global_reference -> bool

  val constr_of_global_in_context : Environ.env ->
    Globnames.global_reference -> Constr.types * Univ.AUContext.t

  val type_of_global_in_context : Environ.env ->
    Globnames.global_reference -> Constr.types * Univ.AUContext.t

  val current_dirpath : unit -> Names.DirPath.t
  val body_of_constant_body : Declarations.constant_body -> (Constr.t * Univ.AUContext.t) option
  val body_of_constant : Names.Constant.t -> (Constr.t * Univ.AUContext.t) option
  val add_constraints : Univ.Constraint.t -> unit
end

module Lib : sig
  type is_type = bool
  type export = bool option
  type node =
            | Leaf of Libobject.obj (* FIX: horrible hack (wrt. Enrico) *)
            | CompilingLibrary of Libnames.object_prefix
            | OpenedModule of is_type * export * Libnames.object_prefix * Summary.frozen
            | ClosedModule  of library_segment
            | OpenedSection of Libnames.object_prefix * Summary.frozen
            | ClosedSection of library_segment

   and library_segment = (Libnames.object_name * node) list

  val current_mp : unit -> Names.ModPath.t
  val is_modtype : unit -> bool
  val is_module : unit -> bool
  val sections_are_opened : unit -> bool
  val add_anonymous_leaf : ?cache_first:bool -> Libobject.obj -> unit
  val contents : unit -> library_segment
  val cwd : unit -> Names.DirPath.t
  val add_leaf : Names.Id.t -> Libobject.obj -> Libnames.object_name
  val make_kn : Names.Id.t -> Names.KerName.t
  val make_path : Names.Id.t -> Libnames.full_path
  val discharge_con : Names.Constant.t -> Names.Constant.t
  val discharge_inductive : Names.inductive -> Names.inductive
end

module Declaremods :
sig

  val append_end_library_hook : (unit -> unit) -> unit

end

module Library :
sig
  val library_is_loaded : Names.DirPath.t -> bool
  val loaded_libraries : unit -> Names.DirPath.t list
end

module States :
sig
  val with_state_protection_on_exception : ('a -> 'b) -> 'a -> 'b
  val with_state_protection : ('a -> 'b) -> 'a -> 'b
end

module Kindops :
sig
  val logical_kind_of_goal_kind : Decl_kinds.goal_object_kind -> Decl_kinds.logical_kind
end

module Goptions :
sig
  type option_name = string list
  type 'a option_sig =
    {
      optdepr  : bool;
      optname  : string;
      optkey   : option_name;
      optread  : unit -> 'a;
      optwrite : 'a -> unit
    }

  type 'a write_function = 'a -> unit

  val declare_bool_option  : ?preprocess:(bool -> bool) ->
                             bool option_sig   -> bool write_function
  val declare_int_option   : ?preprocess:(int option -> int option) ->
                             int option option_sig -> int option write_function
  val declare_string_option: ?preprocess:(string -> string) ->
                             string option_sig -> string write_function
  val set_bool_option_value : option_name -> bool -> unit
end

module Keys :
sig
  type key
  val constr_key : ('a -> ('a, 't, 'u, 'i) Constr.kind_of_term) -> 'a -> key option
  val declare_equiv_keys : key -> key -> unit
  val pr_keys : (Globnames.global_reference -> Pp.std_ppcmds) -> Pp.std_ppcmds
end

module Coqlib :
sig

  type coq_eq_data = { eq   : Globnames.global_reference;
                       ind  : Globnames.global_reference;
                       refl : Globnames.global_reference;
                       sym  : Globnames.global_reference;
                       trans: Globnames.global_reference;
                       congr: Globnames.global_reference;
                     }

  type coq_sigma_data = {
      proj1 : Globnames.global_reference;
      proj2 : Globnames.global_reference;
      elim  : Globnames.global_reference;
      intro : Globnames.global_reference;
      typ   : Globnames.global_reference }
  val gen_reference : string -> string list -> string -> Globnames.global_reference
  val find_reference : string -> string list -> string -> Globnames.global_reference
  val check_required_library : string list -> unit
  val logic_module_name : string list
  val glob_true : Globnames.global_reference
  val glob_false : Globnames.global_reference
  val glob_O : Globnames.global_reference
  val glob_S : Globnames.global_reference
  val nat_path : Libnames.full_path
  val datatypes_module_name : string list
  val glob_eq : Globnames.global_reference
  val build_coq_eq_sym : Globnames.global_reference Util.delayed
  val build_coq_False : Globnames.global_reference Util.delayed
  val build_coq_not : Globnames.global_reference Util.delayed
  val build_coq_eq : Globnames.global_reference Util.delayed
  val build_coq_eq_data : coq_eq_data Util.delayed
  val path_of_O : Names.constructor
  val path_of_S : Names.constructor
  val build_prod : coq_sigma_data Util.delayed
  val build_coq_True : Globnames.global_reference Util.delayed
  val coq_iff_ref : Globnames.global_reference lazy_t
  val build_coq_iff_left_proj : Globnames.global_reference Util.delayed
  val build_coq_iff_right_proj : Globnames.global_reference Util.delayed
  val init_modules : string list list
  val build_coq_eq_refl  : Globnames.global_reference Util.delayed
  val arith_modules : string list list
  val zarith_base_modules : string list list
  val gen_reference_in_modules : string -> string list list-> string -> Globnames.global_reference
  val jmeq_module_name : string list
  val coq_eq_ref : Globnames.global_reference lazy_t
  val coq_not_ref : Globnames.global_reference lazy_t
  val coq_or_ref : Globnames.global_reference lazy_t
  val build_coq_and : Globnames.global_reference Util.delayed
  val build_coq_I : Globnames.global_reference Util.delayed
  val coq_reference : string -> string list -> string -> Globnames.global_reference
end

(************************************************************************)
(* End of modules from library/                                         *)
(************************************************************************)
