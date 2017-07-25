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

open Kernel_API
open Intf_API
open Engine_API
open Library_API
open Pretyping_API

(************************************************************************)
(* Modules from interp/                                                 *)
(************************************************************************)

module Genintern :
sig
  open Genarg

  module Store : Store.S

  type glob_sign = {
    ltacvars : Names.Id.Set.t;
    genv : Environ.env;
    extra : Store.t;
  }

  val empty_glob_sign : Environ.env -> glob_sign

  type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb


  val generic_intern : (raw_generic_argument, glob_generic_argument) intern_fun

  type 'glb subst_fun = Mod_subst.substitution -> 'glb -> 'glb
  val generic_substitute : Genarg.glob_generic_argument subst_fun

  type 'glb ntn_subst_fun = Tactypes.glob_constr_and_expr Names.Id.Map.t -> 'glb -> 'glb

  val register_intern0 : ('raw, 'glb, 'top) genarg_type ->
    ('raw, 'glb) intern_fun -> unit

  val register_subst0 : ('raw, 'glb, 'top) genarg_type ->
    'glb subst_fun -> unit

  val register_ntn_subst0 : ('raw, 'glb, 'top) genarg_type ->
    'glb ntn_subst_fun -> unit

end

module Stdarg :
sig
  val loc_of_or_by_notation : ('a -> Loc.t option) -> 'a Misctypes.or_by_notation -> Loc.t option
  val wit_unit : unit Genarg.uniform_genarg_type
  val wit_int : int Genarg.uniform_genarg_type
  val wit_var : (Names.Id.t Loc.located, Names.Id.t Loc.located, Names.Id.t) Genarg.genarg_type
  val wit_bool : bool Genarg.uniform_genarg_type
  val wit_string : string Genarg.uniform_genarg_type
  val wit_pre_ident : string Genarg.uniform_genarg_type
  val wit_global : (Libnames.reference, Globnames.global_reference Loc.located Misctypes.or_var, Globnames.global_reference) Genarg.genarg_type
  val wit_ident : Names.Id.t Genarg.uniform_genarg_type
  val wit_integer : int Genarg.uniform_genarg_type
  val wit_constr : (Constrexpr.constr_expr, Tactypes.glob_constr_and_expr, EConstr.constr) Genarg.genarg_type
  val wit_open_constr : (Constrexpr.constr_expr, Tactypes.glob_constr_and_expr, EConstr.constr) Genarg.genarg_type
  val wit_intro_pattern : (Constrexpr.constr_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.glob_constr_and_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.intro_pattern) Genarg.genarg_type
  val wit_int_or_var : (int Misctypes.or_var, int Misctypes.or_var, int) Genarg.genarg_type
  val wit_ref : (Libnames.reference, Globnames.global_reference Loc.located Misctypes.or_var, Globnames.global_reference) Genarg.genarg_type
  val wit_clause_dft_concl :  (Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) Genarg.genarg_type
  val wit_uconstr : (Constrexpr.constr_expr , Tactypes.glob_constr_and_expr, Glob_term.closed_glob_constr) Genarg.genarg_type
  val wit_red_expr :
    ((Constrexpr.constr_expr,Libnames.reference Misctypes.or_by_notation,Constrexpr.constr_expr) Genredexpr.red_expr_gen,
     (Tactypes.glob_constr_and_expr,Names.evaluable_global_reference Misctypes.and_short_name Misctypes.or_var,Tactypes.glob_constr_pattern_and_expr) Genredexpr.red_expr_gen,
     (EConstr.constr,Names.evaluable_global_reference,Pattern.constr_pattern) Genredexpr.red_expr_gen) Genarg.genarg_type
  val wit_quant_hyp : Misctypes.quantified_hypothesis Genarg.uniform_genarg_type
  val wit_bindings :
    (Constrexpr.constr_expr Misctypes.bindings,
     Tactypes.glob_constr_and_expr Misctypes.bindings,
     EConstr.constr Misctypes.bindings Tactypes.delayed_open) Genarg.genarg_type
  val wit_constr_with_bindings :
    (Constrexpr.constr_expr Misctypes.with_bindings,
     Tactypes.glob_constr_and_expr Misctypes.with_bindings,
     EConstr.constr Misctypes.with_bindings Tactypes.delayed_open) Genarg.genarg_type
  val wit_intropattern : (Constrexpr.constr_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.glob_constr_and_expr Misctypes.intro_pattern_expr Loc.located, Tactypes.intro_pattern) Genarg.genarg_type
  val wit_quantified_hypothesis : Misctypes.quantified_hypothesis Genarg.uniform_genarg_type
  val wit_clause :  (Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Loc.located Locus.clause_expr,Names.Id.t Locus.clause_expr) Genarg.genarg_type
  val wit_preident : string Genarg.uniform_genarg_type
  val wit_reference : (Libnames.reference, Globnames.global_reference Loc.located Misctypes.or_var, Globnames.global_reference) Genarg.genarg_type
  val wit_open_constr_with_bindings :
    (Constrexpr.constr_expr Misctypes.with_bindings,
     Tactypes.glob_constr_and_expr Misctypes.with_bindings,
     EConstr.constr Misctypes.with_bindings Tactypes.delayed_open) Genarg.genarg_type
end

module Constrexpr_ops :
sig
  val mkIdentC : Names.Id.t -> Constrexpr.constr_expr
  val mkAppC : Constrexpr.constr_expr * Constrexpr.constr_expr list -> Constrexpr.constr_expr
  val names_of_local_assums : Constrexpr.local_binder_expr list -> Names.Name.t Loc.located list
  val coerce_reference_to_id : Libnames.reference -> Names.Id.t
  val coerce_to_id : Constrexpr.constr_expr -> Names.Id.t Loc.located
  val constr_loc : Constrexpr.constr_expr -> Loc.t option
  val mkRefC : Libnames.reference -> Constrexpr.constr_expr
  val mkLambdaC : Names.Name.t Loc.located list * Constrexpr.binder_kind * Constrexpr.constr_expr * Constrexpr.constr_expr -> Constrexpr.constr_expr
  val default_binder_kind : Constrexpr.binder_kind
  val mkLetInC : Names.Name.t Loc.located * Constrexpr.constr_expr * Constrexpr.constr_expr option * Constrexpr.constr_expr -> Constrexpr.constr_expr
  val mkCProdN : ?loc:Loc.t -> Constrexpr.local_binder_expr list -> Constrexpr.constr_expr -> Constrexpr.constr_expr
end

module Notation_ops :
sig
  val glob_constr_of_notation_constr : ?loc:Loc.t -> Notation_term.notation_constr -> Glob_term.glob_constr
  val glob_constr_of_notation_constr_with_binders : ?loc:Loc.t ->
                                                    ('a -> Names.Name.t -> 'a * Names.Name.t) ->
                                                    ('a -> Notation_term.notation_constr -> Glob_term.glob_constr) ->
                                                    'a -> Notation_term.notation_constr -> Glob_term.glob_constr
end

module Ppextend :
sig

  type precedence = int
  type parenRelation =
    | L | E | Any | Prec of precedence
  type tolerability = precedence * parenRelation

end

module Notation :
sig
  type cases_pattern_status = bool
  type required_module = Libnames.full_path * string list
  type 'a prim_token_interpreter = ?loc:Loc.t -> 'a -> Glob_term.glob_constr
  type 'a prim_token_uninterpreter = Glob_term.glob_constr list * (Glob_term.glob_constr -> 'a option) * cases_pattern_status
  type delimiters = string
  type local_scopes = Notation_term.tmp_scope_name option * Notation_term.scope_name list
  type notation_location = (Names.DirPath.t * Names.DirPath.t) * string
  val declare_string_interpreter : Notation_term.scope_name -> required_module ->
                                   string prim_token_interpreter -> string prim_token_uninterpreter -> unit
  val declare_numeral_interpreter : Notation_term.scope_name -> required_module ->
                                    Bigint.bigint prim_token_interpreter -> Bigint.bigint prim_token_uninterpreter -> unit
  val interp_notation_as_global_reference : ?loc:Loc.t -> (Globnames.global_reference -> bool) ->
                                            Constrexpr.notation -> delimiters option -> Globnames.global_reference
  val locate_notation : (Glob_term.glob_constr -> Pp.std_ppcmds) -> Constrexpr.notation ->
                        Notation_term.scope_name option -> Pp.std_ppcmds
  val find_delimiters_scope : ?loc:Loc.t -> delimiters -> Notation_term.scope_name
  val pr_scope : (Glob_term.glob_constr -> Pp.std_ppcmds) -> Notation_term.scope_name -> Pp.std_ppcmds
  val pr_scopes : (Glob_term.glob_constr -> Pp.std_ppcmds) -> Pp.std_ppcmds
  val interp_notation : ?loc:Loc.t -> Constrexpr.notation -> local_scopes ->
                        Notation_term.interpretation * (notation_location * Notation_term.scope_name option)
  val uninterp_prim_token : Glob_term.glob_constr -> Notation_term.scope_name * Constrexpr.prim_token
end

module Dumpglob :
sig
  val add_glob : ?loc:Loc.t -> Globnames.global_reference -> unit
  val pause : unit -> unit
  val continue : unit -> unit
end

module Smartlocate :
sig
  val locate_global_with_alias : ?head:bool -> Libnames.qualid Loc.located -> Globnames.global_reference
  val global_with_alias : ?head:bool -> Libnames.reference -> Globnames.global_reference
  val global_of_extended_global : Globnames.extended_global_reference -> Globnames.global_reference
  val loc_of_smart_reference : Libnames.reference Misctypes.or_by_notation -> Loc.t option
  val smart_global : ?head:bool -> Libnames.reference Misctypes.or_by_notation -> Globnames.global_reference
end

module Topconstr :
sig
  val replace_vars_constr_expr :
  Names.Id.t Names.Id.Map.t -> Constrexpr.constr_expr -> Constrexpr.constr_expr
end

module Constrintern :
sig
  type ltac_sign = {
    ltac_vars : Names.Id.Set.t;
    ltac_bound : Names.Id.Set.t;
    ltac_extra : Genintern.Store.t;
  }

  type var_internalization_data

  type var_internalization_type =
    | Inductive of Names.Id.t list * bool
    | Recursive
    | Method
    | Variable
  type internalization_env = var_internalization_data Names.Id.Map.t

  val interp_constr_evars : Environ.env -> Evd.evar_map ref ->
                            ?impls:internalization_env -> Constrexpr.constr_expr -> EConstr.constr

  val interp_type_evars : Environ.env -> Evd.evar_map ref ->
                          ?impls:internalization_env -> Constrexpr.constr_expr -> EConstr.types

  val empty_ltac_sign : ltac_sign
  val intern_gen : Pretyping.typing_constraint -> Environ.env ->
                   ?impls:internalization_env -> ?pattern_mode:bool -> ?ltacvars:ltac_sign ->
                   Constrexpr.constr_expr -> Glob_term.glob_constr
  val intern_constr_pattern :
    Environ.env -> ?as_type:bool -> ?ltacvars:ltac_sign ->
    Constrexpr.constr_pattern_expr -> Names.Id.t list * Pattern.constr_pattern
  val intern_constr : Environ.env -> Constrexpr.constr_expr -> Glob_term.glob_constr
  val for_grammar : ('a -> 'b) -> 'a -> 'b
  val interp_reference : ltac_sign -> Libnames.reference -> Glob_term.glob_constr
  val interp_constr : Environ.env -> Evd.evar_map -> ?impls:internalization_env ->
                      Constrexpr.constr_expr -> Constr.t Evd.in_evar_universe_context
  val interp_open_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * EConstr.constr
  val locate_reference :  Libnames.qualid -> Globnames.global_reference
  val interp_type : Environ.env -> Evd.evar_map -> ?impls:internalization_env ->
                    Constrexpr.constr_expr -> Term.types Evd.in_evar_universe_context
  val interp_context_evars :
    ?global_level:bool -> ?impl_env:internalization_env -> ?shift:int ->
    Environ.env -> Evd.evar_map ref -> Constrexpr.local_binder_expr list ->
    internalization_env * ((Environ.env * EConstr.rel_context) * Impargs.manual_implicits)
  val compute_internalization_data : Environ.env -> var_internalization_type ->
                                     Term.types -> Impargs.manual_explicitation list -> var_internalization_data
  val empty_internalization_env : internalization_env
  val global_reference : Names.Id.t -> Globnames.global_reference
end

module Constrextern :
sig
  val extern_glob_constr : Names.Id.Set.t -> Glob_term.glob_constr -> Constrexpr.constr_expr
  val extern_glob_type : Names.Id.Set.t -> Glob_term.glob_constr -> Constrexpr.constr_expr
  val extern_constr : ?lax:bool -> bool -> Environ.env -> Evd.evar_map -> Constr.t -> Constrexpr.constr_expr
  val without_symbols : ('a -> 'b) -> 'a -> 'b
  val print_universes : bool ref
  val extern_type : bool -> Environ.env -> Evd.evar_map -> Term.types -> Constrexpr.constr_expr
  val with_universes : ('a -> 'b) -> 'a -> 'b
  val set_extern_reference :
    (?loc:Loc.t -> Names.Id.Set.t -> Globnames.global_reference -> Libnames.reference) -> unit
end

module Declare :
sig
  type internal_flag =
    | UserAutomaticRequest
    | InternalTacticRequest
    | UserIndividualRequest

  type constant_declaration = Safe_typing.private_constants Entries.constant_entry * Decl_kinds.logical_kind

  type section_variable_entry =
    | SectionLocalDef of Safe_typing.private_constants Entries.definition_entry
    | SectionLocalAssum of Term.types Univ.in_universe_context_set * Decl_kinds.polymorphic * bool

  type variable_declaration = Names.DirPath.t * section_variable_entry * Decl_kinds.logical_kind

  val declare_constant :
    ?internal:internal_flag -> ?local:bool -> Names.Id.t -> ?export_seff:bool -> constant_declaration -> Names.Constant.t

  val declare_universe_context : Decl_kinds.polymorphic -> Univ.ContextSet.t -> unit

  val declare_definition :
    ?internal:internal_flag -> ?opaque:bool -> ?kind:Decl_kinds.definition_object_kind ->
    ?local:bool -> ?poly:Decl_kinds.polymorphic -> Names.Id.t -> ?types:Constr.t ->
    Constr.t Univ.in_universe_context_set -> Names.Constant.t
  val definition_entry : ?fix_exn:Future.fix_exn ->
    ?opaque:bool -> ?inline:bool -> ?types:Term.types ->
    ?poly:Decl_kinds.polymorphic -> ?univs:Univ.UContext.t ->
    ?eff:Safe_typing.private_constants -> Constr.t -> Safe_typing.private_constants Entries.definition_entry
  val definition_message : Names.Id.t -> unit
  val declare_variable : Names.Id.t -> variable_declaration -> Libnames.object_name
end

(************************************************************************)
(* End of modules from interp/                                          *)
(************************************************************************)
