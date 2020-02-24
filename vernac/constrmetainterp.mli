(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

exception CannotCoerceTo of string

val error_metalanguage_variable :
  string ->
  ?loc:Loc.t ->
  Names.Id.t ->
  (Environ.env * Evd.evar_map) option -> Geninterp.Val.t -> string -> 'a

val try_interp_metalanguage_var :
  string ->
  (Geninterp.Val.t -> 'a) ->
  Geninterp.interp_sign ->
  (Environ.env * Evd.evar_map) option -> Names.Id.Map.key CAst.t -> 'a

module type ConstrCoercionSig =
  sig
    val trace :
      (Environ.env ->
       Evd.evar_map ->
       Ltac_pretype.ltac_var_map ->
       Glob_term.glob_constr -> Evd.evar_map * EConstr.constr) ->
      Geninterp.interp_sign ->
      Environ.env ->
      Evd.evar_map ->
      Ltac_pretype.ltac_var_map ->
      Glob_term.glob_constr -> Evd.evar_map * EConstr.constr
    val coerce_to_uconstr :
      Geninterp.Val.t -> Ltac_pretype.closed_glob_constr
    val coerce_to_constr :
      Environ.env -> Geninterp.Val.t -> Ltac_pretype.constr_under_binders
    val coerce_to_constr_list :
      Environ.env -> Geninterp.Val.t -> EConstr.constr list
    val coerce_var_to_ident :
      bool -> Environ.env -> Evd.evar_map -> Geninterp.Val.t -> Names.Id.t
    val name : string
  end

module Make :
  functor (M : ConstrCoercionSig) ->
    sig
      val interp_glob_closure :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        ?kind:Pretyping.typing_constraint ->
        ?pattern_mode:bool ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Ltac_pretype.closed_glob_constr
      val interp_gen :
        Pretyping.typing_constraint ->
        Geninterp.interp_sign ->
        bool ->
        Pretyping.inference_flags ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val constr_flags : unit -> Pretyping.inference_flags
      val interp_constr_gen :
        Pretyping.typing_constraint ->
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val interp_constr :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val interp_type :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val open_constr_use_classes_flags : unit -> Pretyping.inference_flags
      val open_constr_no_classes_flags : unit -> Pretyping.inference_flags
      val pure_open_constr_flags : Pretyping.inference_flags
      val interp_open_constr :
        ?expected_type:Pretyping.typing_constraint ->
        ?flags:Pretyping.inference_flags ->
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val interp_open_constr_with_classes :
        ?expected_type:Pretyping.typing_constraint ->
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val interp_pure_open_constr :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        Glob_term.glob_constr * Constrexpr.constr_expr option ->
        Evd.evar_map * EConstr.constr
      val interp_typed_pattern :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        'a * (Glob_term.glob_constr * Constrexpr.constr_expr option) * 'b ->
        Pattern.constr_pattern
      val interp_in_compound_list :
        ('a -> ('b Glob_term.glob_constr_r, 'c) DAst.t * 'd) ->
        ('e -> Geninterp.Val.t -> 'f list) ->
        (Geninterp.interp_sign -> 'e -> 'g -> 'a -> 'g * 'f) ->
        Geninterp.interp_sign -> 'e -> 'g -> 'a list -> 'g * 'f list
      val interp_constr_list :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        (([ `any ] Glob_term.glob_constr_r, [ `any ]) DAst.t *
         Constrexpr.constr_expr option)
        list -> Evd.evar_map * EConstr.constr list
      val interp_open_constr_list :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        (([ `any ] Glob_term.glob_constr_r, [ `any ]) DAst.t *
         Constrexpr.constr_expr option)
        list -> Evd.evar_map * EConstr.constr list
    end
