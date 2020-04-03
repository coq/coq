(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type RedExprCoercionSig =
  sig
    module N : Constrmetainterp.ConstrCoercionSig
    val coerce_to_evaluable_ref :
      Environ.env ->
      Evd.evar_map -> Geninterp.Val.t -> Names.evaluable_global_reference
    val coerce_to_closed_constr :
      Environ.env -> Geninterp.Val.t -> EConstr.constr
    val coerce_to_int_or_var_list : Geninterp.Val.t -> int Locus.or_var list
    val coerce_to_int : Geninterp.Val.t -> int
  end
module Make :
  functor (M : RedExprCoercionSig) ->
    sig
      val interp_int :
        Geninterp.interp_sign -> Names.Id.Map.key CAst.t -> int
      val interp_int_or_var :
        Geninterp.interp_sign -> int Locus.or_var -> int
      val interp_int_or_var_as_list :
        Geninterp.interp_sign -> int Locus.or_var -> int Locus.or_var list
      val interp_int_or_var_list :
        Geninterp.interp_sign ->
        int Locus.or_var list -> int Locus.or_var list
      val interp_occurrences :
        Geninterp.interp_sign ->
        int Locus.or_var Locus.occurrences_gen ->
        int Locus.or_var Locus.occurrences_gen
      val interp_constr_with_occurrences :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        int Locus.or_var Locus.occurrences_gen *
        (Glob_term.glob_constr * Constrexpr.constr_expr option) ->
        Evd.evar_map *
        (int Locus.or_var Locus.occurrences_gen * EConstr.constr)
      val interp_red_expr :
        Geninterp.interp_sign ->
        Environ.env ->
        Evd.evar_map ->
        (([ `any ] Glob_term.glob_constr_r, [ `any ]) DAst.t *
         Constrexpr.constr_expr option,
         (Names.evaluable_global_reference * Names.variable CAst.t option)
         Locus.or_var,
         'a * (Glob_term.glob_constr * Constrexpr.constr_expr option) * 'b)
        Genredexpr.red_expr_gen ->
        Evd.evar_map *
        (EConstr.constr, Names.evaluable_global_reference,
         Pattern.constr_pattern)
        Genredexpr.red_expr_gen
    end
