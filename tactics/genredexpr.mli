(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Reduction expressions *)

(** The parsing produces initially a list of [red_atom] *)

type 'a red_atom =
  | FBeta
  | FMatch
  | FFix
  | FCofix
  | FZeta
  | FConst of 'a list
  | FDeltaBut of 'a list
  | FHead

(** This list of atoms is immediately converted to a [glob_red_flag] *)

type strength = Norm | Head
(* someday we may add NotUnderBinders *)

type 'a glob_red_flag = {
  rStrength : strength;
  rBeta : bool;
  rMatch : bool;
  rFix : bool;
  rCofix : bool;
  rZeta : bool;
  rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

(** Generic kinds of reductions *)

type ('b,'c,'occvar) red_context = ('occvar Locus.occurrences_gen * ('b,'c) Util.union) option

type ('a, 'b, 'c, 'occvar, 'flags) red_expr_gen0 =
  | Red
  | Hnf
  | Simpl of 'flags * ('b, 'c, 'occvar) red_context
  | Cbv of 'flags
  | Cbn of 'flags
  | Lazy of 'flags
  | Unfold of ('occvar Locus.occurrences_gen * 'b) list
  | Fold of 'a list
  | Pattern of ('occvar Locus.occurrences_gen * 'a) list
  | ExtraRedExpr of string
  | CbvVm of ('b, 'c, 'occvar) red_context
  | CbvNative of ('b, 'c, 'occvar) red_context

type ('a, 'b, 'c, 'occvar) red_expr_gen =
  ('a, 'b, 'c, 'occvar, 'b glob_red_flag) red_expr_gen0

type ('a,'b,'c,'occvar) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a,'b,'c,'occvar) red_expr_gen * 'a
  | ConstrContext of Names.lident * 'a
  | ConstrTypeOf of 'a

open Constrexpr

type r_trm = constr_expr
type r_pat = constr_pattern_expr
type r_cst = Libnames.qualid or_by_notation

type raw_red_expr = (r_trm, r_cst, r_pat, int Locus.or_var) red_expr_gen

type 'a and_short_name = 'a * Names.lident option

type g_trm = Genintern.glob_constr_and_expr
type g_pat = Genintern.glob_constr_pattern_and_expr
type g_cst = Evaluable.t and_short_name Locus.or_var

type glob_red_expr = (g_trm, g_cst, g_trm, int Locus.or_var) red_expr_gen
