(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(** This list of atoms is immediately converted to a [glob_red_flag] *)

type 'a glob_red_flag = {
  rBeta : bool;
  rMatch : bool;
  rFix : bool;
  rCofix : bool;
  rZeta : bool;
  rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

(** Generic kinds of reductions *)

type ('a,'b,'c) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl of 'b glob_red_flag*('b,'c) Util.union Locus.with_occurrences option
  | Cbv of 'b glob_red_flag
  | Cbn of 'b glob_red_flag
  | Lazy of 'b glob_red_flag
  | Unfold of 'b Locus.with_occurrences list
  | Fold of 'a list
  | Pattern of 'a Locus.with_occurrences list
  | ExtraRedExpr of string
  | CbvVm of ('b,'c) Util.union Locus.with_occurrences option
  | CbvNative of ('b,'c) Util.union Locus.with_occurrences option

type ('a,'b,'c) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a,'b,'c) red_expr_gen * 'a
  | ConstrContext of Names.lident * 'a
  | ConstrTypeOf of 'a

open Libnames
open Constrexpr

type r_trm = constr_expr
type r_pat = constr_pattern_expr
type r_cst = qualid or_by_notation

type raw_red_expr = (r_trm, r_cst, r_pat) red_expr_gen
