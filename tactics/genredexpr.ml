(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

type ('a, 'b, 'c, 'flags) red_expr_gen0 =
  | Red of bool
  | Hnf
  | Simpl of 'flags * ('b, 'c) Util.union Locus.with_occurrences option
  | Cbv of 'flags
  | Cbn of 'flags
  | Lazy of 'flags
  | Unfold of 'b Locus.with_occurrences list
  | Fold of 'a list
  | Pattern of 'a Locus.with_occurrences list
  | ExtraRedExpr of string
  | CbvVm of ('b,'c) Util.union Locus.with_occurrences option
  | CbvNative of ('b,'c) Util.union Locus.with_occurrences option

type ('a, 'b, 'c) red_expr_gen =
  ('a, 'b, 'c, 'b glob_red_flag) red_expr_gen0

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

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

type 'a and_short_name = 'a * Names.lident option

let wit_red_expr :
  ((constr_expr,qualid or_by_notation,constr_expr) red_expr_gen,
   (Genintern.glob_constr_and_expr,Tacred.evaluable_global_reference and_short_name Locus.or_var,Genintern.glob_constr_pattern_and_expr) red_expr_gen,
   (EConstr.t,Tacred.evaluable_global_reference,Pattern.constr_pattern) red_expr_gen)
    Genarg.genarg_type =
  make0 "redexpr"
