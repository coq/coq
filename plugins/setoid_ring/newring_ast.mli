(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Libnames
open Constrexpr

open Ltac_plugin
open Tacexpr

type 'constr coeff_spec =
    Computational of 'constr (* equality test *)
  | Abstract (* coeffs = Z *)
  | Morphism of 'constr (* general morphism *)

type cst_tac_spec =
    CstTac of raw_tactic_expr
  | Closed of qualid list

type 'constr ring_mod =
    Ring_kind of 'constr coeff_spec
  | Const_tac of cst_tac_spec
  | Pre_tac of raw_tactic_expr
  | Post_tac of raw_tactic_expr
  | Setoid of constr_expr * constr_expr
  | Pow_spec of cst_tac_spec * constr_expr
           (* Syntaxification tactic , correctness lemma *)
  | Sign_spec of constr_expr
  | Div_spec of constr_expr

type 'constr field_mod =
    Ring_mod of 'constr ring_mod
  | Inject of constr_expr

type ring_info =
    { ring_carrier : types;
      ring_req : constr;
      ring_setoid : constr;
      ring_ext : constr;
      ring_morph : constr;
      ring_th : constr;
      ring_cst_tac : glob_tactic_expr;
      ring_pow_tac : glob_tactic_expr;
      ring_lemma1 : constr;
      ring_lemma2 : constr;
      ring_pre_tac : glob_tactic_expr;
      ring_post_tac : glob_tactic_expr }

type field_info =
    { field_carrier : types;
      field_req : constr;
      field_cst_tac : glob_tactic_expr;
      field_pow_tac : glob_tactic_expr;
      field_ok : constr;
      field_simpl_eq_ok : constr;
      field_simpl_ok : constr;
      field_simpl_eq_in_ok : constr;
      field_cond : constr;
      field_pre_tac : glob_tactic_expr;
      field_post_tac : glob_tactic_expr }
