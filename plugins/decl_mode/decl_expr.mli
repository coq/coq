(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Tacexpr

type 'it statement =
    {st_label:Name.t;
     st_it:'it}

type thesis_kind =
    Plain
  | For of Id.t

type 'this or_thesis =
    This of 'this
  | Thesis of thesis_kind

type side = Lhs | Rhs

type elim_type =
    ET_Case_analysis
  | ET_Induction

type block_type =
    B_proof
  | B_claim
  | B_focus
  | B_elim of elim_type

type ('it,'constr,'tac) cut =
    {cut_stat: 'it;
     cut_by: 'constr list option;
     cut_using: 'tac option}

type ('var,'constr) hyp =
    Hvar of 'var
  | Hprop of 'constr statement

type ('constr,'tac) casee =
    Real of 'constr
  | Virtual of ('constr statement,'constr,'tac) cut

type ('var,'constr,'pat,'tac) bare_proof_instr =
  | Pthen of ('var,'constr,'pat,'tac) bare_proof_instr
  | Pthus of ('var,'constr,'pat,'tac) bare_proof_instr
  | Phence of ('var,'constr,'pat,'tac) bare_proof_instr
  | Pcut of ('constr or_thesis statement,'constr,'tac) cut
  | Prew of side * ('constr statement,'constr,'tac) cut
  | Psuffices of ((('var,'constr) hyp list * 'constr or_thesis),'constr,'tac) cut
  | Passume of ('var,'constr) hyp list
  | Plet of ('var,'constr) hyp list
  | Pgiven of ('var,'constr) hyp list
  | Pconsider of 'constr*('var,'constr) hyp list
  | Pclaim of 'constr statement
  | Pfocus of 'constr statement
  | Pdefine of Id.t * 'var list * 'constr
  | Pcast of Id.t or_thesis * 'constr
  | Psuppose of ('var,'constr) hyp list
  | Pcase of 'var list*'pat*(('var,'constr or_thesis) hyp list)
  | Ptake of 'constr list
  | Pper of elim_type * ('constr,'tac) casee
  | Pend of block_type
  | Pescape

type emphasis = int

type ('var,'constr,'pat,'tac) gen_proof_instr=
    {emph: emphasis;
     instr: ('var,'constr,'pat,'tac) bare_proof_instr }


type raw_proof_instr =
    ((Id.t * (Constrexpr.constr_expr option)) Loc.located,
     Constrexpr.constr_expr,
     Constrexpr.cases_pattern_expr,
     raw_tactic_expr) gen_proof_instr

type glob_proof_instr =
    ((Id.t * (Tacexpr.glob_constr_and_expr option)) Loc.located,
     Tacexpr.glob_constr_and_expr,
     Constrexpr.cases_pattern_expr,
     Tacexpr.glob_tactic_expr) gen_proof_instr

type proof_pattern =
    {pat_vars: Term.types statement list;
     pat_aliases: (Term.constr*Term.types) statement list;
     pat_constr: Term.constr;
     pat_typ: Term.types;
     pat_pat: Glob_term.cases_pattern;
     pat_expr: Constrexpr.cases_pattern_expr}

type proof_instr =
    (Term.constr statement,
     Term.constr,
     proof_pattern,
     Geninterp.Val.t) gen_proof_instr
