(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Mli-only files

Declarations
Entries

Constrexpr
Evar_kinds
Genredexpr
Locus
Notation_term
Tactypes
Decl_kinds
Extend
Glob_term
Misctypes
Pattern
Vernacexpr

Proof_type
*)

module Ppvernac = Ppvernac
module Command = Command
module States = States
module Kindops = Kindops
module Coq_config = Coq_config
module Esubst = Esubst
module Evar = Evar
module Libobject = Libobject
module Evd = Evd
module Libnames = Libnames
module Nameops = Nameops
module Topfmt = Topfmt
module Locusops = Locusops
module Lemmas = Lemmas
module Clenv = Clenv
module Elimschemes = Elimschemes
module Classes = Classes
module Class_tactics = Class_tactics
module Eauto = Eauto
module Keys = Keys
module Vernac_classifier = Vernac_classifier
module Autorewrite = Autorewrite
module Redops = Redops
module Elim = Elim
module Geninterp = Geninterp
module Obligations = Obligations
module Retroknowledge = Retroknowledge
module Evar_refiner = Evar_refiner
module Hipattern = Hipattern
module Auto = Auto
module Hints = Hints
module Contradiction = Contradiction
module Tacticals = Tacticals
module Tactics = Tactics
module Inv = Inv
module Leminv = Leminv
module Equality = Equality
module Redexpr = Redexpr
module Pfedit = Pfedit
module Stm = Stm
module Stateid = Stateid
module Declaremods = Declaremods
module Miscops = Miscops
module Miscprint = Miscprint
module Genprint = Genprint
module Ppconstr = Ppconstr
module Pputils = Pputils
module Logic = Logic
module Himsg = Himsg
module Tacred = Tacred
module Names = Names
module Indrec = Indrec
module Glob_ops = Glob_ops
module Constrexpr_ops = Constrexpr_ops
module Eqdecide = Eqdecide
module Detyping = Detyping
module ExplainErr = ExplainErr
module Printer = Printer
module Constrextern = Constrextern
module Locality = Locality
module Impargs = Impargs
module Termops = Termops
module Refiner = Refiner
module Ppextend = Ppextend
module Nametab = Nametab
module Vernacentries = Vernacentries
module Mltop = Mltop
module Goal = Goal
module Proof_global = Proof_global
module Proof = Proof
module Smartlocate = Smartlocate
module Dumpglob = Dumpglob
module Constrintern = Constrintern
module Topconstr = Topconstr
module Notation_ops = Notation_ops
module Patternops = Patternops
module Mod_typing = Mod_typing
module Modops = Modops
module Opaqueproof = Opaqueproof
module Ind_tables = Ind_tables
module Typeops = Typeops
module Inductive = Inductive
module Vars = Vars
module Reduction = Reduction
module Mod_subst = Mod_subst
module Sorts = Sorts
module Univ = Univ
module Constr = Constr
module CClosure = CClosure
module Type_errors = Type_errors
module Safe_typing = Safe_typing
module UGraph = UGraph
module Namegen = Namegen
module Ftactic = Ftactic
module UState = UState
module Proofview_monad = Proofview_monad
module Classops = Classops
module Global = Global
module Goptions = Goptions
module Lib = Lib
module Library = Library
module Summary = Summary
module Universes = Universes
module Declare = Declare
module Refine = Refine
module Find_subterm = Find_subterm
module Search = Search
module Reductionops = Reductionops
module Inductiveops = Inductiveops
module Recordops = Recordops
module Retyping = Retyping
module Typing = Typing
module Evarsolve = Evarsolve
module Constr_matching = Constr_matching
module Pretyping = Pretyping
module Evarconv = Evarconv
module Unification = Unification
module Typeclasses = Typeclasses
module Pretype_errors = Pretype_errors
module Notation = Notation
module Declareops = Declareops
module Globnames = Globnames
module Environ = Environ
module Term = Term
module Coqlib = Coqlib
module Context = Context
module Stdarg = Stdarg
module Tacmach = Tacmach
module Proofview = Proofview
module Evarutil = Evarutil
module EConstr = EConstr

module Prelude =
  struct
    type global_reference = Globnames.global_reference
    type metavariable = int
    type meta_value_map = (metavariable * Constr.constr) list
    type named_context_val = Environ.named_context_val
    type conv_pb = Reduction.conv_pb =
      | CONV
      | CUMUL
    type constr = Constr.constr
    type types = Constr.types
    type evar = Constr.existential_key
    type 'constr pexistential = 'constr Constr.pexistential
    type env = Environ.env
    type evar_map = Evd.evar_map
    type rigid = Evd.rigid =
               | UnivRigid
               | UnivFlexible of bool
    type reference = Libnames.reference =
      | Qualid of Libnames.qualid Loc.located
      | Ident of Names.Id.t Loc.located
  end
