(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file respects the dependency order established in Coq.

   To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done > API/link
   ```
 *)

(******************************************************************************)
(* config                                                                     *)
(******************************************************************************)
module Coq_config = Coq_config

(******************************************************************************)
(* Kernel *)
(******************************************************************************)
(* "mli" files *)
module Declarations = Declarations
module Entries = Entries

module Names = Names
(* module Uint31 *)
module Univ = Univ
module UGraph = UGraph
module Esubst = Esubst
module Sorts = Sorts
module Evar = Evar
module Constr = Constr
module Context = Context
module Vars = Vars
module Term = Term
module Mod_subst = Mod_subst
module Cbytecodes = Cbytecodes
(* module Copcodes *)
module Cemitcodes = Cemitcodes
(* module Nativevalues *)
(* module CPrimitives *)
module Opaqueproof = Opaqueproof
module Declareops = Declareops
module Retroknowledge = Retroknowledge
module Conv_oracle = Conv_oracle
(* module Pre_env *)
(* module Cbytegen *)
(* module Nativelambda *)
(* module Nativecode *)
(* module Nativelib *)
module Environ = Environ
module CClosure = CClosure
module Reduction = Reduction
(* module Nativeconv *)
module Type_errors = Type_errors
module Modops = Modops
module Inductive = Inductive
module Typeops = Typeops
(* module Indtypes *)
(* module Cooking *)
(* module Term_typing *)
(* module Subtyping *)
module Mod_typing = Mod_typing
(* module Nativelibrary *)
module Safe_typing = Safe_typing
(* module Vm *)
(* module Csymtable *)
(* module Vconv *)

(******************************************************************************)
(* Intf                                                                       *)
(******************************************************************************)
module Constrexpr = Constrexpr
module Locus = Locus
module Glob_term = Glob_term
module Extend = Extend
module Misctypes = Misctypes
module Pattern = Pattern
module Decl_kinds = Decl_kinds
module Vernacexpr = Vernacexpr
module Notation_term = Notation_term
module Evar_kinds = Evar_kinds
module Genredexpr = Genredexpr

(******************************************************************************)
(* Library *)
(******************************************************************************)
module Univops = Univops
module Nameops = Nameops
module Libnames = Libnames
module Globnames = Globnames
module Libobject = Libobject
module Summary = Summary
module Nametab = Nametab
module Global = Global
module Lib = Lib
module Declaremods = Declaremods
(* module Loadpath *)
module Library = Library
module States = States
module Kindops = Kindops
(* module Dischargedhypsmap *)
module Goptions = Goptions
(* module Decls *)
(* module Heads *)
module Keys = Keys
module Coqlib = Coqlib

(******************************************************************************)
(* Engine                                                                     *)
(******************************************************************************)
(* module Logic_monad *)
module Universes = Universes
module UState = UState
module Evd = Evd
module EConstr = EConstr
module Namegen = Namegen
module Termops = Termops
module Proofview_monad = Proofview_monad
module Evarutil = Evarutil
module Proofview = Proofview
module Ftactic = Ftactic
module Geninterp = Geninterp

(******************************************************************************)
(* Pretyping                                                                  *)
(******************************************************************************)
module Ltac_pretype = Ltac_pretype
module Locusops = Locusops
module Pretype_errors = Pretype_errors
module Reductionops = Reductionops
module Inductiveops = Inductiveops
(* module Vnorm *)
(* module Arguments_renaming *)
module Impargs = Impargs
(* module Nativenorm *)
module Retyping = Retyping
(* module Cbv *)
module Find_subterm = Find_subterm
(* module Evardefine *)
module Evarsolve = Evarsolve
module Recordops = Recordops
module Evarconv = Evarconv
module Typing = Typing
module Miscops = Miscops
module Glob_ops = Glob_ops
module Redops = Redops
module Patternops = Patternops
module Constr_matching = Constr_matching
module Tacred = Tacred
module Typeclasses = Typeclasses
module Classops = Classops
(* module Program *)
(* module Coercion *)
module Detyping = Detyping
module Indrec = Indrec
(* module Cases *)
module Pretyping = Pretyping
module Unification = Unification
module Univdecls = Univdecls
(******************************************************************************)
(* interp                                                                     *)
(******************************************************************************)
module Tactypes = Tactypes
module Stdarg = Stdarg
module Genintern = Genintern
module Constrexpr_ops = Constrexpr_ops
module Notation_ops = Notation_ops
module Notation = Notation
module Dumpglob = Dumpglob
(* module Syntax_def *)
module Smartlocate = Smartlocate
module Topconstr = Topconstr
(* module Reserve *)
(* module Implicit_quantifiers *)
module Constrintern = Constrintern
(* module Modintern *)
module Constrextern = Constrextern
(* module Discharge *)
module Declare = Declare

(******************************************************************************)
(* Proofs                                                                     *)
(******************************************************************************)
module Miscprint = Miscprint
module Goal = Goal
module Evar_refiner = Evar_refiner
(* module Proof_using *)
module Proof_type = Proof_type
module Logic = Logic
module Refine = Refine
module Proof = Proof
module Proof_bullet = Proof_bullet
module Proof_global = Proof_global
module Redexpr = Redexpr
module Refiner = Refiner
module Tacmach = Tacmach
module Pfedit = Pfedit
module Clenv = Clenv
(* module Clenvtac *)
(* "mli" file *)

(******************************************************************************)
(* Printing                                                                   *)
(******************************************************************************)
module Genprint = Genprint
module Pputils = Pputils
module Ppconstr = Ppconstr
module Printer = Printer
(* module Printmod *)
module Prettyp = Prettyp
module Ppvernac = Ppvernac

(******************************************************************************)
(* Parsing                                                                    *)
(******************************************************************************)
module Tok = Tok
module CLexer = CLexer
module Pcoq = Pcoq
module Egramml = Egramml
(* Egramcoq *)

module G_vernac = G_vernac
module G_proofs = G_proofs

(******************************************************************************)
(* Tactics                                                                    *)
(******************************************************************************)
(* module Dnet *)
(* module Dn *)
(* module Btermdn *)
module Tacticals = Tacticals
module Hipattern = Hipattern
module Ind_tables = Ind_tables
(* module Eqschemes *)
module Elimschemes = Elimschemes
module Tactics = Tactics
module Elim = Elim
module Equality = Equality
module Contradiction = Contradiction
module Inv = Inv
module Leminv = Leminv
module Hints = Hints
module Auto = Auto
module Eauto = Eauto
module Class_tactics = Class_tactics
(* module Term_dnet *)
module Eqdecide = Eqdecide
module Autorewrite = Autorewrite

(******************************************************************************)
(* Vernac                                                                     *)
(******************************************************************************)
(* module Vernacprop *)
module Lemmas = Lemmas
module Himsg = Himsg
module ExplainErr = ExplainErr
(* module Class *)
module Locality = Locality
module Metasyntax = Metasyntax
(* module Auto_ind_decl *)
module Search = Search
(* module Indschemes *)
module Obligations = Obligations
module ComDefinition = ComDefinition
module ComInductive = ComInductive
module ComFixpoint = ComFixpoint
module Classes = Classes
(* module Record *)
(* module Assumptions *)
module Vernacstate = Vernacstate
module Vernacinterp = Vernacinterp
module Mltop = Mltop
module Topfmt = Topfmt
module Vernacentries = Vernacentries

(******************************************************************************)
(* Stm                                                                        *)
(******************************************************************************)
module Vernac_classifier = Vernac_classifier
module Stm = Stm
