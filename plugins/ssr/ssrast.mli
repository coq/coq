(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names
open Ltac_plugin

(* Names of variables to be cleared (automatic check: not a section var) *)
type ssrhyp = SsrHyp of Id.t Loc.located
(* Variant of the above *)
type ssrhyp_or_id = Hyp of ssrhyp | Id of ssrhyp

(* Variant of the above *)
type ssrhyps = ssrhyp list

(* Direction to be used for rewriting as in -> or rewrite flag *)
type ssrdir = Ssrmatching_plugin.Ssrmatching.ssrdir = L2R | R2L

(* simpl: "/=", cut: "//", simplcut: "//=" nop: commodity placeholder *)
type ssrsimpl = Simpl of int | Cut of int | SimplCut of int * int | Nop

(* modality for rewrite and do: ! ? *)
type ssrmmod = May | Must | Once

(* modality with a bound for rewrite and do: !n ?n *)
type ssrmult = int * ssrmmod

(** Occurrence switch {1 2}, all is Some(false,[]) *)
type ssrocc = (bool * int list) option

(* index MAYBE REMOVE ONLY INTERNAL stuff between {} *)
type ssrindex = int Locus.or_var

(* clear switch {H G} *)
type ssrclear = ssrhyps

(* Discharge occ switch (combined occurrence / clear switch) *)
type ssrdocc = ssrclear option * ssrocc

(* OLD ssr terms *)
type ssrtermkind = char (* FIXME, make algebraic *)
type ssrterm = ssrtermkind * Tacexpr.glob_constr_and_expr

(* NEW ssr term *)

(* These terms are raw but closed with the intenalization/interpretation
 * context.  It is up to the tactic receiving it to decide if such contexts
 * are useful or not, and eventually manipulate the term before turning it
 * into a constr *)
type ast_closure_term = {
  body : Constrexpr.constr_expr;
  glob_env : Genintern.glob_sign option; (* for Tacintern.intern_constr *)
  interp_env :  Geninterp.interp_sign option; (* for Tacinterp.interp_open_constr_with_bindings *)
  annotation : [ `None | `Parens | `DoubleParens | `At ];
}

type ssrview = ast_closure_term list

(* TODO
type id_mod = Hat | HatTilde | Sharp
 *)

(* Only [One] forces an introduction, possibly reducing the goal. *)
type anon_iter =
  | One
  | Drop
  | All
(* TODO
  | Dependent (* fast mode *)
  | UntilMark
  | Temporary (* "+" *)
 *)

type ssripat =
  | IPatNoop
  | IPatId of (*TODO id_mod option * *) Id.t
  | IPatAnon of anon_iter (* inaccessible name *)
(* TODO  | IPatClearMark *)
  | IPatDispatch of bool (* ssr exception: accept a dispatch on the empty list even when there are subgoals *) * ssripatss (* (..|..) *)
  | IPatCase of (* ipats_mod option * *) ssripatss (* this is not equivalent to /case /[..|..] if there are already multiple goals *)
  | IPatInj of ssripatss
  | IPatRewrite of (*occurrence option * rewrite_pattern **) ssrocc * ssrdir
  | IPatView of bool * ssrview (* {}/view (true if the clear is present) *)
  | IPatClear of ssrclear (* {H1 H2} *)
  | IPatSimpl of ssrsimpl
  | IPatAbstractVars of Id.t list
  | IPatTac of unit Proofview.tactic

and ssripats = ssripat list
and ssripatss = ssripats list
type ssrhpats = ((ssrclear * ssripats) * ssripats) * ssripats
type ssrhpats_wtransp = bool * ssrhpats

(* tac => inpats *)
type ssrintrosarg = Tacexpr.raw_tactic_expr * ssripats


type ssrfwdid = Id.t
(** Binders (for fwd tactics) *)
type 'term ssrbind =
  | Bvar of Name.t
  | Bdecl of Name.t list * 'term
  | Bdef of Name.t * 'term option * 'term
  | Bstruct of Name.t
  | Bcast of 'term
(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for the two first levels of representation of  *)
(* of constr terms.                                                      *)
type ssrbindfmt =
  | BFvar
  | BFdecl of int        (* #xs *)
  | BFcast               (* final cast *)
  | BFdef                (* has cast? *)
  | BFrec of bool * bool (* has struct? * has cast? *)
type 'term ssrbindval = 'term ssrbind list * 'term

(** Forward chaining argument *)
(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)
type ssrfwdkind = FwdHint of string * bool | FwdHave | FwdPose
type ssrfwdfmt = ssrfwdkind * ssrbindfmt list

(* in *)
type ssrclseq = InGoal | InHyps
 | InHypsGoal | InHypsSeqGoal | InSeqGoal | InHypsSeq | InAll | InAllHyps

type 'tac ssrhint = bool * 'tac option list

type 'tac fwdbinders =
        bool * (ssrhpats * ((ssrfwdfmt * ast_closure_term) * 'tac ssrhint))

type clause =
  (ssrclear * ((ssrhyp_or_id * string) *
              Ssrmatching_plugin.Ssrmatching.cpattern option) option)
type clauses = clause list * ssrclseq

type wgen =
           (ssrclear *
            ((ssrhyp_or_id * string) *
             Ssrmatching_plugin.Ssrmatching.cpattern option)
            option)

type 'a ssrdoarg = ((ssrindex * ssrmmod) * 'a ssrhint) * clauses
type 'a ssrseqarg = ssrindex * ('a ssrhint * 'a option)


open Ssrmatching_plugin
open Ssrmatching

type 'a ssrcasearg = ssripat option * ('a * ssripats)
type 'a ssrmovearg = ssrview * 'a ssrcasearg

type ssrdgens = { dgens : (ssrdocc * cpattern) list;
                  gens  : (ssrdocc * cpattern) list;
                  clr  : ssrclear }
type 'a ssragens = (ssrdocc * 'a) list list * ssrclear
type ssrapplyarg = ssrterm list * (ssrterm ssragens * ssripats)

(* OOP : these are general shortcuts *)
type gist = Tacintern.glob_sign
type ist = Tacinterp.interp_sign
type goal = Goal.goal
type 'a sigma = 'a Evd.sigma
type v82tac = Tacmach.tactic
