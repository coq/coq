(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
type ssrindex = int Misctypes.or_var

(* clear switch {H G} *)
type ssrclear = ssrhyps

(* Discharge occ switch (combined occurrence / clear switch) *)
type ssrdocc = ssrclear option * ssrocc

(* FIXME, make algebraic *)
type ssrtermkind = char

type ssrterm = ssrtermkind * Tacexpr.glob_constr_and_expr

type ssrview = ssrterm list

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
(* TODO | IPatDispatch of ssripatss (* /[..|..] *) *)
  | IPatCase of (* ipats_mod option * *) ssripatss (* this is not equivalent to /case /[..|..] if there are already multiple goals *)
  | IPatInj of ssripatss
  | IPatRewrite of (*occurrence option * rewrite_pattern **) ssrocc * ssrdir
  | IPatView of ssrterm list (* /view *)
  | IPatClear of ssrclear (* {H1 H2} *)
  | IPatSimpl of ssrsimpl
  | IPatNewHidden of Id.t list
(* | IPatVarsForAbstract of Id.t list *)

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
        bool * (ssrhpats * ((ssrfwdfmt * ssrterm) * 'tac ssrhint))

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

(* OOP : these are general shortcuts *)
type gist = Tacintern.glob_sign
type ist = Tacinterp.interp_sign
type goal = Goal.goal 
type 'a sigma = 'a Evd.sigma
type v82tac = Tacmach.tactic
