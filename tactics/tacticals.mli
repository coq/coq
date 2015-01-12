(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Term
open Context
open Tacmach
open Proof_type
open Clenv
open Tacexpr
open Locus
open Misctypes

(** Tacticals i.e. functions from tactics to tactics. *)

val tclIDTAC         : tactic
val tclIDTAC_MESSAGE : std_ppcmds -> tactic
val tclORELSE0       : tactic -> tactic -> tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclTHEN          : tactic -> tactic -> tactic
val tclTHENSEQ       : tactic list -> tactic
val tclTHENLIST      : tactic list -> tactic
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic
val tclTHENFIRST     : tactic -> tactic -> tactic
val tclTHENLAST      : tactic -> tactic -> tactic
val tclTHENS         : tactic -> tactic list -> tactic
val tclTHENSV        : tactic -> tactic array -> tactic
val tclTHENSLASTn    : tactic -> tactic -> tactic array -> tactic
val tclTHENLASTn     : tactic -> tactic array -> tactic
val tclTHENSFIRSTn   : tactic -> tactic array -> tactic -> tactic
val tclTHENFIRSTn    : tactic -> tactic array -> tactic
val tclREPEAT        : tactic -> tactic
val tclREPEAT_MAIN   : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : int -> std_ppcmds -> tactic
val tclFAIL_lazy     : int -> std_ppcmds Lazy.t -> tactic
val tclDO            : int -> tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclSHOWHYPS      : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclMAP           : ('a -> tactic) -> 'a list -> tactic

val tclIFTHENELSE        : tactic -> tactic -> tactic -> tactic
val tclIFTHENSELSE       : tactic -> tactic list -> tactic -> tactic
val tclIFTHENSVELSE      : tactic -> tactic array -> tactic -> tactic
val tclIFTHENTRYELSEMUST : tactic -> tactic -> tactic

(** {6 Tacticals applying to hypotheses } *)

val onNthHypId       : int -> (Id.t -> tactic) -> tactic
val onNthHyp         : int -> (constr -> tactic) -> tactic
val onNthDecl        : int -> (named_declaration -> tactic) -> tactic
val onLastHypId      : (Id.t -> tactic) -> tactic
val onLastHyp        : (constr -> tactic) -> tactic
val onLastDecl       : (named_declaration -> tactic) -> tactic
val onNLastHypsId    : int -> (Id.t list -> tactic) -> tactic
val onNLastHyps      : int -> (constr list -> tactic) -> tactic
val onNLastDecls     : int -> (named_context -> tactic) -> tactic

val lastHypId   : goal sigma -> Id.t
val lastHyp     : goal sigma -> constr
val lastDecl    : goal sigma -> named_declaration
val nLastHypsId : int -> goal sigma -> Id.t list
val nLastHyps   : int -> goal sigma -> constr list
val nLastDecls  : int -> goal sigma -> named_context

val afterHyp    : Id.t -> goal sigma -> named_context

val ifOnHyp     : (Id.t * types -> bool) ->
                  (Id.t -> tactic) -> (Id.t -> tactic) ->
		   Id.t -> tactic

val onHyps      : (goal sigma -> named_context) ->
                  (named_context -> tactic) -> tactic

(** {6 Tacticals applying to goal components } *)

(** A [clause] denotes occurrences and hypotheses in a
   goal; in particular, it can abstractly refer to the set of
   hypotheses independently of the effective contents of the current goal *)

val onAllHyps           : (Id.t -> tactic) -> tactic
val onAllHypsAndConcl   : (Id.t option -> tactic) -> tactic

val onClause   : (Id.t option -> tactic) -> clause -> tactic
val onClauseLR : (Id.t option -> tactic) -> clause -> tactic

(** {6 Elimination tacticals. } *)

type branch_args = {
  ity        : pinductive;   (** the type we were eliminating on *)
  largs      : constr list; (** its arguments *)
  branchnum  : int;         (** the branch number *)
  pred       : constr;      (** the predicate we used *)
  nassums    : int;         (** the number of assumptions to be introduced *)
  branchsign : bool list;   (** the signature of the branch.
                               true=recursive argument, false=constant *)
  branchnames : intro_patterns}

type branch_assumptions = {
  ba        : branch_args;     (** the branch args *)
  assums    : named_context}   (** the list of assumptions introduced *)

(** [check_disjunctive_pattern_size loc pats n] returns an appropriate 
   error message if |pats| <> n *)
val check_or_and_pattern_size :
  Loc.t -> delayed_open_constr or_and_intro_pattern_expr -> int -> unit

(** Tolerate "[]" to mean a disjunctive pattern of any length *)
val fix_empty_or_and_pattern : int -> 
  delayed_open_constr or_and_intro_pattern_expr ->
  delayed_open_constr or_and_intro_pattern_expr

(** Useful for [as intro_pattern] modifier *)
val compute_induction_names :
  int -> or_and_intro_pattern option -> intro_patterns array

val elimination_sort_of_goal : goal sigma -> sorts_family
val elimination_sort_of_hyp  : Id.t -> goal sigma -> sorts_family
val elimination_sort_of_clause : Id.t option -> goal sigma -> sorts_family

val pf_with_evars :  (goal sigma -> Evd.evar_map * 'a) -> ('a -> tactic) -> tactic
val pf_constr_of_global : Globnames.global_reference -> (constr -> tactic) -> tactic

val elim_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic
val case_on_ba : (branch_assumptions -> tactic) -> branch_args  -> tactic

(** Tacticals defined directly in term of Proofview *)

(** The tacticals in the module [New] are the tactical of Ltac. Their
    semantics is an extension of the tacticals in this file for the
    multi-goal backtracking tactics. They do not have the same
    semantics as the similarly named tacticals in [Proofview]. The
    tactical of [Proofview] are used in the definition of the
    tacticals of [Tacticals.New], but they are more atomic. In
    particular [Tacticals.New.tclORELSE] sees like of progress as a
    failure, whereas [Proofview.tclORELSE] doesn't. Additionally every
    tactic which can catch failure ([tclOR], [tclORELSE], [tclTRY],
    [tclREPEAt], etc…) are run into each goal independently (failures
    and backtracks are localised to a given goal). *)
module New : sig
  open Proofview

  (** [catch_failerror e] fails and decreases the level if [e] is an
      Ltac error with level more than 0. Otherwise succeeds. *)
  val catch_failerror : Util.iexn -> unit tactic

  val tclIDTAC : unit tactic
  val tclTHEN : unit tactic -> unit tactic -> unit tactic
  (* [tclFAIL n msg] fails with [msg] as an error message at level [n]
     (meaning that it will jump over [n] error catching tacticals FROM
     THIS MODULE. *)
  val tclFAIL : int -> Pp.std_ppcmds -> 'a tactic

  val tclZEROMSG : ?loc:Loc.t -> Pp.std_ppcmds -> 'a tactic
  (** Fail with a [User_Error] containing the given message. *)

  val tclOR : unit tactic -> unit tactic -> unit tactic
  val tclORD : unit tactic -> (unit -> unit tactic) -> unit tactic
  (** Like {!tclOR} but accepts a delayed tactic as a second argument
      in the form of a function which will be run only in case of
      backtracking. *)

  val tclONCE : unit tactic -> unit tactic
  val tclEXACTLY_ONCE : unit tactic -> unit tactic

  val tclIFCATCH :
             unit tactic  ->
    (unit -> unit tactic) ->
    (unit -> unit tactic) -> unit tactic

  val tclORELSE0 : unit tactic -> unit tactic -> unit tactic
  val tclORELSE  : unit tactic -> unit tactic -> unit tactic

  (** [tclTHENS3PARTS tac1 [|t1 ; ... ; tn|] tac2 [|t'1 ; ... ; t'm|]
      gls] applies the tactic [tac1] to [gls] then, applies [t1], ...,
      [tn] to the first [n] resulting subgoals, [t'1], ..., [t'm] to the
      last [m] subgoals and [tac2] to the rest of the subgoals in the
      middle. Raises an error if the number of resulting subgoals is
      strictly less than [n+m] *)
  val tclTHENS3PARTS     : unit tactic -> unit tactic array -> unit tactic -> unit tactic array -> unit tactic
  val tclTHENSFIRSTn : unit tactic -> unit tactic array -> unit tactic -> unit tactic
  val tclTHENFIRSTn : unit tactic -> unit tactic array -> unit tactic
  (** [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls]
      and [tac2] to the first resulting subgoal *)
  val tclTHENFIRST : unit tactic -> unit tactic -> unit tactic
  val tclTHENLASTn : unit tactic -> unit tactic array -> unit tactic
  val tclTHENLAST  : unit tactic -> unit tactic -> unit tactic
  (* [tclTHENS t l = t <*> tclDISPATCH l] *)
  val tclTHENS : unit tactic -> unit tactic list -> unit tactic
  (* [tclTHENLIST [t1;…;tn]] is [t1<*>…<*>tn] *)
  val tclTHENLIST : unit tactic list -> unit tactic

  (** [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
  val tclMAP : ('a -> unit tactic) -> 'a list -> unit tactic

  val tclTRY : unit tactic -> unit tactic
  val tclFIRST : unit tactic list -> unit tactic
  val tclIFTHENELSE : unit tactic -> unit tactic -> unit tactic -> unit tactic
  val tclIFTHENSVELSE : unit tactic -> unit tactic array -> unit tactic -> unit tactic
  val tclIFTHENTRYELSEMUST : unit tactic -> unit tactic -> unit tactic

  val tclDO : int -> unit tactic -> unit tactic
  val tclREPEAT : unit tactic -> unit tactic
  (* Repeat on the first subgoal (no failure if no more subgoal) *)
  val tclREPEAT_MAIN : unit tactic -> unit tactic
  val tclCOMPLETE : 'a tactic -> 'a tactic
  val tclSOLVE : unit tactic list -> unit tactic
  val tclPROGRESS : unit tactic -> unit tactic
  val tclWITHHOLES : bool -> ('a -> unit tactic) -> Evd.evar_map -> 'a -> unit tactic

  val tclTIMEOUT : int -> unit tactic -> unit tactic
  val tclTIME : string option -> 'a tactic -> 'a tactic

  val nLastDecls  : [ `NF ] Proofview.Goal.t -> int -> named_context

  val ifOnHyp     : (identifier * types -> bool) ->
    (identifier -> unit Proofview.tactic) -> (identifier -> unit Proofview.tactic) ->
    identifier -> unit Proofview.tactic

  val onNthHypId : int -> (identifier -> unit tactic) -> unit tactic
  val onLastHypId      : (identifier -> unit tactic) -> unit tactic
  val onLastHyp        : (constr -> unit tactic) -> unit tactic
  val onLastDecl       : (named_declaration -> unit tactic) -> unit tactic

  val onHyps      : ([ `NF ] Proofview.Goal.t -> named_context) ->
                    (named_context -> unit tactic) -> unit tactic
  val afterHyp    : Id.t -> (named_context -> unit tactic) -> unit tactic

  val tryAllHyps          : (identifier -> unit tactic) -> unit tactic
  val tryAllHypsAndConcl  : (identifier option -> unit tactic) -> unit tactic
  val onClause   : (identifier option -> unit tactic) -> clause -> unit tactic

  val elimination_sort_of_goal : 'a Proofview.Goal.t -> sorts_family
  val elimination_sort_of_hyp  : Id.t -> 'a Proofview.Goal.t -> sorts_family
  val elimination_sort_of_clause : Id.t option -> 'a Proofview.Goal.t -> sorts_family

  val elimination_then :
    (branch_args -> unit Proofview.tactic) ->
    constr -> unit Proofview.tactic

  val case_then_using :
    or_and_intro_pattern option -> (branch_args -> unit Proofview.tactic) ->
    constr option -> pinductive -> Term.constr * Term.types -> unit Proofview.tactic

  val case_nodep_then_using :
    or_and_intro_pattern option -> (branch_args -> unit Proofview.tactic) ->
    constr option -> pinductive -> Term.constr * Term.types -> unit Proofview.tactic

  val elim_on_ba : (branch_assumptions -> unit Proofview.tactic) -> branch_args  -> unit Proofview.tactic
  val case_on_ba : (branch_assumptions -> unit Proofview.tactic) -> branch_args  -> unit Proofview.tactic

  val pf_constr_of_global : Globnames.global_reference -> (constr -> unit Proofview.tactic) -> unit Proofview.tactic
end
