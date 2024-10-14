(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Evd
open Locus
open Tactypes

(** A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.t Lazy.t

(** Tacticals defined directly in term of Proofview *)

(** The tacticals below are the tactical of Ltac. Their
    semantics is an extension of the tacticals in this file for the
    multi-goal backtracking tactics. They do not have the same
    semantics as the similarly named tacticals in [Proofview]. The
    tactical of [Proofview] are used in the definition of the
    tacticals of [Tacticals], but they are more atomic. In
    particular [Tacticals.tclORELSE] sees lack of progress as a
    failure, whereas [Proofview.tclORELSE] doesn't. Additionally every
    tactic which can catch failure ([tclOR], [tclORELSE], [tclTRY],
    [tclREPEAt], etc…) are run into each goal independently (failures
    and backtracks are localised to a given goal). *)

open Proofview

(** [catch_failerror e] fails and decreases the level if [e] is an
    Ltac error with level more than 0. Otherwise succeeds. *)
val catch_failerror : Exninfo.iexn -> unit tactic

val tclIDTAC : unit tactic
val tclTHEN : unit tactic -> unit tactic -> unit tactic
(* [tclFAILn n msg] fails with [msg] as an error message at level [n]
    (meaning that it will jump over [n] error catching tacticals FROM
    THIS MODULE. *)
val tclFAILn : ?info:Exninfo.info -> int -> Pp.t -> 'a tactic

val tclFAIL : ?info:Exninfo.info -> Pp.t -> 'a tactic
(** Same as above with level set to 0. *)

val tclZEROMSG : ?info:Exninfo.info -> ?loc:Loc.t -> Pp.t -> 'a tactic
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
val tclTHENSLASTn    : unit tactic -> unit tactic -> unit tactic array -> unit tactic
val tclTHENSFIRSTn : unit tactic -> unit tactic array -> unit tactic -> unit tactic
val tclTHENFIRSTn : unit tactic -> unit tactic array -> unit tactic

(** [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls]
    and [tac2] to the first resulting subgoal *)
val tclTHENFIRST : unit tactic -> unit tactic -> unit tactic
val tclBINDFIRST : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
val tclTHENLASTn : unit tactic -> unit tactic array -> unit tactic
val tclTHENLAST  : unit tactic -> unit tactic -> unit tactic
val tclBINDLAST  : 'a tactic -> ('a -> 'b tactic) -> 'b tactic
(* [tclTHENS t l = t <*> tclDISPATCH l] *)
val tclTHENS : unit tactic -> unit tactic list -> unit tactic
(* [tclTHENLIST [t1;…;tn]] is [t1<*>…<*>tn] *)
val tclTHENLIST : unit tactic list -> unit tactic

(** [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
val tclMAP : ('a -> unit tactic) -> 'a list -> unit tactic

val tclTRY : unit tactic -> unit tactic
val tclTRYb : unit tactic -> bool list tactic
val tclFIRST : unit tactic list -> unit tactic
val tclIFTHENELSE : unit tactic -> unit tactic -> unit tactic -> unit tactic
val tclIFTHENSVELSE : unit tactic -> unit tactic array -> unit tactic -> unit tactic
val tclIFTHENTRYELSEMUST : unit tactic -> unit tactic -> unit tactic
val tclIFTHENFIRSTTRYELSEMUST : unit tactic -> unit tactic -> unit tactic

val tclDO : int -> unit tactic -> unit tactic
val tclREPEAT : unit tactic -> unit tactic
(* Repeat on the first subgoal (no failure if no more subgoal) *)
val tclREPEAT_MAIN : unit tactic -> unit tactic
val tclCOMPLETE : 'a tactic -> 'a tactic
val tclSOLVE : unit tactic list -> unit tactic
val tclPROGRESS : unit tactic -> unit tactic
val tclRUNWITHHOLES : bool -> 'a tactic -> ('a -> 'b tactic) -> 'b tactic
(** [tclRUNWITHHOLES b tac0 tac] is [tac0 >>= tac] if [b = false],
    otherwise it additionally checks that evars created by [tac0] are solved after [tac]. *)

val tclWITHHOLES : bool -> 'a tactic -> Evd.evar_map -> 'a tactic
val tclDELAYEDWITHHOLES : bool -> 'a delayed_open -> ('a -> unit tactic) -> unit tactic
val tclMAPDELAYEDWITHHOLES : bool -> 'a delayed_open list -> ('a -> unit tactic) -> unit tactic
(* in [tclMAPDELAYEDWITHHOLES with_evars l tac] the delayed
    argument of [l] are evaluated in the possibly-updated
    environment and updated sigma of each new successive goals *)

val tactic_of_delayed : 'a delayed_open -> 'a tactic
(** Must be focused to use *)

val check_evar_list : Environ.env -> evar_map -> Evar.Set.t -> evar_map -> Evar.t list
  (* [check_evar_list env sigma evars origsigma] returns the subset of
     [evars] not instantiated (up to restriction) in the extension
     [sigma] of [origsigma] where evars of [origsigma] are considered
     as "axioms", that is that an evar of [evars] instantiated by an
     evar of [origsigma] is considered to be instantiated *)

val tclTIMEOUT : int -> unit tactic -> unit tactic
val tclTIME : string option -> 'a tactic -> 'a tactic

val nLastDecls  : Proofview.Goal.t -> int -> named_context

val ifOnHyp : (Environ.env -> evar_map -> Id.t * types -> bool) ->
  (Id.t -> unit Proofview.tactic) -> (Id.t -> unit Proofview.tactic) ->
  Id.t -> unit Proofview.tactic

val onNthHypId : int -> (Id.t -> unit tactic) -> unit tactic
val onLastHypId      : (Id.t -> unit tactic) -> unit tactic
val onLastHyp        : (constr -> unit tactic) -> unit tactic
val onLastDecl       : (named_declaration -> unit tactic) -> unit tactic

val onNLastHypsId    : int -> (Id.t list -> unit tactic) -> unit tactic
val onNLastHyps      : int -> (constr list -> unit tactic) -> unit tactic
val onNLastDecls     : int -> (named_context -> unit tactic) -> unit tactic

val onHyps      : (Proofview.Goal.t -> named_context) ->
                  (named_context -> unit tactic) -> unit tactic
val afterHyp    : Id.t -> (named_context -> unit tactic) -> unit tactic

val tryAllHyps          : (Id.t -> unit tactic) -> unit tactic
val tryAllHypsAndConcl  : (Id.t option -> unit tactic) -> unit tactic
val onClause   : (Id.t option -> unit tactic) -> clause -> unit tactic

val onAllHyps           : (Id.t -> unit tactic) -> unit tactic
val onAllHypsAndConcl   : (Id.t option -> unit tactic) -> unit tactic

val elimination_sort_of_goal : Proofview.Goal.t -> Sorts.family
val elimination_sort_of_hyp  : Id.t -> Proofview.Goal.t -> Sorts.family
val elimination_sort_of_clause : Id.t option -> Proofview.Goal.t -> Sorts.family

val pf_constr_of_global : GlobRef.t -> constr Proofview.tactic

val tclTYPEOFTHEN : ?refresh:bool -> constr -> (evar_map -> types -> unit Proofview.tactic) -> unit Proofview.tactic

val tclSELECT : ?nosuchgoal:'a tactic -> Goal_select.t -> 'a tactic -> 'a tactic
[@@ocaml.deprecated "(8.14) Use [Goal_select.tclSELECT]"]

(** {6 Elimination tacticals. } *)

(** [get_and_check_or_and_pattern loc pats branchsign] returns an appropriate
   error message if |pats| <> |branchsign|; extends them if no pattern is given
   for let-ins in the case of a conjunctive pattern *)
val get_and_check_or_and_pattern :
  ?loc:Loc.t -> delayed_open_constr or_and_intro_pattern_expr ->
  bool list array -> intro_patterns array

(** Tolerate "[]" to mean a disjunctive pattern of any length *)
val fix_empty_or_and_pattern : int ->
  delayed_open_constr or_and_intro_pattern_expr ->
  delayed_open_constr or_and_intro_pattern_expr

val compute_constructor_signatures : Environ.env -> rec_flag:bool -> inductive * 'a -> bool list array

(** Useful for [as intro_pattern] modifier *)
val compute_induction_names :
  bool -> bool list array -> or_and_intro_pattern option -> intro_patterns array
