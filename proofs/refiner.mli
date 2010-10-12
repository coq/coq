(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Sign
open Evd
open Proof_type
open Tacexpr
open Logic

(** The refiner (handles primitive rules and high-level tactics). *)

val sig_it  : 'a sigma -> 'a
val project : 'a sigma -> evar_map

val pf_env  : goal sigma -> Environ.env
val pf_hyps : goal sigma -> named_context

val unpackage : 'a sigma -> evar_map ref * 'a
val repackage : evar_map ref -> 'a -> 'a sigma
val apply_sig_tac :
  evar_map ref -> (goal sigma -> goal list sigma) -> goal -> goal list

(** {6 Hiding the implementation of tactics. } *)

(** [abstract_tactic tac] hides the (partial) proof produced by [tac] under
   a single proof node. The boolean tells if the default tactic is used. *)
(* spiwack: currently here for compatibility, abstract_operation 
    is a second projection *)
val abstract_operation : compound_rule -> tactic -> tactic
val abstract_tactic : ?dflt:bool -> atomic_tactic_expr -> tactic -> tactic
val abstract_tactic_expr : ?dflt:bool -> tactic_expr -> tactic -> tactic
val abstract_extended_tactic :
  ?dflt:bool -> string -> typed_generic_argument list -> tactic -> tactic

val refiner : rule -> tactic

(** {6 Tacticals. } *)

(** [tclNORMEVAR] forces propagation of evar constraints *)
val tclNORMEVAR       : tactic

(** [tclIDTAC] is the identity tactic without message printing*)
val tclIDTAC          : tactic
val tclIDTAC_MESSAGE  : Pp.std_ppcmds -> tactic

(** [tclEVARS sigma] changes the current evar map *)
val tclEVARS : evar_map -> tactic

(** [tclTHEN tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [tac2] to every resulting subgoals *)
val tclTHEN          : tactic -> tactic -> tactic

(** [tclTHENLIST [t1;..;tn]] applies [t1] THEN [t2] ... THEN [tn]. More
   convenient than [tclTHEN] when [n] is large *)
val tclTHENLIST      : tactic list -> tactic

(** [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
val tclMAP           : ('a -> tactic) -> 'a list -> tactic

(** [tclTHEN_i tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [(tac2 i)] to the [i]{^ th} resulting subgoal (starting from 1) *)
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic

(** [tclTHENLAST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the last resulting subgoal (previously called [tclTHENL]) *)
val tclTHENLAST         : tactic -> tactic -> tactic

(** [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the first resulting subgoal *)
val tclTHENFIRST         : tactic -> tactic -> tactic

(** [tclTHENS tac1 [|t1 ; ... ; tn|] gls] applies the tactic [tac1] to
   [gls] and applies [t1],..., [tn] to the [n] resulting subgoals. Raises
   an error if the number of resulting subgoals is not [n] *)
val tclTHENSV         : tactic -> tactic array -> tactic

(** Same with a list of tactics *)
val tclTHENS         : tactic -> tactic list -> tactic

(** [tclTHENST] is renamed [tclTHENSFIRSTn]
val tclTHENST        : tactic -> tactic array -> tactic -> tactic
*)

(** [tclTHENS3PARTS tac1 [|t1 ; ... ; tn|] tac2 [|t'1 ; ... ; t'm|] gls]
   applies the tactic [tac1] to [gls] then, applies [t1], ..., [tn] to
   the first [n] resulting subgoals, [t'1], ..., [t'm] to the last [m]
   subgoals and [tac2] to the rest of the subgoals in the middle. Raises an
   error if the number of resulting subgoals is strictly less than [n+m] *)
val tclTHENS3PARTS     : tactic -> tactic array -> tactic -> tactic array -> tactic

(** [tclTHENSLASTn tac1 [t1 ; ... ; tn] tac2 gls] applies [t1],...,[tn] on the
   last [n] resulting subgoals and [tac2] on the remaining first subgoals *)
val tclTHENSLASTn     : tactic -> tactic -> tactic array -> tactic

(** [tclTHENSFIRSTn tac1 [t1 ; ... ; tn] tac2 gls] first applies [tac1], then
   applies [t1],...,[tn] on the first [n] resulting subgoals and
   [tac2] for the remaining last subgoals (previously called tclTHENST) *)
val tclTHENSFIRSTn : tactic -> tactic array -> tactic -> tactic

(** [tclTHENLASTn tac1 [t1 ; ... ; tn] gls] first applies [tac1] then,
   applies [t1],...,[tn] on the last [n] resulting subgoals and leaves
   unchanged the other subgoals *)
val tclTHENLASTn    : tactic -> tactic array -> tactic

(** [tclTHENFIRSTn tac1 [t1 ; ... ; tn] gls] first applies [tac1] then,
   applies [t1],...,[tn] on the first [n] resulting subgoals and leaves
   unchanged the other subgoals (previously called [tclTHENSI]) *)
val tclTHENFIRSTn   : tactic -> tactic array -> tactic

(** A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.std_ppcmds Lazy.t

(** Takes an exception and either raise it at the next
   level or do nothing. *)
val catch_failerror  : exn -> unit

val tclORELSE0       : tactic -> tactic -> tactic
val tclORELSE        : tactic -> tactic -> tactic
val tclREPEAT        : tactic -> tactic
val tclREPEAT_MAIN   : tactic -> tactic
val tclFIRST         : tactic list -> tactic
val tclSOLVE         : tactic list -> tactic
val tclTRY           : tactic -> tactic
val tclTHENTRY       : tactic -> tactic -> tactic
val tclCOMPLETE      : tactic -> tactic
val tclAT_LEAST_ONCE : tactic -> tactic
val tclFAIL          : int -> Pp.std_ppcmds -> tactic
val tclFAIL_lazy     : int -> Pp.std_ppcmds Lazy.t -> tactic
val tclDO            : int -> tactic -> tactic
val tclWEAK_PROGRESS : tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclNOTSAMEGOAL   : tactic -> tactic
val tclINFO          : tactic -> tactic

(** [tclIFTHENELSE tac1 tac2 tac3 gls] first applies [tac1] to [gls] then,
   if it succeeds, applies [tac2] to the resulting subgoals,
   and if not applies [tac3] to the initial goal [gls] *)
val tclIFTHENELSE    : tactic -> tactic -> tactic -> tactic
val tclIFTHENSELSE   : tactic -> tactic list -> tactic ->tactic
val tclIFTHENSVELSE   : tactic -> tactic array -> tactic ->tactic

(** [tclIFTHENTRYELSEMUST tac1 tac2 gls] applies [tac1] then [tac2]. If [tac1]
   has been successful, then [tac2] may fail. Otherwise, [tac2] must succeed.
   Equivalent to [(tac1;try tac2)||tac2] *)

val tclIFTHENTRYELSEMUST : tactic -> tactic -> tactic

(** {6 Tactics handling a list of goals. } *)

type tactic_list = goal list sigma -> goal list sigma

val tclFIRSTLIST       : tactic_list list -> tactic_list
val tclIDTAC_list      : tactic_list
val first_goal         : 'a list sigma -> 'a sigma
val apply_tac_list     : tactic -> tactic_list
val then_tactic_list   : tactic_list -> tactic_list -> tactic_list
val tactic_list_tactic : tactic_list -> tactic
val goal_goal_list     : 'a sigma -> 'a list sigma

(** [tclWITHHOLES solve_holes tac (sigma,c)] applies [tac] to [c] which
   may have unresolved holes; if [solve_holes] these holes must be
   resolved after application of the tactic; [sigma] must be an
   extension of the sigma of the goal *)
val tclWITHHOLES : bool -> ('a -> tactic) -> evar_map -> 'a -> tactic
