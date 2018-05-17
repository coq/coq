(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Evd
open Proof_type
open EConstr

(** The refiner (handles primitive rules and high-level tactics). *)

val sig_it  : 'a sigma -> 'a
val project : 'a sigma -> evar_map

val pf_env  : goal sigma -> Environ.env
val pf_hyps : goal sigma -> named_context

val unpackage : 'a sigma -> evar_map ref * 'a
[@@ocaml.deprecated "Do not use [evar_map ref]"]
val repackage : evar_map ref -> 'a -> 'a sigma
[@@ocaml.deprecated "Do not use [evar_map ref]"]
val apply_sig_tac :
  evar_map ref -> (goal sigma -> goal list sigma) -> goal -> goal list
[@@ocaml.deprecated "Do not use [evar_map ref]"]

val refiner : rule -> tactic

(** {6 Tacticals. } *)

(** [tclIDTAC] is the identity tactic without message printing*)
val tclIDTAC          : tactic
val tclIDTAC_MESSAGE  : Pp.t -> tactic

(** [tclEVARS sigma] changes the current evar map *)
val tclEVARS : evar_map -> tactic
val tclEVARUNIVCONTEXT : UState.t -> tactic

val tclPUSHCONTEXT : Evd.rigid -> Univ.ContextSet.t -> tactic -> tactic
val tclPUSHEVARUNIVCONTEXT : UState.t -> tactic

val tclPUSHCONSTRAINTS : Univ.Constraint.t -> tactic

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
exception FailError of int * Pp.t Lazy.t

(** Takes an exception and either raise it at the next
   level or do nothing. *)
val catch_failerror  : Exninfo.iexn -> unit

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
val tclFAIL          : int -> Pp.t -> tactic
val tclFAIL_lazy     : int -> Pp.t Lazy.t -> tactic
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
val tclSHOWHYPS      : tactic -> tactic

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
