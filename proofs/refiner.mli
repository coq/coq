(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Evd
open EConstr

(** The refiner (handles primitive rules and high-level tactics). *)
type tactic = Proofview.V82.tac

val sig_it  : 'a sigma -> 'a
val project : 'a sigma -> evar_map

val pf_env  : Goal.goal sigma -> Environ.env
val pf_hyps : Goal.goal sigma -> named_context

val refiner : check:bool -> Constr.t -> unit Proofview.tactic

(** {6 Tacticals. } *)

(** [tclIDTAC] is the identity tactic without message printing*)
val tclIDTAC          : tactic
[@@ocaml.deprecated "Use Tactical.New.tclIDTAC"]
val tclIDTAC_MESSAGE  : Pp.t -> tactic
[@@ocaml.deprecated]

(** [tclEVARS sigma] changes the current evar map *)
val tclEVARS : evar_map -> tactic
[@@ocaml.deprecated "Use Proofview.Unsafe.tclEVARS"]


(** [tclTHEN tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [tac2] to every resulting subgoals *)
val tclTHEN          : tactic -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHEN"]

(** [tclTHENLIST [t1;..;tn]] applies [t1] THEN [t2] ... THEN [tn]. More
   convenient than [tclTHEN] when [n] is large *)
val tclTHENLIST      : tactic list -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENLIST"]

(** [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
val tclMAP           : ('a -> tactic) -> 'a list -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclMAP"]

(** [tclTHEN_i tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [(tac2 i)] to the [i]{^ th} resulting subgoal (starting from 1) *)
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHEN_i"]

(** [tclTHENLAST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the last resulting subgoal (previously called [tclTHENL]) *)
val tclTHENLAST         : tactic -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENLAST"]

(** [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the first resulting subgoal *)
val tclTHENFIRST         : tactic -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENFIRST"]

(** [tclTHENS tac1 [|t1 ; ... ; tn|] gls] applies the tactic [tac1] to
   [gls] and applies [t1],..., [tn] to the [n] resulting subgoals. Raises
   an error if the number of resulting subgoals is not [n] *)
val tclTHENSV         : tactic -> tactic array -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENSV"]

(** Same with a list of tactics *)
val tclTHENS         : tactic -> tactic list -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENS"]

(** [tclTHENS3PARTS tac1 [|t1 ; ... ; tn|] tac2 [|t'1 ; ... ; t'm|] gls]
   applies the tactic [tac1] to [gls] then, applies [t1], ..., [tn] to
   the first [n] resulting subgoals, [t'1], ..., [t'm] to the last [m]
   subgoals and [tac2] to the rest of the subgoals in the middle. Raises an
   error if the number of resulting subgoals is strictly less than [n+m] *)
val tclTHENS3PARTS     : tactic -> tactic array -> tactic -> tactic array -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENS3PARTS"]

(** [tclTHENSLASTn tac1 [t1 ; ... ; tn] tac2 gls] applies [t1],...,[tn] on the
   last [n] resulting subgoals and [tac2] on the remaining first subgoals *)
val tclTHENSLASTn     : tactic -> tactic -> tactic array -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENSLASTn"]

(** [tclTHENSFIRSTn tac1 [t1 ; ... ; tn] tac2 gls] first applies [tac1], then
   applies [t1],...,[tn] on the first [n] resulting subgoals and
   [tac2] for the remaining last subgoals (previously called tclTHENST) *)
val tclTHENSFIRSTn : tactic -> tactic array -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENSFIRSTn"]

(** A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.t Lazy.t

(** Takes an exception and either raise it at the next
   level or do nothing. *)
val catch_failerror  : Exninfo.iexn -> unit

val tclORELSE0       : tactic -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclORELSE0"]
val tclORELSE        : tactic -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclORELSE"]
val tclREPEAT        : tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclREPEAT"]
val tclFIRST         : tactic list -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclFIRST"]
val tclTRY           : tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTRY"]
val tclTHENTRY       : tactic -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclTHENTRY"]
val tclCOMPLETE      : tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclCOMPLETE"]
val tclAT_LEAST_ONCE : tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclAT_LEAST_ONCE"]
val tclFAIL          : int -> Pp.t -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclFAIL"]
val tclFAIL_lazy     : int -> Pp.t Lazy.t -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclFAIL_lazy"]
val tclDO            : int -> tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclDO"]
val tclPROGRESS      : tactic -> tactic
[@@ocaml.deprecated "Use Tactical.New.tclPROGRESS"]
val tclSHOWHYPS      : tactic -> tactic
[@@ocaml.deprecated "Internal tactic. Do not use."]
