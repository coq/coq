(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Evd
open Proof_type
open EConstr

(** The refiner (handles primitive rules and high-level tactics). *)

val sig_it  : 'a sigma -> 'a
[@@ocaml.deprecated]
val project : 'a sigma -> evar_map
[@@ocaml.deprecated]

val pf_env  : goal sigma -> Environ.env
[@@ocaml.deprecated]
val pf_hyps : goal sigma -> named_context
[@@ocaml.deprecated]

val unpackage : 'a sigma -> evar_map ref * 'a
[@@ocaml.deprecated]
val repackage : evar_map ref -> 'a -> 'a sigma
[@@ocaml.deprecated]
val apply_sig_tac :
  evar_map ref -> (goal sigma -> goal list sigma) -> goal -> goal list
[@@ocaml.deprecated]

val refiner : rule -> tactic
[@@ocaml.deprecated]

(** {6 Tacticals. } *)

(** [tclIDTAC] is the identity tactic without message printing*)
val tclIDTAC          : tactic
[@@ocaml.deprecated]
val tclIDTAC_MESSAGE  : Pp.std_ppcmds -> tactic
[@@ocaml.deprecated]

(** [tclEVARS sigma] changes the current evar map *)
val tclEVARS : evar_map -> tactic
[@@ocaml.deprecated]
val tclEVARUNIVCONTEXT : Evd.evar_universe_context -> tactic
[@@ocaml.deprecated]

val tclPUSHCONTEXT : Evd.rigid -> Univ.universe_context_set -> tactic -> tactic
[@@ocaml.deprecated]
val tclPUSHEVARUNIVCONTEXT : Evd.evar_universe_context -> tactic
[@@ocaml.deprecated]

val tclPUSHCONSTRAINTS : Univ.constraints -> tactic
[@@ocaml.deprecated]

(** [tclTHEN tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [tac2] to every resulting subgoals *)
val tclTHEN          : tactic -> tactic -> tactic
[@@ocaml.deprecated]

(** [tclTHENLIST [t1;..;tn]] applies [t1] THEN [t2] ... THEN [tn]. More
   convenient than [tclTHEN] when [n] is large *)
val tclTHENLIST      : tactic list -> tactic
[@@ocaml.deprecated]

(** [tclMAP f [x1..xn]] builds [(f x1);(f x2);...(f xn)] *)
val tclMAP           : ('a -> tactic) -> 'a list -> tactic
[@@ocaml.deprecated]

(** [tclTHEN_i tac1 tac2 gls] applies the tactic [tac1] to [gls] and applies
   [(tac2 i)] to the [i]{^ th} resulting subgoal (starting from 1) *)
val tclTHEN_i        : tactic -> (int -> tactic) -> tactic
[@@ocaml.deprecated]

(** [tclTHENLAST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the last resulting subgoal (previously called [tclTHENL]) *)
val tclTHENLAST         : tactic -> tactic -> tactic
[@@ocaml.deprecated]

(** [tclTHENFIRST tac1 tac2 gls] applies the tactic [tac1] to [gls] and [tac2]
   to the first resulting subgoal *)
val tclTHENFIRST         : tactic -> tactic -> tactic
[@@ocaml.deprecated]

(** [tclTHENS tac1 [|t1 ; ... ; tn|] gls] applies the tactic [tac1] to
   [gls] and applies [t1],..., [tn] to the [n] resulting subgoals. Raises
   an error if the number of resulting subgoals is not [n] *)
val tclTHENSV         : tactic -> tactic array -> tactic
[@@ocaml.deprecated]

(** Same with a list of tactics *)
val tclTHENS         : tactic -> tactic list -> tactic
[@@ocaml.deprecated]

(** [tclTHENS3PARTS tac1 [|t1 ; ... ; tn|] tac2 [|t'1 ; ... ; t'm|] gls]
   applies the tactic [tac1] to [gls] then, applies [t1], ..., [tn] to
   the first [n] resulting subgoals, [t'1], ..., [t'm] to the last [m]
   subgoals and [tac2] to the rest of the subgoals in the middle. Raises an
   error if the number of resulting subgoals is strictly less than [n+m] *)
val tclTHENS3PARTS     : tactic -> tactic array -> tactic -> tactic array -> tactic
[@@ocaml.deprecated]

(** [tclTHENSLASTn tac1 [t1 ; ... ; tn] tac2 gls] applies [t1],...,[tn] on the
   last [n] resulting subgoals and [tac2] on the remaining first subgoals *)
val tclTHENSLASTn     : tactic -> tactic -> tactic array -> tactic
[@@ocaml.deprecated]

(** [tclTHENSFIRSTn tac1 [t1 ; ... ; tn] tac2 gls] first applies [tac1], then
   applies [t1],...,[tn] on the first [n] resulting subgoals and
   [tac2] for the remaining last subgoals (previously called tclTHENST) *)
val tclTHENSFIRSTn : tactic -> tactic array -> tactic -> tactic
[@@ocaml.deprecated]

(** [tclTHENLASTn tac1 [t1 ; ... ; tn] gls] first applies [tac1] then,
   applies [t1],...,[tn] on the last [n] resulting subgoals and leaves
   unchanged the other subgoals *)
val tclTHENLASTn    : tactic -> tactic array -> tactic
[@@ocaml.deprecated]

(** [tclTHENFIRSTn tac1 [t1 ; ... ; tn] gls] first applies [tac1] then,
   applies [t1],...,[tn] on the first [n] resulting subgoals and leaves
   unchanged the other subgoals (previously called [tclTHENSI]) *)
val tclTHENFIRSTn   : tactic -> tactic array -> tactic
[@@ocaml.deprecated]

(** A special exception for levels for the Fail tactic *)
exception FailError of int * Pp.std_ppcmds Lazy.t

(** Takes an exception and either raise it at the next
   level or do nothing. *)
val catch_failerror  : Exninfo.iexn -> unit

val tclORELSE0       : tactic -> tactic -> tactic
[@@ocaml.deprecated]
val tclORELSE        : tactic -> tactic -> tactic
[@@ocaml.deprecated]
val tclREPEAT        : tactic -> tactic
[@@ocaml.deprecated]
val tclREPEAT_MAIN   : tactic -> tactic
[@@ocaml.deprecated]
val tclFIRST         : tactic list -> tactic
[@@ocaml.deprecated]
val tclSOLVE         : tactic list -> tactic
[@@ocaml.deprecated]
val tclTRY           : tactic -> tactic
[@@ocaml.deprecated]
val tclTHENTRY       : tactic -> tactic -> tactic
[@@ocaml.deprecated]
val tclCOMPLETE      : tactic -> tactic
[@@ocaml.deprecated]
val tclAT_LEAST_ONCE : tactic -> tactic
[@@ocaml.deprecated]
val tclFAIL          : int -> Pp.std_ppcmds -> tactic
[@@ocaml.deprecated]
val tclFAIL_lazy     : int -> Pp.std_ppcmds Lazy.t -> tactic
[@@ocaml.deprecated]
val tclDO            : int -> tactic -> tactic
val tclPROGRESS      : tactic -> tactic
[@@ocaml.deprecated]
val tclSHOWHYPS      : tactic -> tactic

(** [tclIFTHENELSE tac1 tac2 tac3 gls] first applies [tac1] to [gls] then,
   if it succeeds, applies [tac2] to the resulting subgoals,
   and if not applies [tac3] to the initial goal [gls] *)
val tclIFTHENELSE    : tactic -> tactic -> tactic -> tactic
[@@ocaml.deprecated]
val tclIFTHENSELSE   : tactic -> tactic list -> tactic ->tactic
[@@ocaml.deprecated]
val tclIFTHENSVELSE   : tactic -> tactic array -> tactic ->tactic
[@@ocaml.deprecated]

(** [tclIFTHENTRYELSEMUST tac1 tac2 gls] applies [tac1] then [tac2]. If [tac1]
   has been successful, then [tac2] may fail. Otherwise, [tac2] must succeed.
   Equivalent to [(tac1;try tac2)||tac2] *)

val tclIFTHENTRYELSEMUST : tactic -> tactic -> tactic
[@@ocaml.deprecated]
