(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.

(** ML-facing types *)

Ltac2 Type hypothesis := [ AnonHyp (int) | NamedHyp (ident) ].

Ltac2 Type bindings := [
| NoBindings
| ImplicitBindings (constr list)
| ExplicitBindings ((hypothesis * constr) list)
].

Ltac2 Type constr_with_bindings := constr * bindings.

Ltac2 Type occurrences := [
| AllOccurrences
| AllOccurrencesBut (int list)
| NoOccurrences
| OnlyOccurrences (int list)
].

Ltac2 Type hyp_location_flag := [ InHyp | InHypTypeOnly | InHypValueOnly ].

Ltac2 Type clause := {
  on_hyps : (ident * occurrences * hyp_location_flag) list option;
  on_concl : occurrences;
}.

Ltac2 Type evaluable_reference := [
| EvalVarRef (ident)
| EvalConstRef (constant)
].

Ltac2 Type red_flags := {
  rBeta : bool;
  rMatch : bool;
  rFix : bool;
  rCofix : bool;
  rZeta : bool;
  rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
  rConst : evaluable_reference list
}.

(** Standard, built-in tactics. See Ltac1 for documentation. *)

Ltac2 @ external eelim : constr_with_bindings -> constr_with_bindings option -> unit := "ltac2" "tac_eelim".
Ltac2 @ external ecase : constr_with_bindings -> unit := "ltac2" "tac_ecase".

Ltac2 @ external egeneralize : (constr * occurrences * ident option) list -> unit := "ltac2" "tac_egeneralize".

Ltac2 @ external pose : ident option -> constr -> unit := "ltac2" "tac_pose".
Ltac2 @ external set : ident option -> (unit -> constr) -> clause -> unit := "ltac2" "tac_set".
Ltac2 @ external eset : ident option -> (unit -> constr) -> clause -> unit := "ltac2" "tac_eset".

Ltac2 @ external red : clause -> unit := "ltac2" "tac_red".
Ltac2 @ external hnf : clause -> unit := "ltac2" "tac_hnf".
Ltac2 @ external cbv : red_flags -> clause -> unit := "ltac2" "tac_cbv".
Ltac2 @ external cbn : red_flags -> clause -> unit := "ltac2" "tac_cbn".
Ltac2 @ external lazy : red_flags -> clause -> unit := "ltac2" "tac_lazy".

Ltac2 @ external reflexivity : unit -> unit := "ltac2" "tac_reflexivity".

Ltac2 @ external assumption : unit -> unit := "ltac2" "tac_assumption".

Ltac2 @ external transitivity : constr -> unit := "ltac2" "tac_transitivity".

Ltac2 @ external etransitivity : unit -> unit := "ltac2" "tac_etransitivity".

Ltac2 @ external cut : constr -> unit := "ltac2" "tac_cut".

Ltac2 @ external left : bindings -> unit := "ltac2" "tac_left".
Ltac2 @ external eleft : bindings -> unit := "ltac2" "tac_eleft".
Ltac2 @ external right : bindings -> unit := "ltac2" "tac_right".
Ltac2 @ external eright : bindings -> unit := "ltac2" "tac_eright".

Ltac2 @ external constructor : unit -> unit := "ltac2" "tac_constructor".
Ltac2 @ external econstructor : unit -> unit := "ltac2" "tac_econstructor".
Ltac2 @ external split : bindings -> unit := "ltac2" "tac_split".
Ltac2 @ external esplit : bindings -> unit := "ltac2" "tac_esplit".

Ltac2 @ external constructor_n : int -> bindings -> unit := "ltac2" "tac_constructorn".
Ltac2 @ external econstructor_n : int -> bindings -> unit := "ltac2" "tac_econstructorn".

Ltac2 @ external intros_until : hypothesis -> unit := "ltac2" "tac_introsuntil".

Ltac2 @ external symmetry : clause -> unit := "ltac2" "tac_symmetry".

Ltac2 @ external rename : (ident * ident) list -> unit := "ltac2" "tac_rename".

Ltac2 @ external revert : ident list -> unit := "ltac2" "tac_revert".

Ltac2 @ external admit : unit -> unit := "ltac2" "tac_admit".

Ltac2 @ external fix_ : ident option -> int -> unit := "ltac2" "tac_fix".
Ltac2 @ external cofix_ : ident option -> unit := "ltac2" "tac_cofix".

Ltac2 @ external clear : ident list -> unit := "ltac2" "tac_clear".
Ltac2 @ external keep : ident list -> unit := "ltac2" "tac_keep".

Ltac2 @ external clearbody : ident list -> unit := "ltac2" "tac_clearbody".

Ltac2 @ external exact_no_check : constr -> unit := "ltac2" "tac_exactnocheck".
Ltac2 @ external vm_cast_no_check : constr -> unit := "ltac2" "tac_vmcastnocheck".
Ltac2 @ external native_cast_no_check : constr -> unit := "ltac2" "tac_nativecastnocheck".

Ltac2 @ external absurd : constr -> unit := "ltac2" "tac_absurd".

Ltac2 @ external subst : ident list -> unit := "ltac2" "tac_subst".
Ltac2 @ external subst_all : unit -> unit := "ltac2" "tac_substall".
