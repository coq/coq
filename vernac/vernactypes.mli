(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Interpretation of extended vernac phrases. *)

module InProg : sig
  type _ t =
    | Ignore : unit t
    | Use : Declare.OblState.t t

  val cast : Declare.OblState.t -> 'a t -> 'a
end

module OutProg : sig
  type _ t =
    | No : unit t
    | Yes : Declare.OblState.t t
    | Push
    | Pop

  val cast : 'a -> 'a t -> Declare.OblState.t NeList.t -> Declare.OblState.t NeList.t
end

module InProof : sig
  type _ t =
    | Ignore : unit t
    | Reject : unit t
    | Use : Declare.Proof.t t
    | UseOpt : Declare.Proof.t option t

  val cast : Declare.Proof.t option -> 'a t -> 'a
end

module OutProof : sig

  type _ t =
    | No : unit t
    | Close : unit t
    | Update : Declare.Proof.t t
    | New : Declare.Proof.t t

end

type ('inprog,'outprog,'inproof,'outproof) vernac_type = {
  inprog : 'inprog InProg.t;
  outprog : 'outprog InProg.t;
  inproof : 'inproof InProof.t;
  outproof : 'outproof OutProof.t;
}

type typed_vernac =
    TypedVernac : {
      inprog : 'inprog InProg.t;
      outprog : 'outprog OutProg.t;
      inproof : 'inproof InProof.t;
      outproof : 'outproof OutProof.t;
      run : pm:'inprog -> proof:'inproof -> 'outprog * 'outproof;
    } -> typed_vernac

(** Some convenient typed_vernac constructors. Used by coqpp. *)

val vtdefault : (unit -> unit) -> typed_vernac
val vtnoproof : (unit -> unit) -> typed_vernac
val vtcloseproof : (lemma:Declare.Proof.t -> pm:Declare.OblState.t -> Declare.OblState.t) -> typed_vernac
val vtopenproof : (unit -> Declare.Proof.t) -> typed_vernac
val vtmodifyproof : (pstate:Declare.Proof.t -> Declare.Proof.t) -> typed_vernac
val vtreadproofopt : (pstate:Declare.Proof.t option -> unit) -> typed_vernac
val vtreadproof : (pstate:Declare.Proof.t -> unit) -> typed_vernac
val vtreadprogram : (pm:Declare.OblState.t -> unit) -> typed_vernac
val vtmodifyprogram : (pm:Declare.OblState.t -> Declare.OblState.t) -> typed_vernac
val vtdeclareprogram : (pm:Declare.OblState.t -> Declare.Proof.t) -> typed_vernac
val vtopenproofprogram : (pm:Declare.OblState.t -> Declare.OblState.t * Declare.Proof.t) -> typed_vernac
