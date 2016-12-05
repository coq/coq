(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Genarg
open Names
open Libnames

type mutable_flag = bool
type rec_flag = bool
type lid = Id.t
type uid = Id.t

type ltac_constant = KerName.t
type ltac_constructor = KerName.t
type ltac_projection = KerName.t
type type_constant = KerName.t

(** {5 Misc} *)

type ml_tactic_name = {
  mltac_plugin : string;
  mltac_tactic : string;
}

(** {5 Type syntax} *)

type raw_typexpr =
| CTypVar of Name.t located
| CTypArrow of Loc.t * raw_typexpr * raw_typexpr
| CTypTuple of Loc.t * raw_typexpr list
| CTypRef of Loc.t * qualid located * raw_typexpr list

type raw_typedef =
| CTydDef of raw_typexpr option
| CTydAlg of (uid * raw_typexpr list) list
| CTydRec of (lid * mutable_flag * raw_typexpr) list

type 'a glb_typexpr =
| GTypVar of 'a
| GTypArrow of 'a glb_typexpr * 'a glb_typexpr
| GTypTuple of 'a glb_typexpr list
| GTypRef of type_constant * 'a glb_typexpr list

type glb_typedef =
| GTydDef of int glb_typexpr option
| GTydAlg of (uid * int glb_typexpr list) list
| GTydRec of (lid * mutable_flag * int glb_typexpr) list

type type_scheme = int * int glb_typexpr

type raw_quant_typedef = Id.t located list * raw_typedef
type glb_quant_typedef = int * glb_typedef

(** {5 Term syntax} *)

type atom =
| AtmInt of int
| AtmStr of string

(** Tactic expressions *)
type raw_patexpr =
| CPatAny of Loc.t
| CPatRef of Loc.t * qualid located * raw_patexpr list
| CPatTup of raw_patexpr list located

type raw_tacexpr =
| CTacAtm of atom located
| CTacRef of qualid located
| CTacFun of Loc.t * (Name.t located * raw_typexpr option) list * raw_tacexpr
| CTacApp of Loc.t * raw_tacexpr * raw_tacexpr list
| CTacLet of Loc.t * rec_flag * (Name.t located * raw_typexpr option * raw_tacexpr) list * raw_tacexpr
| CTacTup of raw_tacexpr list located
| CTacArr of raw_tacexpr list located
| CTacLst of raw_tacexpr list located
| CTacCnv of Loc.t * raw_tacexpr * raw_typexpr
| CTacSeq of Loc.t * raw_tacexpr * raw_tacexpr
| CTacCse of Loc.t * raw_tacexpr * raw_taccase list
| CTacRec of Loc.t * raw_recexpr
| CTacPrj of Loc.t * raw_tacexpr * qualid located
| CTacSet of Loc.t * raw_tacexpr * qualid located * raw_tacexpr
| CTacExt of Loc.t * raw_generic_argument

and raw_taccase = raw_patexpr * raw_tacexpr

and raw_recexpr = (qualid located * raw_tacexpr) list

type case_info =
| GCaseTuple of int
| GCaseAlg of type_constant

type glb_tacexpr =
| GTacAtm of atom
| GTacVar of Id.t
| GTacRef of ltac_constant
| GTacFun of Name.t list * glb_tacexpr
| GTacApp of glb_tacexpr * glb_tacexpr list
| GTacLet of rec_flag * (Name.t * glb_tacexpr) list * glb_tacexpr
| GTacTup of glb_tacexpr list
| GTacArr of glb_tacexpr list
| GTacCst of type_constant * int * glb_tacexpr list
| GTacCse of glb_tacexpr * case_info * glb_tacexpr array * (Name.t array * glb_tacexpr) array
| GTacPrj of glb_tacexpr * int
| GTacSet of glb_tacexpr * int * glb_tacexpr
| GTacExt of glob_generic_argument
| GTacPrm of ml_tactic_name * glb_tacexpr list

(** Toplevel statements *)
type strexpr =
| StrVal of rec_flag * (Name.t located * raw_tacexpr) list
| StrTyp of rec_flag * (Id.t located * raw_quant_typedef) list
| StrPrm of Id.t located * raw_typexpr * ml_tactic_name

(** {5 Dynamic semantics} *)

(** Values are represented in a way similar to OCaml, i.e. they constrast
    immediate integers (integers, constructors without arguments) and structured
    blocks (tuples, arrays, constructors with arguments), as well as a few other
    base cases, namely closures, strings and dynamic type coming from the Coq
    implementation. *)

type tag = int

type valexpr =
| ValInt of int
  (** Immediate integers *)
| ValBlk of tag * valexpr array
  (** Structured blocks *)
| ValStr of Bytes.t
  (** Strings *)
| ValCls of closure
  (** Closures *)
| ValExt of Geninterp.Val.t
  (** Arbitrary data *)

and closure = {
  mutable clos_env : valexpr Id.Map.t;
  (** Mutable so that we can implement recursive functions imperatively *)
  clos_var : Name.t list;
  (** Bound variables *)
  clos_exp : glb_tacexpr;
  (** Body *)
}

type ml_tactic = valexpr list -> valexpr Proofview.tactic

type environment = valexpr Id.Map.t
