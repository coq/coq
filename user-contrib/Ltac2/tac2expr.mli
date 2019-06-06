(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames

type mutable_flag = bool
type rec_flag = bool
type redef_flag = bool
type lid = Id.t
type uid = Id.t

type ltac_constant = KerName.t
type ltac_alias = KerName.t
type ltac_constructor = KerName.t
type ltac_projection = KerName.t
type type_constant = KerName.t

type tacref =
| TacConstant of ltac_constant
| TacAlias of ltac_alias

type 'a or_relid =
| RelId of qualid
| AbsKn of 'a

(** {5 Misc} *)

type ml_tactic_name = {
  mltac_plugin : string;
  mltac_tactic : string;
}

type 'a or_tuple =
| Tuple of int
| Other of 'a

(** {5 Type syntax} *)

type raw_typexpr_r =
| CTypVar of Name.t
| CTypArrow of raw_typexpr * raw_typexpr
| CTypRef of type_constant or_tuple or_relid * raw_typexpr list

and raw_typexpr = raw_typexpr_r CAst.t

type raw_typedef =
| CTydDef of raw_typexpr option
| CTydAlg of (uid * raw_typexpr list) list
| CTydRec of (lid * mutable_flag * raw_typexpr) list
| CTydOpn

type 'a glb_typexpr =
| GTypVar of 'a
| GTypArrow of 'a glb_typexpr * 'a glb_typexpr
| GTypRef of type_constant or_tuple * 'a glb_typexpr list

type glb_alg_type = {
  galg_constructors : (uid * int glb_typexpr list) list;
  (** Constructors of the algebraic type *)
  galg_nconst : int;
  (** Number of constant constructors *)
  galg_nnonconst : int;
  (** Number of non-constant constructors *)
}

type glb_typedef =
| GTydDef of int glb_typexpr option
| GTydAlg of glb_alg_type
| GTydRec of (lid * mutable_flag * int glb_typexpr) list
| GTydOpn

type type_scheme = int * int glb_typexpr

type raw_quant_typedef = Names.lident list * raw_typedef
type glb_quant_typedef = int * glb_typedef

(** {5 Term syntax} *)

type atom =
| AtmInt of int
| AtmStr of string

(** Tactic expressions *)
type raw_patexpr_r =
| CPatVar of Name.t
| CPatRef of ltac_constructor or_tuple or_relid * raw_patexpr list
| CPatCnv of raw_patexpr * raw_typexpr

and raw_patexpr = raw_patexpr_r CAst.t

type raw_tacexpr_r =
| CTacAtm of atom
| CTacRef of tacref or_relid
| CTacCst of ltac_constructor or_tuple or_relid
| CTacFun of raw_patexpr list * raw_tacexpr
| CTacApp of raw_tacexpr * raw_tacexpr list
| CTacLet of rec_flag * (raw_patexpr * raw_tacexpr) list * raw_tacexpr
| CTacCnv of raw_tacexpr * raw_typexpr
| CTacSeq of raw_tacexpr * raw_tacexpr
| CTacCse of raw_tacexpr * raw_taccase list
| CTacRec of raw_recexpr
| CTacPrj of raw_tacexpr * ltac_projection or_relid
| CTacSet of raw_tacexpr * ltac_projection or_relid * raw_tacexpr
| CTacExt : ('a, _) Tac2dyn.Arg.tag * 'a -> raw_tacexpr_r

and raw_tacexpr = raw_tacexpr_r CAst.t

and raw_taccase = raw_patexpr * raw_tacexpr

and raw_recexpr = (ltac_projection or_relid * raw_tacexpr) list

type case_info = type_constant or_tuple

type 'a open_match = {
  opn_match : 'a;
  opn_branch : (Name.t * Name.t array * 'a) KNmap.t;
  (** Invariant: should not be empty *)
  opn_default : Name.t * 'a;
}

type glb_tacexpr =
| GTacAtm of atom
| GTacVar of Id.t
| GTacRef of ltac_constant
| GTacFun of Name.t list * glb_tacexpr
| GTacApp of glb_tacexpr * glb_tacexpr list
| GTacLet of rec_flag * (Name.t * glb_tacexpr) list * glb_tacexpr
| GTacCst of case_info * int * glb_tacexpr list
| GTacCse of glb_tacexpr * case_info * glb_tacexpr array * (Name.t array * glb_tacexpr) array
| GTacPrj of type_constant * glb_tacexpr * int
| GTacSet of type_constant * glb_tacexpr * int * glb_tacexpr
| GTacOpn of ltac_constructor * glb_tacexpr list
| GTacWth of glb_tacexpr open_match
| GTacExt : (_, 'a) Tac2dyn.Arg.tag * 'a -> glb_tacexpr
| GTacPrm of ml_tactic_name * glb_tacexpr list

(** {5 Parsing & Printing} *)

type exp_level =
| E5
| E4
| E3
| E2
| E1
| E0

type sexpr =
| SexprStr of string CAst.t
| SexprInt of int CAst.t
| SexprRec of Loc.t * Id.t option CAst.t * sexpr list

(** {5 Toplevel statements} *)

type strexpr =
| StrVal of mutable_flag * rec_flag * (Names.lname * raw_tacexpr) list
  (** Term definition *)
| StrTyp of rec_flag * (qualid * redef_flag * raw_quant_typedef) list
  (** Type definition *)
| StrPrm of Names.lident * raw_typexpr * ml_tactic_name
  (** External definition *)
| StrSyn of sexpr list * int option * raw_tacexpr
  (** Syntactic extensions *)
| StrMut of qualid * raw_tacexpr
  (** Redefinition of mutable globals *)

(** {5 Dynamic semantics} *)

(** Values are represented in a way similar to OCaml, i.e. they contrast
    immediate integers (integers, constructors without arguments) and structured
    blocks (tuples, arrays, constructors with arguments), as well as a few other
    base cases, namely closures, strings, named constructors, and dynamic type
    coming from the Coq implementation. *)

type tag = int

type frame =
| FrLtac of ltac_constant
| FrAnon of glb_tacexpr
| FrPrim of ml_tactic_name
| FrExtn : ('a, 'b) Tac2dyn.Arg.tag * 'b -> frame

type backtrace = frame list
