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
open Libnames

type mutable_flag = bool
type rec_flag = bool
type redef_flag = bool
type lid = Id.t
type uid = Id.t

type ltac_constant = KerName.t
type ltac_alias = KerName.t
type ltac_notation = KerName.t
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
| CTydAlg of (Attributes.vernac_flags * uid * raw_typexpr list) list
| CTydRec of (lid * mutable_flag * raw_typexpr) list
| CTydOpn

type 'a glb_typexpr =
| GTypVar of 'a
| GTypArrow of 'a glb_typexpr * 'a glb_typexpr
| GTypRef of type_constant or_tuple * 'a glb_typexpr list

type glb_alg_type = {
  galg_constructors : (UserWarn.t option * uid * int glb_typexpr list) list;
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

(* We want to generate these easily in the Closed case, otherwise we
   could have the kn in the ctor_data_for_patterns type. Maybe still worth doing?? *)
type ctor_indx =
  | Closed of int
  | Open of ltac_constructor

type ctor_data_for_patterns = {
  ctyp : type_constant option; (* [None] means [Tuple cnargs] and [cindx = Closed 0] *)
  cnargs : int;
  cindx : ctor_indx;
}

type glb_pat =
  | GPatVar of Name.t
  | GPatAtm of atom
  | GPatRef of ctor_data_for_patterns * glb_pat list
  | GPatOr of glb_pat list
  | GPatAs of glb_pat * Id.t

module PartialPat : sig
  type r =
    | Var of Name.t
    | Atom of atom
    | Ref of ctor_data_for_patterns * t list
    | Or of t list
    | As of t * Id.t
    | Extension of { example : atom option }
  and t = r CAst.t
end

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
| GTacFullMatch of glb_tacexpr * (glb_pat * glb_tacexpr) list
| GTacExt : (_, 'a) Tac2dyn.Arg.tag * 'a -> glb_tacexpr
| GTacPrm of ml_tactic_name

(** Tactic expressions *)
type raw_patexpr_r =
| CPatVar of Name.t
| CPatAtm of atom
| CPatRef of ltac_constructor or_tuple or_relid * raw_patexpr list
| CPatRecord of (ltac_projection or_relid * raw_patexpr) list
| CPatCnv of raw_patexpr * raw_typexpr
| CPatOr of raw_patexpr list
| CPatAs of raw_patexpr * lident

and raw_patexpr = raw_patexpr_r CAst.t

type raw_tacexpr_r =
| CTacAtm of atom
| CTacRef of tacref or_relid
| CTacCst of ltac_constructor or_tuple or_relid
| CTacFun of raw_patexpr list * raw_tacexpr
| CTacApp of raw_tacexpr * raw_tacexpr list
| CTacSyn of (lname * raw_tacexpr) list * KerName.t
| CTacLet of rec_flag * (raw_patexpr * raw_tacexpr) list * raw_tacexpr
| CTacCnv of raw_tacexpr * raw_typexpr
| CTacSeq of raw_tacexpr * raw_tacexpr
| CTacIft of raw_tacexpr * raw_tacexpr * raw_tacexpr
| CTacCse of raw_tacexpr * raw_taccase list
| CTacRec of raw_tacexpr option * raw_recexpr
| CTacPrj of raw_tacexpr * ltac_projection or_relid
| CTacSet of raw_tacexpr * ltac_projection or_relid * raw_tacexpr
| CTacExt : ('a, _) Tac2dyn.Arg.tag * 'a -> raw_tacexpr_r
| CTacGlb of int * (lname * raw_tacexpr * int glb_typexpr option) list * glb_tacexpr * int glb_typexpr
(** CTacGlb is essentially an expanded typed notation.
    Arguments bound with Anonymous have no type constraint. *)

and raw_tacexpr = raw_tacexpr_r CAst.t

and raw_taccase = raw_patexpr * raw_tacexpr

and raw_recexpr = (ltac_projection or_relid * raw_tacexpr) list

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
| StrMut of qualid * Names.lident option * raw_tacexpr
  (** Redefinition of mutable globals *)

type frame =
| FrLtac of ltac_constant
| FrAnon of glb_tacexpr
| FrPrim of ml_tactic_name
| FrExtn : ('a, 'b) Tac2dyn.Arg.tag * 'b -> frame

type backtrace = frame list
