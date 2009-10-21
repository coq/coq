(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Target language for extraction: a core ML called MiniML. *)

open Pp
open Util
open Names
open Libnames

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)

(* We eliminate from terms:  1) types 2) logical parts.
   [Kother] stands both for logical or unknown reason. *)

type kill_reason = Ktype | Kother

type sign = Keep | Kill of kill_reason


(* Convention: outmost lambda/product gives the head of the list. *)

type signature = sign list

(*s ML type expressions. *)

type ml_type =
  | Tarr    of ml_type * ml_type
  | Tglob   of global_reference * ml_type list
  | Tvar    of int
  | Tvar'   of int (* same as Tvar, used to avoid clash *)
  | Tmeta   of ml_meta (* used during ML type reconstruction *)
  | Tdummy  of kill_reason
  | Tunknown
  | Taxiom

and ml_meta = { id : int; mutable contents : ml_type option }

(* ML type schema.
   The integer is the number of variable in the schema. *)

type ml_schema = int * ml_type

(*s ML inductive types. *)

type inductive_info =
  | Singleton
  | Coinductive
  | Standard
  | Record of global_reference list

type case_info = int list (* list of branches to merge in a _ pattern *)

(* A [ml_ind_packet] is the miniml counterpart of a [one_inductive_body].
   If the inductive is logical ([ip_logical = false]), then all other fields
   are unused. Otherwise,
   [ip_sign] is a signature concerning the arguments of the inductive,
   [ip_vars] contains the names of the type variables surviving in ML,
   [ip_types] contains the ML types of all constructors.
*)

type ml_ind_packet = {
  ip_typename : identifier;
  ip_consnames : identifier array;
  ip_logical : bool;
  ip_sign : signature;
  ip_vars : identifier list;
  ip_types : (ml_type list) array }

(* [ip_nparams] contains the number of parameters. *)

type equiv =
  | NoEquiv
  | Equiv of kernel_name
  | RenEquiv of string

type ml_ind = {
  ind_info : inductive_info;
  ind_nparams : int;
  ind_packets : ml_ind_packet array;
  ind_equiv : equiv
}

(*s ML terms. *)

type ml_ast =
  | MLrel    of int
  | MLapp    of ml_ast * ml_ast list
  | MLlam    of identifier * ml_ast
  | MLletin  of identifier * ml_ast * ml_ast
  | MLglob   of global_reference
  | MLcons   of inductive_info * global_reference * ml_ast list
  | MLcase   of (inductive_info*case_info) * ml_ast *
      (global_reference * identifier list * ml_ast) array
  | MLfix    of int * identifier array * ml_ast array
  | MLexn    of string
  | MLdummy
  | MLaxiom
  | MLmagic  of ml_ast

(*s ML declarations. *)

type ml_decl =
  | Dind  of kernel_name * ml_ind
  | Dtype of global_reference * identifier list * ml_type
  | Dterm of global_reference * ml_ast * ml_type
  | Dfix  of global_reference array * ml_ast array * ml_type array

type ml_spec =
  | Sind  of kernel_name * ml_ind
  | Stype of global_reference * identifier list * ml_type option
  | Sval  of global_reference * ml_type

type ml_specif =
  | Spec of ml_spec
  | Smodule of ml_module_type
  | Smodtype of ml_module_type

and ml_module_type =
  | MTident of module_path
  | MTfunsig of mod_bound_id * ml_module_type * ml_module_type
  | MTsig of module_path * ml_module_sig
  | MTwith of ml_module_type * ml_with_declaration

and ml_with_declaration =
  | ML_With_type of identifier list * identifier list * ml_type
  | ML_With_module of identifier list * module_path

and ml_module_sig = (label * ml_specif) list

type ml_structure_elem =
  | SEdecl of ml_decl
  | SEmodule of ml_module
  | SEmodtype of ml_module_type

and ml_module_expr =
  | MEident of module_path
  | MEfunctor of mod_bound_id * ml_module_type * ml_module_expr
  | MEstruct of module_path * ml_module_structure
  | MEapply of ml_module_expr * ml_module_expr

and ml_module_structure = (label * ml_structure_elem) list

and ml_module =
    { ml_mod_expr : ml_module_expr;
      ml_mod_type : ml_module_type }

(* NB: we do not translate the [mod_equiv] field, since [mod_equiv = mp]
   implies that [mod_expr = MEBident mp]. Same with [msb_equiv]. *)

type ml_structure = (module_path * ml_module_structure) list

type ml_signature = (module_path * ml_module_sig) list

type unsafe_needs = {
  mldummy : bool;
  tdummy : bool;
  tunknown : bool;
  magic : bool
}

type language_descr = {
  keywords : Idset.t;

  (* Concerning the source file *)
  file_suffix : string;
  capital_file : bool; (* should we capitalize filenames ? *)
  preamble : identifier -> module_path list -> unsafe_needs -> std_ppcmds;
  pp_struct : ml_structure -> std_ppcmds;

  (* Concerning a possible interface file *)
  sig_suffix : string option;
  sig_preamble : identifier -> module_path list -> unsafe_needs -> std_ppcmds;
  pp_sig : ml_signature -> std_ppcmds;

  (* for an isolated declaration print *)
  pp_decl : ml_decl -> std_ppcmds;

}
