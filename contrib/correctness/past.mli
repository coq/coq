(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(*s Abstract syntax of imperative programs. *)

open Names
open Ptype
open Topconstr

type termination = 
  | RecArg of int 
  | Wf of constr_expr * constr_expr

type variable = identifier

type pattern =
  | PatVar of identifier
  | PatConstruct of identifier * ((kernel_name * int) * int)
  | PatAlias of pattern * identifier
  | PatPair of pattern * pattern
  | PatApp of pattern list

type epattern =
  | ExnConstant of identifier
  | ExnBind of identifier * identifier

type ('a, 'b) block_st =
  | Label of string
  | Assert of 'b Ptype.assertion
  | Statement of 'a

type ('a, 'b) block = ('a, 'b) block_st list

type ('a, 'b) t = { 
  desc : ('a, 'b) t_desc;
  pre  : 'b Ptype.precondition list;
  post : 'b Ptype.postcondition option;
  loc  : Util.loc;
  info : 'a 
}

and ('a, 'b) t_desc =
  | Variable of variable
  | Acc of variable
  | Aff of variable * ('a, 'b) t
  | TabAcc of bool * variable * ('a, 'b) t
  | TabAff of bool * variable * ('a, 'b) t * ('a, 'b) t
  | Seq of (('a, 'b) t, 'b) block
  | While of ('a, 'b) t * 'b Ptype.assertion option * ('b * 'b) *
               (('a, 'b) t, 'b) block
  | If of ('a, 'b) t * ('a, 'b) t * ('a, 'b) t
  | Lam of 'b Ptype.ml_type_v Ptype.binder list * ('a, 'b) t
  | Apply of ('a, 'b) t * ('a, 'b) arg list
  | SApp of ('a, 'b) t_desc list * ('a, 'b) t list
  | LetRef of variable * ('a, 'b) t * ('a, 'b) t
  | Let of variable * ('a, 'b) t * ('a, 'b) t
  | LetRec of variable * 'b Ptype.ml_type_v Ptype.binder list *
                'b Ptype.ml_type_v * ('b * 'b) * ('a, 'b) t
  | PPoint of string * ('a, 'b) t_desc
  | Expression of Term.constr
  | Debug of string * ('a, 'b) t

and ('a, 'b) arg =
  | Term of ('a, 'b) t
  | Refarg of variable
  | Type of 'b Ptype.ml_type_v

type program = (unit, Topconstr.constr_expr) t

(*s Intermediate type for CC terms. *)

type cc_type = Term.constr

type cc_bind_type = 
  | CC_typed_binder of cc_type 
  | CC_untyped_binder

type cc_binder = variable * cc_bind_type

type cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_type * cc_binder list * cc_term * cc_term
  | CC_lam of cc_binder list * cc_term
  | CC_app of cc_term * cc_term list
  | CC_tuple of bool * cc_type list * cc_term list
  | CC_case of cc_type * cc_term * cc_term list
  | CC_expr of Term.constr
  | CC_hole of cc_type
