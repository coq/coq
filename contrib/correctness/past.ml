(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Term
open Ptype

(* Programmes impératifs *)

type termination = RecArg of int
                 | Wf     of Coqast.t * Coqast.t

type variable = Names.identifier

type pattern =
    PatVar       of Names.identifier
  | PatConstruct of Names.identifier * ((Names.section_path * int) * int)
  | PatAlias     of pattern * Names.identifier
  | PatPair      of pattern * pattern
  | PatApp       of pattern list
  
type epattern =
    ExnConstant of Names.identifier
  | ExnBind     of Names.identifier * Names.identifier

type ('a,'b) block_st =
    Label     of string
  | Assert    of 'b assertion
  | Statement of 'a

type ('a,'b) block = ('a,'b) block_st list

(* type of programs with assertions of type 'b and info of type 'a *)

type ('a,'b) t =
  { desc : ('a,'b) t_desc ;
    pre  : 'b precondition list ;
    post : 'b postcondition option ;
    loc  : Coqast.loc ;
    info : 'a }

and ('a,'b) t_desc = 
    Var    of variable
  | Acc    of variable
  | Aff    of variable * (('a,'b) t)
  | TabAcc of bool * variable * (('a,'b) t)
  | TabAff of bool * variable * (('a,'b) t) * (('a,'b) t)
  | Seq    of (('a,'b) t,'b) block
  | While  of (('a,'b) t)           (* test *)
            * 'b assertion option   (* invariant *)
	    * ('b * 'b)             (* variant *)
	    * (('a,'b) t, 'b) block (* corps *)
  | If     of (('a,'b) t)  * (('a,'b) t) * (('a,'b) t)
  | Lam    of 'b ml_type_v binder list * ('a,'b) t
  | App    of (('a,'b) t) * (('a,'b) arg) list
  | SApp   of (('a,'b) t_desc) list * (('a,'b) t) list  (* for connectives *)
  | LetRef of variable * (('a,'b) t) * (('a,'b) t)
  | LetIn  of variable * (('a,'b) t) * (('a,'b) t)
  | LetRec of variable                                 (* nom *)
            * 'b ml_type_v binder list * 'b ml_type_v  (* types *)
            * ('b * 'b)                                (* variant *)
	    * ('a,'b) t                                (* corps *)
  | PPoint of string * ('a,'b) t_desc
  | Expression of constr

  | Debug  of string * (('a,'b) t) 

and ('a,'b) arg = 
    Term   of (('a,'b) t) 
  | Refarg of variable
  | Type   of 'b ml_type_v

type program = (unit, Coqast.t) t


(* AST for intermediate constructions.
 *
 * We define an intermediate type between typed program (above)
 * and CIC terms (constr), because we need to perform some eta-reductions
 * (see prog_red.ml for details)
 *
 * But here types are already CIC terms (constr).
 *)

type cc_type = constr

type cc_bind_type =
    CC_typed_binder of cc_type
  | CC_untyped_binder

type cc_binder = variable * cc_bind_type

type cc_term =
    CC_var   of variable
  | CC_letin of bool                (* dep. or not *)
              * cc_type             (* type of result *)
	      * cc_binder list
	      * (cc_term * constr)  (* the matched term and its ind. type *)
	      * cc_term
  | CC_lam   of cc_binder list * cc_term
  | CC_app   of cc_term * cc_term list
  | CC_tuple of bool                (* dep. or not *)
              * cc_type list * cc_term list
  | CC_case  of cc_type             (* type of result *)
              * (cc_term * constr)  (* the test and its inductive type *)
	      * cc_term list        (* branches *)
  | CC_expr  of constr
  | CC_hole  of cc_type


