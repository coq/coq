(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id$ *)

open Term

(* Types des valeurs (V) et des calculs (C).
 *
 * On a C = r:V,E,P,Q 
 *
 *   et V = (x1:V1)...(xn:Vn)C | V ref | V array | <type pur>
 *
 * INVARIANT: l'effet E contient toutes les variables apparaissant dans
 *            le programme ET les annotations P et Q
 *            Si E = { x1,...,xn | y1,...,ym }, les variables x sont les
 *            variables en lecture seule et y1 les variables modifi�es
 *            les xi sont libres dans P et Q, et les yi,result li�es dans Q
 *            i.e.  P = p(x)
 *               et Q = [y1]...[yn][res]q(x,y,res)
 *)

(* pre and post conditions *)

type 'a precondition = { p_assert : bool; p_name : name; p_value : 'a }

type 'a assertion  = { a_name : Identifier.name; a_value : 'a }

type 'a postcondition = 'a assertion

type predicate = constr assertion

(* binders *)

type 'a binder_type =
    BindType  of 'a
  | BindSet
  | Untyped

type 'a binder = Identifier.identifier * 'a binder_type

(* variant *)

type variant = constr * constr * constr (* phi, R, A *)

(* types des valeurs *)

type 'a ml_type_v =
    Ref       of 'a ml_type_v
  | Array     of 'a * 'a ml_type_v   (* size x type *)
  | Arrow     of 'a ml_type_v binder list * 'a ml_type_c

  | TypePure  of 'a

(* et type des calculs *)

and 'a ml_type_c =
    (Identifier.identifier * 'a ml_type_v) 
  * Peffect.t
  * ('a precondition list) * ('a postcondition option)

(* at beginning they contain Coq AST but they become constr after typing *)
type type_v = constr ml_type_v
type type_c = constr ml_type_c


