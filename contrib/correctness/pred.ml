(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Past

(* here we only perform eta-reductions on programs to eliminate
 * redexes of the kind
 *
 *   let (x1,...,xn) = e in (x1,...,xn)  -->  e
 *
 *)

let is_eta_redex bl al =
  try
    List.for_all2
      (fun (id,_) t -> match t with CC_var id' -> id=id' | _ -> false)
      bl al
  with
      Invalid_argument("List.for_all2") -> false

let rec red = function
    CC_letin (dep, ty, bl, (e1,info), e2) ->
      begin match red e2 with
	  CC_tuple (false,tl,al) ->
	    if is_eta_redex bl al then
	      red e1
	    else
	      CC_letin (dep, ty, bl, (red e1,info),
			CC_tuple (false,tl,List.map red al))
	| e -> CC_letin (dep, ty, bl, (red e1,info), e)
      end

  | CC_lam (bl, e) ->
      CC_lam (bl, red e)
  | CC_app (e, al) ->
      CC_app (red e, List.map red al)
  | CC_case (ty, (e1,info), el) ->
      CC_case (ty, (red e1,info), List.map red el)
  | CC_tuple (dep, tl, al) ->
      CC_tuple (dep, tl, List.map red al)
  | e -> e


(* How to reduce uncomplete proof terms when they have become constr *)

open Generic
open Term
open Reduction

(* Il ne faut pas reduire de redexe (beta/iota) qui impliquerait
 * la substitution d'une métavariable.
 * 
 * On commence par rendre toutes les applications binaire (strong bin_app)
 * puis on applique la reduction spéciale programmes définie dans
 * typing/reduction *)

let bin_app = function
    DOPN(AppL,v) as c ->
      (match Array.length v with
	   1 -> v.(0)
	 | 2 -> c
	 | n ->
	     let f = DOPN(AppL,Array.sub v 0 (pred n)) in
	       DOPN(AppL,[|f;v.(pred n)|]))
  | c -> c

let red_cci c = 
  let c = strong bin_app c in strong whd_programs c

