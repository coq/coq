(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Past
open Pmisc

let rec cc_subst subst = function
  | CC_var id as c -> 
      (try CC_expr (List.assoc id subst) with Not_found -> c)
  | CC_letin (b,ty,bl,c1,c2) ->
      CC_letin (b, real_subst_in_constr subst ty, cc_subst_binders subst bl,
		cc_subst subst c1, cc_subst (cc_cross_binders subst bl) c2)
  | CC_lam (bl, c) ->
      CC_lam (cc_subst_binders subst bl, 
	      cc_subst (cc_cross_binders subst bl) c)
  | CC_app (c, cl) ->
      CC_app (cc_subst subst c, List.map (cc_subst subst) cl)
  | CC_tuple (b, tl, cl) ->
      CC_tuple (b, List.map (real_subst_in_constr subst) tl,
		List.map (cc_subst subst) cl)
  | CC_case (ty, c, cl) ->
      CC_case (real_subst_in_constr subst ty, cc_subst subst c,
	       List.map (cc_subst subst) cl)
  | CC_expr c ->
      CC_expr (real_subst_in_constr subst c)
  | CC_hole ty ->
      CC_hole (real_subst_in_constr subst ty)

and cc_subst_binders subst = List.map (cc_subst_binder subst)

and cc_subst_binder subst = function
  | id,CC_typed_binder c -> id,CC_typed_binder (real_subst_in_constr subst c)
  | b -> b

and cc_cross_binders subst = function
  | [] -> subst
  | (id,_) :: bl -> cc_cross_binders (List.remove_assoc id subst) bl

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
  | CC_letin (_, _, [id,_], CC_expr c1, e2) ->
      red (cc_subst [id,c1] e2)
  | CC_letin (dep, ty, bl, e1, e2) ->
      begin match red e2 with
	| CC_tuple (false,tl,al) ->
	    if is_eta_redex bl al then
	      red e1
	    else
	      CC_letin (dep, ty, bl, red e1,
			CC_tuple (false,tl,List.map red al))
	| e -> CC_letin (dep, ty, bl, red e1, e)
      end
  | CC_lam (bl, e) ->
      CC_lam (bl, red e)
  | CC_app (e, al) ->
      CC_app (red e, List.map red al)
  | CC_case (ty, e1, el) ->
      CC_case (ty, red e1, List.map red el)
  | CC_tuple (dep, tl, al) ->
      CC_tuple (dep, tl, List.map red al)
  | e -> e


(* How to reduce uncomplete proof terms when they have become constr *)

open Term
open Reductionops

(* Il ne faut pas reduire de redexe (beta/iota) qui impliquerait
 * la substitution d'une métavariable.
 * 
 * On commence par rendre toutes les applications binaire (strong bin_app)
 * puis on applique la reduction spéciale programmes définie dans
 * typing/reduction *)

(*i
let bin_app = function
  | DOPN(AppL,v) as c ->
      (match Array.length v with
	 | 1 -> v.(0)
	 | 2 -> c
	 | n ->
	     let f = DOPN(AppL,Array.sub v 0 (pred n)) in
	     DOPN(AppL,[|f;v.(pred n)|]))
  | c -> c
i*)

let red_cci c = 
  (*i let c = strong bin_app c in i*) 
  strong whd_programs (Global.env ()) Evd.empty c

