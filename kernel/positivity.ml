(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Environ
open Util
open Precedence
open Symbol
open Declarations

(* check that no symbol equivalent to [kn] occurs in [c] *)
let const_notin prec kn =
  let rec notin c =
    match kind_of_term c with
      | Const kn' -> not (is_equiv prec kn kn')
      | Evar (_,va) -> array_for_all notin va
      | Cast (c,t) -> notin c & notin t
      | LetIn (_,c,t,b) -> notin c & notin t & notin b
      | Case (_,t,c,va) -> notin t & notin c & array_for_all notin va
      | Fix (_,(_,vt,vc)) | CoFix (_,(_,vt,vc)) ->
	  array_for_all notin vt & array_for_all notin vc
      | App (f,va) -> notin f & array_for_all notin va
      | Lambda (_,t,b) | Prod (_,t,b) -> notin t & notin b
      | _ -> true
  in notin

(* if d=Pos, say if constant [kn] occurs positively in [c]
        Neg                              negatively
        Nul                       does not occur           *)
let occur_const env kn =
  let prec = prec env in
  let occkn d kn' = if is_equiv prec kn kn' then d = Pos else true
  and notin = const_notin prec kn in
  let rec occ d c =
    match kind_of_term c with
      | Const kn' -> occkn d kn'
      | App (f,va) ->
	  begin
	    match kind_of_term f with
	      | Const kn' ->
		  begin
		    let cb = lookup_constant kn' env in
		      match cb.const_symb with
			| Some si ->
			    let f i = occ si.symb_mons.(i) in
			      occkn d kn' & array_for_all_i f va
			| _ -> array_for_all notin va
		  end
	      | _ -> occ d f & array_for_all notin va
	  end
      | Prod (_,t,b) -> occ (opp d) t & occ d b
      | Lambda (_,t,b) -> notin t & occ d b
      | _ -> notin c
  in occ

(* check that no inductive [kn] occurs in [c] *)
let ind_notin kn =
  let rec notin c =
    match kind_of_term c with
      | Ind (kn',_) -> kn <> kn'
      | Evar (_,va) -> array_for_all notin va
      | Cast (c,t) -> notin c & notin t
      | LetIn (_,c,t,b) -> notin c & notin t & notin b
      | Case (_,t,c,va) -> notin t & notin c & array_for_all notin va
      | Fix (_,(_,vt,vc)) | CoFix (_,(_,vt,vc)) ->
	  array_for_all notin vt & array_for_all notin vc
      | App (f,va) -> notin f & array_for_all notin va
      | Lambda (_,t,b) | Prod (_,t,b) -> notin t & notin b
      | _ -> true
  in notin

(* if d=Pos, say if inductive [kn] occurs positively in [c]
        Neg                               negatively
        Nul                        does not occur           *)
let occur_mind env kn =
  let notin = ind_notin kn in
  let rec occ d c =
    match kind_of_term c with
      | Ind (kn',_) -> if kn = kn' then d = Pos else true
      | App (f,va) ->
	  begin
	    match kind_of_term f with
	      | Const kn' ->
		  begin
		    let cb = lookup_constant kn' env in
		      match cb.const_symb with
			| Some si ->
			    let f i = occ si.symb_mons.(i) in
			      array_for_all_i f va
			| _ -> array_for_all notin va
		  end
	      | _ -> occ d f & array_for_all notin va
	  end
      | Prod (_,t,b) -> occ (opp d) t & occ d b
      | Lambda (_,t,b) -> notin t & occ d b
      | _ -> notin c
  in occ
