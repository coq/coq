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

(* if d=Pos, say if [kn] occurs positively in [c] wrt precedence [prec]
        Neg                     negatively
        Nul              does not occur           *)
let occur env kn =
  let prec = prec env in
  let occkn d kn' = if is_equiv prec kn kn' then d = Pos else true in
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
			      (occkn d kn') & (array_for_all_i f va)
			| _ -> array_for_all (occ Nul) va
		  end
	      | _ -> (occ d f) & (array_for_all (occ Nul) va)
	  end
      | Prod (_,t,b) -> (occ (opp d) t) & (occ d b)
      | Lambda (_,t,b) -> (occ Nul t) & (occ d b)
      | _ -> anomaly "occur"
  in occ
