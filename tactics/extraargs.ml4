(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Pcoq
open Genarg
open Names
open Tacexpr
open Tacinterp

(* Rewriting orientation *)

let _ = Metasyntax.add_token_obj "<-"
let _ = Metasyntax.add_token_obj "->"

let pr_orient _prc _prlc _prt = function
  | true -> Pp.mt ()
  | false -> Pp.str " <-"


ARGUMENT EXTEND orient TYPED AS bool PRINTED BY pr_orient
| [ "->" ] -> [ true ]
| [ "<-" ] -> [ false ]
| [ ] -> [ true ]
END

(* For Setoid rewrite *)
let pr_morphism_signature _ _ _ s =
  spc () ++ Setoid_replace.pr_morphism_signature s

ARGUMENT EXTEND morphism_signature
 TYPED AS morphism_signature
 PRINTED BY pr_morphism_signature
  | [ constr(out) ] -> [ [],out ]
  | [ constr(c) "++>" morphism_signature(s) ] ->
       [ let l,out = s in (Some true,c)::l,out ]
  | [ constr(c) "-->" morphism_signature(s) ] ->
       [ let l,out = s in (Some false,c)::l,out ]
  | [ constr(c) "==>" morphism_signature(s) ] ->
       [ let l,out = s in (None,c)::l,out ]
END

let pr_gen prc _prlc _prtac c = prc c

let pr_rawc _prc _prlc _prtac raw = Printer.pr_rawconstr raw

let interp_raw _ _ (t,_) = t

let glob_raw = Tacinterp.intern_constr

let subst_raw = Tacinterp.subst_rawconstr_and_expr

ARGUMENT EXTEND raw
    TYPED AS rawconstr
    PRINTED BY pr_rawc
     
     INTERPRETED BY interp_raw	
     GLOBALIZED BY glob_raw
     SUBSTITUTED BY subst_raw
     
     RAW_TYPED AS constr_expr
     RAW_PRINTED BY pr_gen
     
     GLOB_TYPED AS rawconstr_and_expr
     GLOB_PRINTED BY pr_gen
  [ lconstr(c) ] -> [ c ]
END

type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = identifier Util.located gen_place
type place = identifier gen_place

let pr_gen_place pr_id = function
    ConclLocation () -> Pp.mt ()
  | HypLocation (id,InHyp) -> str "in " ++ pr_id id
  | HypLocation (id,InHypTypeOnly) -> 
      str "in (Type of " ++ pr_id id ++ str ")"
  | HypLocation (id,InHypValueOnly) -> 
      str "in (Value of " ++ pr_id id ++ str ")"

let pr_loc_place _ _ _ = pr_gen_place (fun (_,id) -> Nameops.pr_id id)
let pr_place _ _ _ = pr_gen_place Nameops.pr_id

let intern_place ist = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (intern_hyp ist id,hl)

let interp_place ist gl = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (interp_hyp ist gl id,hl)

let subst_place subst pl = pl 

ARGUMENT EXTEND hloc
    TYPED AS place
    PRINTED BY pr_place
    INTERPRETED BY interp_place
    GLOBALIZED BY intern_place
    SUBSTITUTED BY subst_place
    RAW_TYPED AS loc_place
    RAW_PRINTED BY pr_loc_place
    GLOB_TYPED AS loc_place
    GLOB_PRINTED BY pr_loc_place
  [ ] -> 
    [ ConclLocation () ]
  |  [ "in" "|-" "*" ] -> 
    [ ConclLocation () ]
| [ "in" ident(id) ] ->
    [ HypLocation ((Util.dummy_loc,id),InHyp) ]
| [ "in" "(" "Type" "of" ident(id) ")" ] -> 
    [ HypLocation ((Util.dummy_loc,id),InHypTypeOnly) ]
| [ "in" "(" "Value" "of" ident(id) ")" ] -> 
    [ HypLocation ((Util.dummy_loc,id),InHypValueOnly) ]
   
 END

