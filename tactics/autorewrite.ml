(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ast
open Coqast
open Equality
open Hipattern
open Names
open Pp
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Term
open Util
open Vernacinterp
open Tacexpr

(* Rewriting rules *)
type rew_rule = constr * bool * tactic

(* Summary and Object declaration *)
let rewtab =
  ref (Stringmap.empty : rew_rule list Stringmap.t)

let _ = 
  let init () = rewtab := Stringmap.empty in
  let freeze () = !rewtab in
  let unfreeze fs = rewtab := fs in
  Summary.declare_summary "autorewrite"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_module = false;
      Summary.survive_section   = false }

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = constr * bool * raw_tactic_expr

(* Applies all the rules of one base *)
let one_base tac_main bas =
  let lrul = 
    try 
      Stringmap.find bas !rewtab
    with Not_found -> 
      errorlabstrm "AutoRewrite" 
        (str ("Rewriting base "^(bas)^" does not exist"))
  in
    tclREPEAT_MAIN (tclPROGRESS (List.fold_left (fun tac (csr,dir,tc) ->
      tclTHEN tac
        (tclREPEAT_MAIN 
	  (tclTHENSFIRSTn (general_rewrite dir csr) [|tac_main|] tc)))
      tclIDTAC lrul))

(* The AutoRewrite tactic *)
let autorewrite tac_main lbas =
  tclREPEAT_MAIN (tclPROGRESS
    (List.fold_left (fun tac bas -> 
       tclTHEN tac (one_base tac_main bas)) tclIDTAC lbas))

(* Functions necessary to the library object declaration *)
let cache_hintrewrite (_,(rbase,lrl)) =
  let l = List.rev_map (fun (c,b,t) -> (c,b,Tacinterp.eval_tactic t)) lrl in
  let l = 
    try 
      List.rev_append l (Stringmap.find rbase !rewtab) 
    with
      | Not_found -> List.rev l
  in
    rewtab:=Stringmap.add rbase l !rewtab

let export_hintrewrite x = Some x

let subst_hintrewrite (_,subst,(rbase,list as node)) = 
  let subst_first (cst,b,t as pair) = 
    let cst' = Term.subst_mps subst cst in
    let t' = Tacinterp.subst_tactic subst t in
      if cst == cst' & t == t' then pair else
	(cst',b,t)
  in
  let list' = list_smartmap subst_first list in
    if list' == list then node else
      (rbase,list')
      
let classify_hintrewrite (_,x) = Libobject.Substitute x


(* Declaration of the Hint Rewrite library object *)
let (in_hintrewrite,out_hintrewrite)=
  Libobject.declare_object {(Libobject.default_object "HINT_REWRITE") with
       Libobject.open_function = (fun i o -> if i=1 then cache_hintrewrite o);
       Libobject.cache_function = cache_hintrewrite;
       Libobject.subst_function = subst_hintrewrite;
       Libobject.classify_function = classify_hintrewrite;
       Libobject.export_function = export_hintrewrite }

(* To add rewriting rules to a base *)
let add_rew_rules base lrul =
  let lrul = List.rev_map (fun (c,b,t) -> (c,b,Tacinterp.glob_tactic t)) lrul in
  Lib.add_anonymous_leaf (in_hintrewrite (base,lrul))
