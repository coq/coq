(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
  ref ((Hashtbl.create 53) : (string,rew_rule) Hashtbl.t)

let _ = 
  let init () = rewtab := (Hashtbl.create 53) in
  let freeze () = !rewtab in
  let unfreeze fs = rewtab := fs in
  Summary.declare_summary "autorewrite"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_section   = false }

(* Rewriting rules before tactic interpretation *)
type raw_rew_rule = constr * bool * raw_tactic_expr

(* Applies all the rules of one base *)
let one_base tac_main bas =
  let lrul = Hashtbl.find_all !rewtab bas in
  if lrul = [] then
    errorlabstrm "AutoRewrite"
      (str ("Rewriting base "^(bas)^" does not exist"))
  else
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
let load_hintrewrite _ = ()
let cache_hintrewrite (_,(rbase,lrl)) =
  List.iter
    (fun (c,b,t) -> Hashtbl.add !rewtab rbase (c,b,Tacinterp.interp t)) lrl
let export_hintrewrite x = Some x

(* Declaration of the Hint Rewrite library object *)
let (in_hintrewrite,out_hintrewrite)=
  Libobject.declare_object
    ("HINT_REWRITE",
     { Libobject.load_function = load_hintrewrite;
       Libobject.open_function = cache_hintrewrite;
       Libobject.cache_function = cache_hintrewrite;
       Libobject.export_function = export_hintrewrite })

(* To add rewriting rules to a base *)
let add_rew_rules base lrul =
  Lib.add_anonymous_leaf (in_hintrewrite (base,lrul))
