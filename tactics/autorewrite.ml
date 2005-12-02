(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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
open Mod_subst

(* Rewriting rules *)
(* the type is the statement of the lemma constr. Used to elim duplicates. *)
type rew_rule = constr * types * bool * glob_tactic_expr

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

let print_rewrite_hintdb bas =
 try
  let hints = Stringmap.find bas !rewtab in
   ppnl (str "Database " ++ str bas ++ (Pp.cut ()) ++
    prlist_with_sep Pp.cut
     (fun (c,typ,d,t) ->
       str (if d then "rewrite -> " else "rewrite <- ") ++
       Printer.prterm c ++ str " of type " ++ Printer.prterm typ ++
       str " then use tactic " ++ Pptactic.pr_glob_tactic t) hints)
 with
  Not_found -> 
   errorlabstrm "AutoRewrite" 
     (str ("Rewriting base "^(bas)^" does not exist"))

type raw_rew_rule = constr * bool * raw_tactic_expr

(* Applies all the rules of one base *)
let one_base general_rewrite_maybe_in tac_main bas =
  let lrul = 
    try 
      Stringmap.find bas !rewtab
    with Not_found -> 
      errorlabstrm "AutoRewrite" 
        (str ("Rewriting base "^(bas)^" does not exist"))
  in
  let lrul = List.map (fun (c,_,b,t) -> (c,b,Tacinterp.eval_tactic t)) lrul in
    tclREPEAT_MAIN (tclPROGRESS (List.fold_left (fun tac (csr,dir,tc) ->
      tclTHEN tac
        (tclREPEAT_MAIN 
	  (tclTHENSFIRSTn (general_rewrite_maybe_in dir csr) [|tac_main|] tc)))
      tclIDTAC lrul))

(* The AutoRewrite tactic *)
let autorewrite tac_main lbas =
  tclREPEAT_MAIN (tclPROGRESS
    (List.fold_left (fun tac bas -> 
       tclTHEN tac (one_base general_rewrite tac_main bas)) tclIDTAC lbas))

let autorewrite_in id tac_main lbas gl =
 (* let's check at once if id exists (to raise the appropriate error) *)
 let _ = Tacmach.pf_get_hyp gl id in
 let general_rewrite_in =
  let id = ref id in
  let to_be_cleared = ref false in
   fun dir cstr gl ->
    let last_hyp_id =
     match (Environ.named_context_of_val gl.Evd.it.Evd.evar_hyps) with
        (last_hyp_id,_,_)::_ -> last_hyp_id
      | _ -> (* even the hypothesis id is missing *)
             error ("No such hypothesis : " ^ (string_of_id !id))
    in
    let gl' = general_rewrite_in dir !id cstr gl in
    let gls = (fst gl').Evd.it in
    match gls with
       g::_ ->
        (match Environ.named_context_of_val g.Evd.evar_hyps with
            (lastid,_,_)::_ ->
              if last_hyp_id <> lastid then
               begin
                let gl'' =
                  if !to_be_cleared then
                   tclTHEN (fun _ -> gl') (tclTRY (clear [!id])) gl
                  else gl' in
                id := lastid ;
                to_be_cleared := true ;
                gl''
               end
              else
               begin
                to_be_cleared := false ;
                gl'
               end
          | _ -> assert false) (* there must be at least an hypothesis *)
     | _ -> assert false (* rewriting cannot complete a proof *)
 in
  tclREPEAT_MAIN (tclPROGRESS
    (List.fold_left (fun tac bas -> 
       tclTHEN tac (one_base general_rewrite_in tac_main bas)) tclIDTAC lbas))
   gl

(* Functions necessary to the library object declaration *)
let cache_hintrewrite (_,(rbase,lrl)) =
  let l = 
    try 
      let oldl = Stringmap.find rbase !rewtab in
      let lrl =
       List.map
        (fun (c,dummy,b,t) ->
          (* here we substitute the dummy value with the right one *)
          c,Typing.type_of (Global.env ()) Evd.empty c,b,t) lrl in
      (List.filter
          (fun (_,typ,_,_) ->
            not (List.exists (fun (_,typ',_,_) -> Term.eq_constr typ typ') oldl)
          ) lrl) @ oldl
    with
      | Not_found -> lrl
  in
    rewtab:=Stringmap.add rbase l !rewtab

let export_hintrewrite x = Some x

let subst_hintrewrite (_,subst,(rbase,list as node)) = 
  let subst_first (cst,typ,b,t as pair) = 
    let cst' = subst_mps subst cst in
    let typ' =
     (* here we do not have the environment and Global.env () is not the
        one where cst' lives in. Thus we can just put a dummy value and
        override it in cache_hintrewrite *)
     typ (* dummy value, it will be recomputed by cache_hintrewrite *) in
    let t' = Tacinterp.subst_tactic subst t in
      if cst == cst' && t == t' then pair else
	(cst',typ',b,t)
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
  let lrul =
   List.rev_map
    (fun (c,b,t) ->
      (c,mkProp (* dummy value *), b,Tacinterp.glob_tactic t)
    ) lrul
  in
   Lib.add_anonymous_leaf (in_hintrewrite (base,lrul))
