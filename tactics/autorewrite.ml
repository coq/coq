(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Equality
open Hipattern
open Names
open Pp
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Term
open Termops
open Util
open Rawterm
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
       Printer.pr_lconstr c ++ str " of type " ++ Printer.pr_lconstr typ ++
       str " then use tactic " ++ 
       Pptactic.pr_glob_tactic (Global.env()) t) hints)
 with
  Not_found -> 
   errorlabstrm "AutoRewrite" 
     (str ("Rewriting base "^(bas)^" does not exist."))

type raw_rew_rule = constr * bool * raw_tactic_expr

(* Applies all the rules of one base *)
let one_base general_rewrite_maybe_in tac_main bas =
  let lrul =
    try
      Stringmap.find bas !rewtab
    with Not_found ->
      errorlabstrm "AutoRewrite"
        (str ("Rewriting base "^(bas)^" does not exist."))
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
       tclTHEN tac
        (one_base (fun dir -> general_rewrite dir all_occurrences)
	  tac_main bas))
      tclIDTAC lbas))

let autorewrite_multi_in idl tac_main lbas : tactic =
  fun gl -> 
 (* let's check at once if id exists (to raise the appropriate error) *)
 let _ = List.map (Tacmach.pf_get_hyp gl) idl in
 let general_rewrite_in id =
  let id = ref id in
  let to_be_cleared = ref false in
   fun dir cstr gl ->
    let last_hyp_id =
     match (Environ.named_context_of_val gl.Evd.it.Evd.evar_hyps) with
        (last_hyp_id,_,_)::_ -> last_hyp_id
      | _ -> (* even the hypothesis id is missing *)
             error ("No such hypothesis: " ^ (string_of_id !id) ^".")
    in
    let gl' = general_rewrite_in dir all_occurrences !id cstr false gl in
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
 tclMAP (fun id -> 
  tclREPEAT_MAIN (tclPROGRESS
    (List.fold_left (fun tac bas -> 
       tclTHEN tac (one_base (general_rewrite_in id) tac_main bas)) tclIDTAC lbas)))
   idl gl

let autorewrite_in id = autorewrite_multi_in [id]

let gen_auto_multi_rewrite tac_main lbas cl = 
  let try_do_hyps treat_id l = 
    autorewrite_multi_in (List.map treat_id l) tac_main lbas
  in 
  if cl.concl_occs <> all_occurrences_expr &
     cl.concl_occs <> no_occurrences_expr
  then 
    error "The \"at\" syntax isn't available yet for the autorewrite tactic."
  else 
    let compose_tac t1 t2 = 
      match cl.onhyps with 
	| Some [] -> t1 
	| _ ->      tclTHENFIRST t1 t2
    in
    compose_tac
	(if cl.concl_occs <> no_occurrences_expr then autorewrite tac_main lbas else tclIDTAC)
	(match cl.onhyps with 
	   | Some l -> try_do_hyps (fun ((_,id),_) -> id) l
	   | None -> 
	       fun gl -> 
		 (* try to rewrite in all hypothesis 
		    (except maybe the rewritten one) *)
		 let ids =  Tacmach.pf_ids_of_hyps gl
		 in try_do_hyps (fun id -> id)  ids gl)

let auto_multi_rewrite = gen_auto_multi_rewrite Refiner.tclIDTAC

let auto_multi_rewrite_with tac_main lbas cl gl =
  let onconcl = cl.Tacexpr.concl_occs <> no_occurrences_expr in
  match onconcl,cl.Tacexpr.onhyps with 
    | false,Some [_] | true,Some [] | false,Some [] ->   
	(* autorewrite with .... in clause using tac n'est sur que 
	   si clause represente soit le but soit UNE hypothese 
	*)
	gen_auto_multi_rewrite tac_main  lbas cl gl
    | _ -> 
	    Util.errorlabstrm "autorewrite" 
	      (strbrk "autorewrite .. in .. using can only be used either with a unique hypothesis or on the conclusion.")


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
	(cst',typ',b,t')
  in
  let list' = list_smartmap subst_first list in
    if list' == list then node else
      (rbase,list')
      
let classify_hintrewrite (_,x) = Libobject.Substitute x


(* Declaration of the Hint Rewrite library object *)
let (inHintRewrite,_)=
  Libobject.declare_object {(Libobject.default_object "HINT_REWRITE") with
       Libobject.cache_function = cache_hintrewrite;
       Libobject.load_function = (fun _ -> cache_hintrewrite);
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
   Lib.add_anonymous_leaf (inHintRewrite (base,lrul))
