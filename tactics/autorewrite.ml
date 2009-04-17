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
type rew_rule = { rew_lemma: constr;
		  rew_type: types;
		  rew_pat: constr;
		  rew_l2r: bool;
		  rew_tac: glob_tactic_expr }

let subst_hint subst hint =
  let cst' = subst_mps subst hint.rew_lemma in
  let typ' = subst_mps subst hint.rew_type in
  let pat' = subst_mps subst hint.rew_pat in
  let t' = Tacinterp.subst_tactic subst hint.rew_tac in
    if hint.rew_lemma == cst' && hint.rew_tac == t' then hint else
      { hint with 
	rew_lemma = cst'; rew_type = typ'; 
	rew_pat = pat';	rew_tac = t' }

module HintIdent = 
struct
  type t = int * rew_rule
  
  let compare (i,t) (i',t') =
    Pervasives.compare i i'
(*     Pervasives.compare t.rew_lemma t'.rew_lemma *)

  let subst s (i,t) = (i,subst_hint s t)

  let constr_of (i,t) = t.rew_pat
end

module HintOpt =
struct
  let reduce c = c
  let direction = true
end

module HintDN = Term_dnet.Make(HintIdent)(HintOpt)

(* Summary and Object declaration *)
let rewtab =
  ref (Stringmap.empty : HintDN.t Stringmap.t)

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

let find_base bas =
 try Stringmap.find bas !rewtab
 with
  Not_found -> 
   errorlabstrm "AutoRewrite" 
     (str ("Rewriting base "^(bas)^" does not exist."))

let find_rewrites bas = 
  List.rev_map snd (HintDN.find_all (find_base bas))

let find_matches bas pat =
  let base = find_base bas in
  let res = HintDN.search_pattern base pat in
    List.map (fun ((_,rew), esubst, subst) -> rew) res

let print_rewrite_hintdb bas =
  ppnl (str "Database " ++ str bas ++ (Pp.cut ()) ++
	   prlist_with_sep Pp.cut
	   (fun h ->
	     str (if h.rew_l2r then "rewrite -> " else "rewrite <- ") ++
	       Printer.pr_lconstr h.rew_lemma ++ str " of type " ++ Printer.pr_lconstr h.rew_type ++
	       str " then use tactic " ++ 
	       Pptactic.pr_glob_tactic (Global.env()) h.rew_tac)
	   (find_rewrites bas))
    
type raw_rew_rule = loc * constr * bool * raw_tactic_expr

(* Applies all the rules of one base *)
let one_base general_rewrite_maybe_in tac_main bas =
  let lrul = find_rewrites bas in
  let lrul = List.map (fun h -> (h.rew_lemma,h.rew_l2r,Tacinterp.eval_tactic h.rew_tac)) lrul in
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
  let base = try find_base rbase with _ -> HintDN.empty in
  let max = try fst (Util.list_last (HintDN.find_all base)) with _ -> 0 in
  let lrl = HintDN.map (fun (i,h) -> (i + max, h)) lrl in
    rewtab:=Stringmap.add rbase (HintDN.union lrl base) !rewtab

let export_hintrewrite x = Some x

let subst_hintrewrite (_,subst,(rbase,list as node)) = 
  let list' = HintDN.subst subst list in
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


open Clenv

type hypinfo = {
  hyp_cl : clausenv;
  hyp_prf : constr;
  hyp_ty : types;
  hyp_car : constr;
  hyp_rel : constr;
  hyp_l2r : bool;
  hyp_left : constr;
  hyp_right : constr;
}

let evd_convertible env evd x y =
  try ignore(Evarconv.the_conv_x env x y evd); true 
  with _ -> false
  
let decompose_applied_relation metas env sigma c ctype left2right =
  let find_rel ty = 
    let eqclause = Clenv.mk_clenv_from_env env sigma None (c,ty) in
    let eqclause = 
      if metas then eqclause
      else clenv_pose_metas_as_evars eqclause (Evd.undefined_metas eqclause.evd)
    in
    let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
    let rec split_last_two = function
      | [c1;c2] -> [],(c1, c2)
      | x::y::z ->
	  let l,res = split_last_two (y::z) in x::l, res
      | _ -> raise Not_found
    in
      try 
	let others,(c1,c2) = split_last_two args in
	let ty1, ty2 = 
	  Typing.mtype_of env eqclause.evd c1, Typing.mtype_of env eqclause.evd c2
	in
	  if not (evd_convertible env eqclause.evd ty1 ty2) then None
	  else
	    Some { hyp_cl=eqclause; hyp_prf=(Clenv.clenv_value eqclause); hyp_ty = ty;
		   hyp_car=ty1; hyp_rel=mkApp (equiv, Array.of_list others);
		   hyp_l2r=left2right; hyp_left=c1; hyp_right=c2; }
      with Not_found -> None
  in
    match find_rel ctype with
    | Some c -> Some c
    | None -> 
	let ctx,t' = Reductionops.splay_prod_assum env sigma ctype in (* Search for underlying eq *)
	match find_rel (it_mkProd_or_LetIn t' ctx) with
	| Some c -> Some c
	| None -> None

let find_applied_relation metas loc env sigma c left2right =
  let ctype = Typing.type_of env sigma c in
    match decompose_applied_relation metas env sigma c ctype left2right with
    | Some c -> c
    | None -> 
	user_err_loc (loc, "decompose_applied_relation", 
		     str"The type" ++ spc () ++ Printer.pr_constr_env env ctype ++
		       spc () ++ str"of this term does not end with an applied relation.")
	
(* To add rewriting rules to a base *)
let add_rew_rules base lrul =
  let counter = ref 0 in
  let lrul =
    List.fold_left
      (fun dn (loc,c,b,t) ->
	let info = find_applied_relation false loc (Global.env ()) Evd.empty c b in
	let pat = if b then info.hyp_left else info.hyp_right in
	let rul = { rew_lemma = c; rew_type = info.hyp_ty;
		    rew_pat = pat; rew_l2r = b;
		    rew_tac = Tacinterp.glob_tactic t}
	in incr counter;
	  HintDN.add pat (!counter, rul) dn) HintDN.empty lrul
  in Lib.add_anonymous_leaf (inHintRewrite (base,lrul))
    
