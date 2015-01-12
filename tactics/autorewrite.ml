(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Equality
open Names
open Pp
open Tacticals
open Tactics
open Term
open Termops
open Errors
open Util
open Tacexpr
open Mod_subst
open Locus

(* Rewriting rules *)
type rew_rule = { rew_lemma: constr;
		  rew_type: types;
		  rew_pat: constr;
		  rew_ctx: Univ.universe_context_set;
		  rew_l2r: bool;
		  rew_tac: glob_tactic_expr option }

let subst_hint subst hint =
  let cst' = subst_mps subst hint.rew_lemma in
  let typ' = subst_mps subst hint.rew_type in
  let pat' = subst_mps subst hint.rew_pat in
  let t' = Option.smartmap (Tacsubst.subst_tactic subst) hint.rew_tac in
    if hint.rew_lemma == cst' && hint.rew_type == typ' && hint.rew_tac == t' then hint else
      { hint with
	rew_lemma = cst'; rew_type = typ';
	rew_pat = pat';	rew_tac = t' }

module HintIdent =
struct
  type t = int * rew_rule

  let compare (i, t) (j, t') = i - j

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
  Summary.ref (String.Map.empty : HintDN.t String.Map.t) ~name:"autorewrite"

let raw_find_base bas = String.Map.find bas !rewtab

let find_base bas =
  try raw_find_base bas
  with Not_found ->
    errorlabstrm "AutoRewrite"
      (str ("Rewriting base "^(bas)^" does not exist."))

let find_rewrites bas =
  List.rev_map snd (HintDN.find_all (find_base bas))

let find_matches bas pat =
  let base = find_base bas in
  let res = HintDN.search_pattern base pat in
  List.map snd res

let print_rewrite_hintdb bas =
  (str "Database " ++ str bas ++ fnl () ++
	   prlist_with_sep fnl
	   (fun h ->
	     str (if h.rew_l2r then "rewrite -> " else "rewrite <- ") ++
	       Printer.pr_lconstr h.rew_lemma ++ str " of type " ++ Printer.pr_lconstr h.rew_type ++
	       Option.cata (fun tac -> str " then use tactic " ++
	       Pptactic.pr_glob_tactic (Global.env()) tac) (mt ()) h.rew_tac)
	   (find_rewrites bas))

type raw_rew_rule = Loc.t * constr Univ.in_universe_context_set * bool * raw_tactic_expr option

(* Applies all the rules of one base *)
let one_base general_rewrite_maybe_in tac_main bas =
  let lrul = find_rewrites bas in
  let try_rewrite dir ctx c tc = Proofview.Goal.nf_enter (fun gl ->
    let subst, ctx' = Universes.fresh_universe_context_set_instance ctx in
    let c' = Vars.subst_univs_level_constr subst c in
    let sigma = Proofview.Goal.sigma gl in
    let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx' in
    Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (general_rewrite_maybe_in dir c' tc)
  ) in
  let lrul = List.map (fun h -> 
  let tac = match h.rew_tac with None -> Proofview.tclUNIT () | Some t -> Tacinterp.eval_tactic t in
    (h.rew_ctx,h.rew_lemma,h.rew_l2r,tac)) lrul in
    Tacticals.New.tclREPEAT_MAIN (Proofview.tclPROGRESS (List.fold_left (fun tac (ctx,csr,dir,tc) ->
      Tacticals.New.tclTHEN tac
        (Tacticals.New.tclREPEAT_MAIN
	    (Tacticals.New.tclTHENFIRST (try_rewrite dir ctx csr tc) tac_main)))
      (Proofview.tclUNIT()) lrul))

(* The AutoRewrite tactic *)
let autorewrite ?(conds=Naive) tac_main lbas =
  Tacticals.New.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (List.fold_left (fun tac bas ->
       Tacticals.New.tclTHEN tac
        (one_base (fun dir c tac ->
	  let tac = (tac, conds) in
	    general_rewrite dir AllOccurrences true false ~tac c)
	  tac_main bas))
      (Proofview.tclUNIT()) lbas))

let autorewrite_multi_in ?(conds=Naive) idl tac_main lbas =
 Proofview.Goal.nf_enter begin fun gl ->
 (* let's check at once if id exists (to raise the appropriate error) *)
 let _ = List.map (fun id -> Tacmach.New.pf_get_hyp id gl) idl in
 let general_rewrite_in id =
  let id = ref id in
  let to_be_cleared = ref false in
   fun dir cstr tac gl ->
    let last_hyp_id =
     match Tacmach.pf_hyps gl with
        (last_hyp_id,_,_)::_ -> last_hyp_id
      | _ -> (* even the hypothesis id is missing *)
        raise (Logic.RefinerError (Logic.NoSuchHyp !id))
    in
    let gl' = Proofview.V82.of_tactic (general_rewrite_in dir AllOccurrences true ~tac:(tac, conds) false !id cstr false) gl in
    let gls = gl'.Evd.it in
    match gls with
       g::_ ->
        (match Environ.named_context_of_val (Goal.V82.hyps gl'.Evd.sigma g) with
            (lastid,_,_)::_ ->
              if not (Id.equal last_hyp_id lastid) then
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
 let general_rewrite_in x y z w = Proofview.V82.tactic (general_rewrite_in x y z w) in
 Tacticals.New.tclMAP (fun id ->
  Tacticals.New.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (List.fold_left (fun tac bas ->
       Tacticals.New.tclTHEN tac (one_base (general_rewrite_in id) tac_main bas)) (Proofview.tclUNIT()) lbas)))
   idl
 end

let autorewrite_in ?(conds=Naive) id = autorewrite_multi_in ~conds [id]

let gen_auto_multi_rewrite conds tac_main lbas cl =
  let try_do_hyps treat_id l =
    autorewrite_multi_in ~conds (List.map treat_id l) tac_main lbas
  in
  if cl.concl_occs != AllOccurrences &&
     cl.concl_occs != NoOccurrences
  then
    Proofview.tclZERO (UserError("" , str"The \"at\" syntax isn't available yet for the autorewrite tactic."))
  else
    let compose_tac t1 t2 =
      match cl.onhyps with
	| Some [] -> t1
	| _ ->      Tacticals.New.tclTHENFIRST t1 t2
    in
    compose_tac
	(if cl.concl_occs != NoOccurrences then autorewrite ~conds tac_main lbas else Proofview.tclUNIT ())
	(match cl.onhyps with
	   | Some l -> try_do_hyps (fun ((_,id),_) -> id) l
	   | None ->
		 (* try to rewrite in all hypothesis
		    (except maybe the rewritten one) *)
               Proofview.Goal.nf_enter begin fun gl ->
                 let ids = Tacmach.New.pf_ids_of_hyps gl in
		 try_do_hyps (fun id -> id)  ids
               end)

let auto_multi_rewrite ?(conds=Naive) = gen_auto_multi_rewrite conds (Proofview.tclUNIT())

let auto_multi_rewrite_with ?(conds=Naive) tac_main lbas cl =
  let onconcl = match cl.Locus.concl_occs with NoOccurrences -> false | _ -> true in
  match onconcl,cl.Locus.onhyps with
    | false,Some [_] | true,Some [] | false,Some [] ->
	(* autorewrite with .... in clause using tac n'est sur que
	   si clause represente soit le but soit UNE hypothese
	*)
	gen_auto_multi_rewrite conds tac_main lbas cl
    | _ ->
        Proofview.tclZERO (UserError ("autorewrite",strbrk "autorewrite .. in .. using can only be used either with a unique hypothesis or on the conclusion."))

(* Functions necessary to the library object declaration *)
let cache_hintrewrite (_,(rbase,lrl)) =
  let base = try raw_find_base rbase with Not_found -> HintDN.empty in
  let max = try fst (Util.List.last (HintDN.find_all base)) with Failure _ -> 0
  in
  let lrl = HintDN.map (fun (i,h) -> (i + max, h)) lrl in
    rewtab:=String.Map.add rbase (HintDN.union lrl base) !rewtab


let subst_hintrewrite (subst,(rbase,list as node)) =
  let list' = HintDN.subst subst list in
    if list' == list then node else
      (rbase,list')

let classify_hintrewrite x = Libobject.Substitute x


(* Declaration of the Hint Rewrite library object *)
let inHintRewrite : string * HintDN.t -> Libobject.obj =
  Libobject.declare_object {(Libobject.default_object "HINT_REWRITE") with
    Libobject.cache_function = cache_hintrewrite;
    Libobject.load_function = (fun _ -> cache_hintrewrite);
    Libobject.subst_function = subst_hintrewrite;
    Libobject.classify_function = classify_hintrewrite }


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
	  Typing.type_of env eqclause.evd c1, Typing.type_of env eqclause.evd c2
	in
(* 	  if not (evd_convertible env eqclause.evd ty1 ty2) then None *)
(* 	  else *)
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
		     str"The type" ++ spc () ++ Printer.pr_constr_env env sigma ctype ++
		       spc () ++ str"of this term does not end with an applied relation.")

(* To add rewriting rules to a base *)
let add_rew_rules base lrul =
  let counter = ref 0 in
  let lrul =
    List.fold_left
      (fun dn (loc,(c,ctx),b,t) ->
	let info = find_applied_relation false loc (Global.env ()) Evd.empty c b in
	let pat = if b then info.hyp_left else info.hyp_right in
	let rul = { rew_lemma = c; rew_type = info.hyp_ty;
		    rew_pat = pat; rew_ctx = ctx; rew_l2r = b;
		    rew_tac = Option.map Tacintern.glob_tactic t}
	in incr counter;
	  HintDN.add pat (!counter, rul) dn) HintDN.empty lrul
  in Lib.add_anonymous_leaf (inHintRewrite (base,lrul))

