(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Equality
open Names
open Pp
open Constr
open Termops
open CErrors
open Util
open Mod_subst
open Locus

(* Rewriting rules *)
type rew_rule = { rew_lemma: constr;
                  rew_type: types;
                  rew_pat: constr;
                  rew_ctx: Univ.ContextSet.t;
                  rew_l2r: bool;
                  rew_tac: Genarg.glob_generic_argument option }

let subst_hint subst hint =
  let cst' = subst_mps subst hint.rew_lemma in
  let typ' = subst_mps subst hint.rew_type in
  let pat' = subst_mps subst hint.rew_pat in
  let t' = Option.Smart.map (Genintern.generic_substitute subst) hint.rew_tac in
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
    user_err
      (str "Rewriting base " ++ str bas ++ str " does not exist.")

let find_rewrites bas =
  List.rev_map snd (HintDN.find_all (find_base bas))

let find_matches bas pat =
  let base = find_base bas in
  let res = HintDN.search_pattern base pat in
  List.map snd res

let print_rewrite_hintdb bas =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (str "Database " ++ str bas ++ fnl () ++
           prlist_with_sep fnl
           (fun h ->
             str (if h.rew_l2r then "rewrite -> " else "rewrite <- ") ++
               Printer.pr_lconstr_env env sigma h.rew_lemma ++ str " of type " ++ Printer.pr_lconstr_env env sigma h.rew_type ++
               Option.cata (fun tac -> str " then use tactic " ++
               Pputils.pr_glb_generic env sigma tac) (mt ()) h.rew_tac)
           (find_rewrites bas))

type raw_rew_rule = (constr Univ.in_universe_context_set * bool * Genarg.raw_generic_argument option) CAst.t

(* Applies all the rules of one base *)
let one_base general_rewrite_maybe_in tac_main bas =
  let lrul = find_rewrites bas in
  let try_rewrite dir ctx c tc =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let subst, ctx' = UnivGen.fresh_universe_context_set_instance ctx in
    let c' = Vars.subst_univs_level_constr subst c in
    let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx' in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (general_rewrite_maybe_in dir c' tc)
  end in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
  let lrul = List.map (fun h ->
  let tac = match h.rew_tac with
  | None -> Proofview.tclUNIT ()
  | Some (Genarg.GenArg (Genarg.Glbwit wit, tac)) ->
    let ist = { Geninterp.lfun = Id.Map.empty
              ; poly
              ; extra = Geninterp.TacStore.empty } in
    Ftactic.run (Geninterp.interp wit ist tac) (fun _ -> Proofview.tclUNIT ())
  in
    (h.rew_ctx,h.rew_lemma,h.rew_l2r,tac)) lrul in
    Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS (List.fold_left (fun tac (ctx,csr,dir,tc) ->
      Tacticals.tclTHEN tac
        (Tacticals.tclREPEAT_MAIN
            (Tacticals.tclTHENFIRST (try_rewrite dir ctx csr tc) tac_main)))
      (Proofview.tclUNIT()) lrul))

(* The AutoRewrite tactic *)
let autorewrite ?(conds=Naive) tac_main lbas =
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (List.fold_left (fun tac bas ->
       Tacticals.tclTHEN tac
        (one_base (fun dir c tac ->
          let tac = (tac, conds) in
            general_rewrite ~where:None ~l2r:dir AllOccurrences ~freeze:true ~dep:false ~with_evars:false ~tac (EConstr.of_constr c, Tactypes.NoBindings))
          tac_main bas))
      (Proofview.tclUNIT()) lbas))

let autorewrite_multi_in ?(conds=Naive) idl tac_main lbas =
  Proofview.Goal.enter begin fun gl ->
 (* let's check at once if id exists (to raise the appropriate error) *)
  let _ = List.map (fun id -> Tacmach.pf_get_hyp id gl) idl in
  let general_rewrite_in id dir cstr tac =
    let cstr = EConstr.of_constr cstr in
    general_rewrite ~where:(Some id) ~l2r:dir AllOccurrences ~freeze:true ~dep:false ~with_evars:false ~tac:(tac, conds) (cstr, Tactypes.NoBindings)
  in
 Tacticals.tclMAP (fun id ->
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (List.fold_left (fun tac bas ->
       Tacticals.tclTHEN tac (one_base (general_rewrite_in id) tac_main bas)) (Proofview.tclUNIT()) lbas)))
   idl
 end

let autorewrite_in ?(conds=Naive) id = autorewrite_multi_in ~conds [id]

let gen_auto_multi_rewrite conds tac_main lbas cl =
  let try_do_hyps treat_id l =
    autorewrite_multi_in ~conds (List.map treat_id l) tac_main lbas
  in
  if not (Locusops.is_all_occurrences cl.concl_occs) &&
     cl.concl_occs != NoOccurrences
  then
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str"The \"at\" syntax isn't available yet for the autorewrite tactic.")
  else
    let compose_tac t1 t2 =
      match cl.onhyps with
        | Some [] -> t1
        | _ ->      Tacticals.tclTHENFIRST t1 t2
    in
    compose_tac
        (if cl.concl_occs != NoOccurrences then autorewrite ~conds tac_main lbas else Proofview.tclUNIT ())
        (match cl.onhyps with
           | Some l -> try_do_hyps (fun ((_,id),_) -> id) l
           | None ->
                 (* try to rewrite in all hypothesis
                    (except maybe the rewritten one) *)
               Proofview.Goal.enter begin fun gl ->
                 let ids = Tacmach.pf_ids_of_hyps gl in
                 try_do_hyps (fun id -> id)  ids
               end)

let auto_multi_rewrite ?(conds=Naive) lems cl =
  Proofview.wrap_exceptions (fun () -> gen_auto_multi_rewrite conds (Proofview.tclUNIT()) lems cl)

let auto_multi_rewrite_with ?(conds=Naive) tac_main lbas cl =
  let onconcl = match cl.Locus.concl_occs with NoOccurrences -> false | _ -> true in
  match onconcl,cl.Locus.onhyps with
    | false,Some [_] | true,Some [] | false,Some [] ->
        (* autorewrite with .... in clause using tac n'est sur que
           si clause represente soit le but soit UNE hypothese
        *)
        Proofview.wrap_exceptions (fun () -> gen_auto_multi_rewrite conds tac_main lbas cl)
    | _ ->
      let info = Exninfo.reify () in
      Tacticals.tclZEROMSG ~info
        (strbrk "autorewrite .. in .. using can only be used either with a unique hypothesis or on the conclusion.")

(* Functions necessary to the library object declaration *)
let cache_hintrewrite (rbase,lrl) =
  let base = try raw_find_base rbase with Not_found -> HintDN.empty in
  let max = try fst (Util.List.last (HintDN.find_all base)) with Failure _ -> 0
  in
  let lrl = HintDN.refresh_metas lrl in
  let lrl = HintDN.map (fun (i,h) -> (i + max, h)) lrl in
    rewtab:=String.Map.add rbase (HintDN.union lrl base) !rewtab


let subst_hintrewrite (subst,(rbase,list as node)) =
  let list' = HintDN.subst subst list in
    if list' == list then node else
      (rbase,list')

(* Declaration of the Hint Rewrite library object *)
let inGlobalHintRewrite : string * HintDN.t -> Libobject.obj =
  let open Libobject in
  declare_object @@ superglobal_object_nodischarge "HINT_REWRITE_GLOBAL"
    ~cache:cache_hintrewrite
    ~subst:(Some subst_hintrewrite)

let inExportHintRewrite : string * HintDN.t -> Libobject.obj =
  let open Libobject in
  declare_object @@ global_object_nodischarge ~cat:Hints.hint_cat "HINT_REWRITE_EXPORT"
    ~cache:cache_hintrewrite
    ~subst:(Some subst_hintrewrite)

type hypinfo = {
  hyp_ty : EConstr.types;
  hyp_pat : EConstr.constr;
}

let decompose_applied_relation env sigma c ctype left2right =
  let find_rel ty =
    (* FIXME: this is nonsense, we generate evars and then we drop the
       corresponding evarmap. This sometimes works because [Term_dnet] performs
       evar surgery via [Termops.filtering]. *)
    let sigma, ty = Clenv.make_evar_clause env sigma ty in
    let (_, args) = Termops.decompose_app_vect sigma ty.Clenv.cl_concl in
    let len = Array.length args in
    if 2 <= len then
      let c1 = args.(len - 2) in
      let c2 = args.(len - 1) in
      Some (if left2right then c1 else c2)
    else None
  in
    match find_rel ctype with
    | Some c -> Some { hyp_pat = c; hyp_ty = ctype }
    | None ->
        let ctx,t' = Reductionops.splay_prod_assum env sigma ctype in (* Search for underlying eq *)
        let ctype = it_mkProd_or_LetIn t' ctx in
        match find_rel ctype with
        | Some c -> Some { hyp_pat = c; hyp_ty = ctype }
        | None -> None

let find_applied_relation ?loc env sigma c left2right =
  let ctype = Retyping.get_type_of env sigma (EConstr.of_constr c) in
    match decompose_applied_relation env sigma c ctype left2right with
    | Some c -> c
    | None ->
        user_err ?loc
                    (str"The type" ++ spc () ++ Printer.pr_econstr_env env sigma ctype ++
                       spc () ++ str"of this term does not end with an applied relation.")

let warn_deprecated_hint_rewrite_without_locality =
  CWarnings.create ~name:"deprecated-hint-rewrite-without-locality" ~category:"deprecated"
    (fun () -> strbrk "The default value for rewriting hint locality is currently \
    \"local\" in a section and \"global\" otherwise, but is scheduled to change \
    in a future release. For the time being, adding rewriting hints outside of sections \
    without specifying an explicit locality attribute is therefore deprecated. It is \
    recommended to use \"export\" whenever possible. Use the attributes \
    #[local], #[global] and #[export] depending on your choice. For example: \
    \"#[export] Hint Rewrite foo : bar.\" This is supported since Coq 8.14.")

let default_hint_rewrite_locality () =
  if Global.sections_are_opened () then Hints.Local
  else
    let () = warn_deprecated_hint_rewrite_without_locality () in
    Hints.SuperGlobal

(* To add rewriting rules to a base *)
let add_rew_rules ~locality base lrul =
  let counter = ref 0 in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let ist = Genintern.empty_glob_sign (Global.env ()) in
  let intern tac = snd (Genintern.generic_intern ist tac) in
  let lrul =
    List.fold_left
      (fun dn {CAst.loc;v=((c,ctx),b,t)} ->
        let sigma = Evd.merge_context_set Evd.univ_rigid sigma ctx in
        let info = find_applied_relation ?loc env sigma c b in
        let pat = EConstr.Unsafe.to_constr info.hyp_pat in
        let rul = { rew_lemma = c; rew_type = EConstr.Unsafe.to_constr info.hyp_ty;
                    rew_pat = pat; rew_ctx = ctx; rew_l2r = b;
                    rew_tac = Option.map intern t}
        in incr counter;
          HintDN.add pat (!counter, rul) dn) HintDN.empty lrul
  in
  let open Hints in
  match locality with
  | Local -> cache_hintrewrite (base,lrul)
  | SuperGlobal ->
    let () =
      if Global.sections_are_opened () then
      CErrors.user_err Pp.(str
        "This command does not support the global attribute in sections.");
    in
    Lib.add_leaf (inGlobalHintRewrite (base,lrul))
  | Export ->
    let () =
      if Global.sections_are_opened () then
        CErrors.user_err Pp.(str
          "This command does not support the export attribute in sections.");
    in
    Lib.add_leaf (inExportHintRewrite (base,lrul))
