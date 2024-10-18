(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open CErrors
open Util
open Mod_subst
open Locus

(* Rewriting rules *)
type rew_rule = { rew_id : KerName.t;
                  rew_lemma : constr;
                  rew_type: types;
                  rew_pat: constr;
                  rew_ctx: Univ.ContextSet.t;
                  rew_l2r: bool;
                  rew_tac: Genarg.glob_generic_argument option }

module RewRule =
struct
  type t = rew_rule
  let rew_lemma r = (r.rew_ctx, r.rew_lemma)
  let rew_l2r r = r.rew_l2r
  let rew_tac r = r.rew_tac
end

module HintIdent =
struct
  type t = rew_rule

  let compare r1 r2 = KerName.compare r1.rew_id r2.rew_id

  let constr_of t = t.rew_pat
end

(* Representation/approximation of terms to use in the dnet:
 *
 * - no meta or evar (use ['a pattern] for that)
 *
 * - [Rel]s and [Sort]s are not taken into account (that's why we need
 *   a second pass of linear filterin on the results - it's not a perfect
 *   term indexing structure)
 *)

module DTerm =
struct

  type 't t =
    | DRel
    | DSort
    | DRef    of GlobRef.t
    | DProd
    | DLet
    | DLambda
    | DApp
    | DCase   of case_info
    | DFix    of int array * int
    | DCoFix  of int
    | DInt    of Uint63.t
    | DFloat  of Float64.t
    | DString of Pstring.t
    | DArray

  let compare_ci ci1 ci2 =
    let c = Label.compare (MutInd.label @@ fst ci1.ci_ind) (MutInd.label @@ fst ci2.ci_ind) in
    if c = 0 then
      let c = Int.compare ci1.ci_npar ci2.ci_npar in
      if c = 0 then
        let c = Array.compare Int.compare ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls in
        if c = 0 then
          Array.compare Int.compare ci1.ci_cstr_nargs ci2.ci_cstr_nargs
        else c
      else c
    else c

  let compare t1 t2 = match t1, t2 with
  | DRel, DRel -> 0
  | DRel, _ -> -1 | _, DRel -> 1
  | DSort, DSort -> 0
  | DSort, _ -> -1 | _, DSort -> 1
  | DRef gr1, DRef gr2 -> GlobRef.UserOrd.compare gr1 gr2
  | DRef _, _ -> -1 | _, DRef _ -> 1

  | DProd, DProd -> 0
  | DProd, _ -> -1 | _, DProd -> 1

  | DLet, DLet -> 0
  | DLet, _ -> -1 | _, DLet -> 1

  | DLambda, DLambda
  | DApp, DApp -> 0
  | DLambda, _ -> -1 | _, DLambda -> 1
  | DApp, _ -> -1 | _, DApp -> 1

  | DCase ci1, DCase ci2 ->
    compare_ci ci1 ci2
  | DCase _, _ -> -1 | _, DCase _ -> 1

  | DFix (i1, j1), DFix (i2, j2) ->
    let c = Int.compare j1 j2 in
    if c = 0 then
      Array.compare Int.compare i1 i2
    else c
  | DFix _, _ -> -1 | _, DFix _ -> 1

  | DCoFix i1, DCoFix i2 ->
    Int.compare i1 i2
  | DCoFix _, _ -> -1 | _, DCoFix _ -> 1

  | DInt i1, DInt i2 -> Uint63.compare i1 i2

  | DInt _, _ -> -1 | _, DInt _ -> 1

  | DFloat f1, DFloat f2 -> Float64.total_compare f1 f2

  | DFloat _, _ -> -1 | _, DFloat _ -> 1

  | DString s1, DString s2 -> Pstring.compare s1 s2

  | DString _, _ -> -1 | _, DString _ -> 1

  | DArray, DArray -> 1

end

(*
 * Terms discrimination nets
 * Uses the general dnet datatype on DTerm.t
 * (here you can restart reading)
 *)

module HintDN :
sig
  type t
  type ident = HintIdent.t

  val empty : t

  (** [add c i dn] adds the binding [(c,i)] to [dn]. [c] can be a
     closed term or a pattern (with untyped Evars). No Metas accepted *)
  val add : Environ.env -> constr -> ident -> t -> t

  (*
   * High-level primitives describing specific search problems
   *)

  (** [search_pattern dn c] returns all terms/patterns in dn
     matching/matched by c *)
  val search_pattern : Environ.env -> t -> constr -> ident list

  (** [find_all dn] returns all idents contained in dn *)
  val find_all : t -> ident list

end
=
struct
  module Ident = HintIdent
  module PTerm =
  struct
    type t = unit DTerm.t
    let compare = DTerm.compare
  end
  module TDnet = Dn.Make(PTerm)(Ident)

  type t = TDnet.t

  type ident = HintIdent.t

  open DTerm
  open TDnet

  let pat_of_constr env c : (unit DTerm.t * Constr.t list) option =
    let open GlobRef in
    let rec pat_of_constr c = match Constr.kind c with
    | Rel _          -> Some (DRel, [])
    | Sort _         -> Some (DSort, [])
    | Var i          -> Some (DRef (VarRef i), [])
    | Const (c,u)    -> Some (DRef (ConstRef (Environ.QConstant.canonize env c)), [])
    | Ind (i,u)      -> Some (DRef (IndRef (Environ.QInd.canonize env i)), [])
    | Construct (c,u)-> Some (DRef (ConstructRef (Environ.QConstruct.canonize env c)), [])
    | Meta _         -> assert false
    | Evar (i,_)     -> None
    | Case (ci,u1,pms1,(c1,_),_iv,c2,ca)     ->
      let f_ctx (_, p) = p in
      Some (DCase(ci), [f_ctx c1; c2] @ Array.map_to_list f_ctx ca)
    | Fix ((ia,i),(_,ta,ca)) ->
      Some (DFix(ia,i), Array.to_list ta @ Array.to_list ca)
    | CoFix (i,(_,ta,ca))    ->
      Some (DCoFix(i), Array.to_list ta @ Array.to_list ca)
    | Cast (c,_,_)   -> pat_of_constr c
    | Lambda (_,t,c) -> Some (DLambda, [t; c])
    | Prod (_, t, u) -> Some (DProd, [t; u])
    | LetIn (_, c, t, u) -> Some (DLet, [c; t; u])
    | App (f,ca)     ->
      let len = Array.length ca in
      let a = ca.(len - 1) in
      let ca = Array.sub ca 0 (len - 1) in
      Some (DApp, [mkApp (f, ca); a])
    | Proj (p,_,c) ->
      (* UnsafeMonomorphic is fine because the term will only be used
         by pat_of_constr which ignores universes *)
      pat_of_constr (mkApp (UnsafeMonomorphic.mkConst (Projection.constant p), [|c|]))
    | Int i -> Some (DInt i, [])
    | Float f -> Some (DFloat f, [])
    | String s -> Some (DString s, [])
    | Array (_u,t,def,ty) ->
      Some (DArray, Array.to_list t @ [def ; ty])
    in
    pat_of_constr c

  (*
   * Basic primitives
   *)

  let empty = TDnet.empty

  let add env (c:constr) (id:Ident.t) (dn:t) =
    (* We used to consider the types of the product as well, but since the dnet
       is only computing an approximation rectified by [filtering] we do not
       anymore. *)
    let (ctx, c) = Term.decompose_prod_decls c in
    let c = TDnet.pattern (fun c -> pat_of_constr env c) c in
    TDnet.add dn c id

(* App(c,[t1,...tn]) -> ([c,t1,...,tn-1],tn)
   App(c,[||]) -> ([],c) *)
let split_app sigma c = match EConstr.kind sigma c with
    App(c,l) ->
      let len = Array.length l in
      if Int.equal len 0 then ([],c) else
        let last = Array.get l (len-1) in
        let prev = Array.sub l 0 (len-1) in
        c::(Array.to_list prev), last
  | _ -> assert false

exception CannotFilter

let filtering env sigma ctx cv_pb c1 c2 =
  let open EConstr in
  let open Vars in
  let evm = ref Evar.Map.empty in
  let define cv_pb e1 ev c1 =
    try let (e2,c2) = Evar.Map.find ev !evm in
    let shift = e1 - e2 in
    if Termops.constr_cmp env sigma cv_pb c1 (lift shift c2) then () else raise CannotFilter
    with Not_found ->
      evm := Evar.Map.add ev (e1,c1) !evm
  in
  let rec aux ctx cv_pb c1 c2 =
    match EConstr.kind sigma c1, EConstr.kind sigma c2 with
      | App _, App _ ->
        let ((p1,l1),(p2,l2)) = (split_app sigma c1),(split_app sigma c2) in
        let () = aux ctx cv_pb l1 l2 in
        begin match p1, p2 with
        | [], [] -> ()
        | (h1 :: p1), (h2 :: p2) ->
          aux ctx cv_pb (applist (h1, p1)) (applist (h2, p2))
        | _ -> assert false
        end
      | Prod (n,t1,c1), Prod (_,t2,c2) ->
          aux ctx cv_pb t1 t2;
          aux (ctx + 1) cv_pb c1 c2
      | _, Evar (ev,_) -> define cv_pb ctx ev c1
      | Evar (ev,_), _ -> define cv_pb ctx ev c2
      | _ ->
          if Termops.compare_constr_univ env sigma
          (fun pb c1 c2 -> aux ctx pb c1 c2; true) cv_pb c1 c2 then ()
          else raise CannotFilter
          (* TODO: le reste des binders *)
  in
  try let () = aux ctx cv_pb c1 c2 in true with CannotFilter -> false

let align_prod_letin sigma c a =
  let (lc,_) = EConstr.decompose_prod_decls sigma c in
  let (l,a) = EConstr.decompose_prod_decls sigma a in
  let lc = List.length lc in
  let n = List.length l in
  if n < lc then invalid_arg "align_prod_letin";
  let l1 = CList.firstn lc l in
  n - lc, EConstr.it_mkProd_or_LetIn a l1

  let decomp env pat = match pat_of_constr env pat with
  | None -> Dn.Everything
  | Some (lbl, args) -> Dn.Label (lbl, args)

  let search_pattern env dn cpat =
    let _dctx, dpat = Term.decompose_prod_decls cpat in
    let whole_c = EConstr.of_constr cpat in
    List.fold_left
      (fun acc id ->
         let c_id = EConstr.of_constr @@ Ident.constr_of id in
         let (ctx,wc) =
           try align_prod_letin Evd.empty whole_c c_id (* FIXME *)
           with Invalid_argument _ -> 0, c_id in
        if filtering env Evd.empty ctx Conversion.CUMUL whole_c wc then id :: acc
        else acc
      ) (TDnet.lookup dn (fun c -> decomp env c) dpat) []

  let find_all dn = TDnet.lookup dn (fun () -> Everything) ()

end

type rewrite_db = {
  rdb_hintdn : HintDN.t;
  rdb_order : int KNmap.t;
  rdb_maxuid : int;
}

let empty_rewrite_db = {
  rdb_hintdn = HintDN.empty;
  rdb_order = KNmap.empty;
  rdb_maxuid = 0;
}

(* Summary and Object declaration *)
let rewtab =
  Summary.ref (String.Map.empty : rewrite_db String.Map.t) ~name:"autorewrite"

let raw_find_base bas = String.Map.find bas !rewtab

let find_base bas =
  try raw_find_base bas
  with Not_found ->
    user_err
      (str "Rewriting base " ++ str bas ++ str " does not exist.")

let find_rewrites bas =
  let db = find_base bas in
  let sort r1 r2 = Int.compare (KNmap.find r2.rew_id db.rdb_order) (KNmap.find r1.rew_id db.rdb_order) in
  List.sort sort (HintDN.find_all db.rdb_hintdn)

let find_matches env bas pat =
  let base = find_base bas in
  let res = HintDN.search_pattern env base.rdb_hintdn pat in
  let sort r1 r2 = Int.compare (KNmap.find r2.rew_id base.rdb_order) (KNmap.find r1.rew_id base.rdb_order) in
  List.sort sort res

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

let tclMAP_rev f args =
  List.fold_left (fun accu arg -> Tacticals.tclTHEN accu (f arg)) (Proofview.tclUNIT ()) args

(* Applies all the rules of one base *)
let one_base where conds tac_main bas =
  let lrul = find_rewrites bas in
  let rewrite dir c tac =
    let c = (EConstr.of_constr c, Tactypes.NoBindings) in
    general_rewrite ~where ~l2r:dir AllOccurrences ~freeze:true ~dep:false ~with_evars:false ~tac:(tac, conds) c
  in
  let try_rewrite h tc =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let subst, ctx' = UnivGen.fresh_universe_context_set_instance h.rew_ctx in
    let subst = Sorts.QVar.Map.empty, subst in
    let c' = Vars.subst_univs_level_constr subst h.rew_lemma in
    let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx' in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (rewrite h.rew_l2r c' tc)
  end in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (_name, poly) ->
  let eval h =
    let tac = match h.rew_tac with
    | None -> Proofview.tclUNIT ()
    | Some tac ->
      let ist = { Geninterp.lfun = Id.Map.empty
                ; poly
                ; extra = Geninterp.TacStore.empty } in
      Ftactic.run (Geninterp.generic_interp ist tac) (fun _ -> Proofview.tclUNIT ())
    in
    Tacticals.tclREPEAT_MAIN (Tacticals.tclTHENFIRST (try_rewrite h tac) tac_main)
  in
  let lrul = tclMAP_rev eval lrul in
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS lrul)

(* The AutoRewrite tactic *)
let autorewrite ?(conds=Naive) tac_main lbas =
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (tclMAP_rev (fun bas -> (one_base None conds tac_main bas)) lbas))

let autorewrite_multi_in ?(conds=Naive) idl tac_main lbas =
  Proofview.Goal.enter begin fun gl ->
 (* let's check at once if id exists (to raise the appropriate error) *)
  let _ = List.map (fun id -> Tacmach.pf_get_hyp id gl) idl in
 Tacticals.tclMAP (fun id ->
  Tacticals.tclREPEAT_MAIN (Proofview.tclPROGRESS
    (tclMAP_rev (fun bas -> (one_base (Some id) conds tac_main bas)) lbas)))
   idl
 end

let autorewrite_in ?(conds=Naive) id = autorewrite_multi_in ~conds [id]

let gen_auto_multi_rewrite conds tac_main lbas cl =
  let try_do_hyps treat_id l =
    autorewrite_multi_in ~conds (List.map treat_id l) tac_main lbas
  in
  let concl_tac = (if cl.concl_occs != NoOccurrences then autorewrite ~conds tac_main lbas else Proofview.tclUNIT ()) in
  if not (Locusops.is_all_occurrences cl.concl_occs) &&
     cl.concl_occs != NoOccurrences
  then
    let info = Exninfo.reify () in
    Tacticals.tclZEROMSG ~info (str"The \"at\" syntax isn't available yet for the autorewrite tactic.")
  else
    match cl.onhyps with
    | Some [] -> concl_tac
    | Some l -> Tacticals.tclTHENFIRST concl_tac (try_do_hyps (fun ((_,id),_) -> id) l)
    | None ->
      let hyp_tac =
        (* try to rewrite in all hypothesis (except maybe the rewritten one) *)
        Proofview.Goal.enter begin fun gl ->
          let ids = Tacmach.pf_ids_of_hyps gl in
          try_do_hyps (fun id -> id)  ids
        end
      in
      Tacticals.tclTHENFIRST concl_tac hyp_tac

let auto_multi_rewrite ?(conds=Naive) lems cl =
  Proofview.wrap_exceptions (fun () -> gen_auto_multi_rewrite conds (Proofview.tclUNIT()) lems cl)

(* Same hack as auto hints: we generate an essentially unique identifier for
   rewrite hints. *)
let fresh_key =
  let id = Summary.ref ~name:"REWHINT-COUNTER" 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, _) = KerName.repr kn in
    (* We embed the full path of the kernel name in the label so that
       the identifier should be unique. This ensures that including
       two modules together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%i"
      (ModPath.to_string mp) cur)
    in
    KerName.make mp (Label.of_id lbl)

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
  let base = try raw_find_base rbase with Not_found -> empty_rewrite_db in
  let fold accu r = {
    rdb_hintdn = HintDN.add (Global.env ()) r.rew_pat r accu.rdb_hintdn;
    rdb_order = KNmap.add r.rew_id accu.rdb_maxuid accu.rdb_order;
    rdb_maxuid = accu.rdb_maxuid + 1;
  } in
  let base = List.fold_left fold base lrl in
  rewtab := String.Map.add rbase base !rewtab

let subst_hintrewrite (subst,(rbase,list as node)) =
  let subst_hint subst hint =
    let id' = subst_kn subst hint.rew_id in
    let cst' = subst_mps subst hint.rew_lemma in
    let typ' = subst_mps subst hint.rew_type in
    let pat' = subst_mps subst hint.rew_pat in
    let t' = Option.Smart.map (Gensubst.generic_substitute subst) hint.rew_tac in
      if hint.rew_id == id' && hint.rew_lemma == cst' && hint.rew_type == typ' &&
         hint.rew_tac == t' && hint.rew_pat == pat' then hint else
        { hint with
          rew_lemma = cst'; rew_type = typ';
          rew_pat = pat';	rew_tac = t' }
  in
  let list' = List.Smart.map (fun h -> subst_hint subst h) list in
    if list' == list then node else
      (rbase,list')

(* Declaration of the Hint Rewrite library object *)
let inHintRewrite : Libobject.locality * (string * rew_rule list) -> Libobject.obj =
  let open Libobject in
  declare_object @@ object_with_locality "HINT_REWRITE_GLOBAL"
    ~cache:cache_hintrewrite
    ~subst:(Some subst_hintrewrite)
    ~discharge:(fun _ -> assert false)

type hypinfo = {
  hyp_ty : EConstr.types;
  hyp_pat : EConstr.constr;
}

let decompose_applied_relation env sigma c ctype left2right =
  let find_rel ty =
    (* FIXME: this is nonsense, we generate evars and then we drop the
       corresponding evarmap. This sometimes works because [Term_dnet] performs
       evar surgery via [Termops.filtering]. *)
    let sigma, ty = EClause.make_evar_clause env sigma ty in
    let (_, args) = EConstr.decompose_app sigma ty.EClause.cl_concl in
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
        let ctx,t' = Reductionops.whd_decompose_prod_decls env sigma ctype in (* Search for underlying eq *)
        let ctype = EConstr.it_mkProd_or_LetIn t' ctx in
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

(* To add rewriting rules to a base *)
let add_rew_rules ~locality base lrul =
  let () = Locality.check_locality_nodischarge locality in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let ist = Genintern.empty_glob_sign ~strict:true (Global.env ()) in
  let intern tac = snd (Genintern.generic_intern ist tac) in
  let map {CAst.loc;v=((c,ctx),b,t)} =
    let sigma = Evd.merge_context_set Evd.univ_rigid sigma ctx in
    let info = find_applied_relation ?loc env sigma c b in
    let pat = EConstr.Unsafe.to_constr info.hyp_pat in
    let uid = fresh_key () in
    { rew_id = uid; rew_lemma = c; rew_type = EConstr.Unsafe.to_constr info.hyp_ty;
      rew_pat = pat; rew_ctx = ctx; rew_l2r = b;
      rew_tac = Option.map intern t }
  in
  let lrul = List.map map lrul in
  Lib.add_leaf (inHintRewrite (locality,(base,lrul)))
