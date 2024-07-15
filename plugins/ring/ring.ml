(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars
open Ltac_plugin
open Pp
open Util
open Names
open Constr
open EConstr
open Vars
open CClosure
open Environ
open Glob_term
open Locus
open Tacexpr
open Coqlib
open Mod_subst
open Tacinterp
open Libobject
open Printer
open Declare
open Ring_ast
open Proofview.Notations

let error msg = CErrors.user_err Pp.(str msg)

(****************************************************************************)
(* controlled reduction *)

type protect_flag = Eval|Prot|Rec

type protection = Environ.env -> Evd.evar_map -> EConstr.t -> GlobRef.t -> (Int.t -> protect_flag) option

let global_head_of_constr sigma c =
  let f, args = decompose_app sigma c in
    try fst (EConstr.destRef sigma f)
    with DestKO -> CErrors.anomaly (str "global_head_of_constr.")

let global_of_constr_nofail sigma c =
  try fst @@ EConstr.destRef sigma c
  with DestKO -> GlobRef.VarRef (Id.of_string "dummy")

let mk_atom c = CClosure.mk_atom (EConstr.Unsafe.to_constr c)

let rec mk_clos_but sigma f_map n t =
  let (f, args) = EConstr.decompose_app sigma t in
  match f_map (global_of_constr_nofail sigma f) with
  | Some tag ->
      let map i t = tag_arg sigma f_map n (tag i) t in
      if Array.is_empty args then map (-1) f
      else mk_red (FApp (map (-1) f, Array.mapi map args))
  | None -> mk_atom t

and tag_arg sigma f_map n tag c = match tag with
| Eval -> mk_clos (Esubst.subs_id n, UVars.Instance.empty) (EConstr.Unsafe.to_constr c)
| Prot -> mk_atom c
| Rec -> mk_clos_but sigma f_map n c

let interp_map env l t =
  let eq g1 g2 = QGlobRef.equal env g1 g2 in
  try Some (List.assoc_f eq t l) with Not_found -> None

let protect_maps : protection String.Map.t ref = ref String.Map.empty
let add_map s m = protect_maps := String.Map.add s m !protect_maps
let lookup_map map =
  try String.Map.find map !protect_maps
  with Not_found ->
    CErrors.user_err (str "Map " ++ qs map ++ str "not found.")

let protect_red map env sigma c =
  let tab = create_tab () in
  let infos = Evarutil.create_clos_infos env sigma RedFlags.all in
  let map = lookup_map map env sigma c in
  let rec eval n c = match EConstr.kind sigma c with
  | Prod (na, t, u) -> EConstr.mkProd (na, eval n t, eval (n + 1) u)
  | _ -> EConstr.of_constr @@ norm_val infos tab (mk_clos_but sigma map n c)
  in
  eval 0 c

let protect_tac map =
  Tactics.reduct_option ~check:false (protect_red map,DEFAULTcast) None

let protect_tac_in map id =
  Tactics.reduct_option ~check:false (protect_red map,DEFAULTcast) (Some(id, Locus.InHyp))


(****************************************************************************)

let rec closed_under sigma cset t =
  try
    let (gr, _) = destRef sigma t in
    GlobRef.Set_env.mem gr cset
  with DestKO ->
    match EConstr.kind sigma t with
    | Cast(c,_,_) -> closed_under sigma cset c
    | App(f,l) -> closed_under sigma cset f && Array.for_all (closed_under sigma cset) l
    | _ -> false

let closed_term args _ = match args with
| [t; l] ->
  let t = Option.get (Value.to_constr t) in
  let l = List.map (fun c -> Value.cast (Genarg.topwit Stdarg.wit_ref) c) (Option.get (Value.to_list l)) in
  Proofview.tclEVARMAP >>= fun sigma ->
  let cs = List.fold_right GlobRef.Set_env.add l GlobRef.Set_env.empty in
  if closed_under sigma cs t then Proofview.tclUNIT () else Tacticals.tclFAIL (mt())
| _ -> assert false

let closed_term_ast =
  let tacname = {
    mltac_plugin = "coq-core.plugins.ring";
    mltac_tactic = "closed_term";
  } in
  let () = Tacenv.register_ml_tactic tacname [|closed_term|] in
  let tacname = {
    mltac_name = tacname;
    mltac_index = 0;
  } in
  fun l ->
  let l = List.map (fun gr -> ArgArg(Loc.tag gr)) l in
  CAst.make (TacFun
    ([Name(Id.of_string"t")],
    CAst.make (TacML (tacname,
    [TacGeneric (None, Genarg.in_gen (Genarg.glbwit Stdarg.wit_constr) (DAst.make @@ GVar(Id.of_string"t"),None));
     TacGeneric (None, Genarg.in_gen (Genarg.glbwit (Genarg.wit_list Stdarg.wit_ref)) l)]))))
(*
let _ = add_tacdef false ((Loc.ghost,Id.of_string"ring_closed_term"
*)

(****************************************************************************)

let ic env sigma c =
  let c, uctx = Constrintern.interp_constr env sigma c in
  (Evd.from_ctx uctx, c)

let ic_unsafe env sigma c = (*FIXME remove *)
  fst (Constrintern.interp_constr env sigma c)

let decl_constant name univs c =
  let open Constr in
  let vars = CVars.universes_of_constr c in
  let univs = UState.restrict_universe_context univs vars in
  let () = Global.push_context_set ~strict:true univs in
  let types = (Typeops.infer (Global.env ()) c).uj_type in
  let univs = UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders in
  (* UnsafeMonomorphic: we always do poly:false *)
  UnsafeMonomorphic.mkConst
    (declare_constant ~name
       ~kind:Decls.(IsProof Lemma)
       (DefinitionEntry (definition_entry ~opaque:true ~types ~univs c)))

let decl_constant na suff univs c =
  let na = Namegen.next_global_ident_away (Nameops.add_suffix na suff) Id.Set.empty in
  decl_constant na univs c

(* Calling a global tactic *)
let ltac_call tac (args:glob_tactic_arg list) =
  CAst.make @@ TacArg (TacCall (CAst.make (ArgArg(Loc.tag @@ Lazy.force tac),args)))

let constr_of sigma v = match Value.to_constr v with
  | Some c -> EConstr.to_constr sigma c
  | None -> failwith "Ring.exec_tactic: anomaly"

let tactic_res = ref [||]

let get_res =
  let open Tacexpr in
  let name = { mltac_plugin = "coq-core.plugins.ring"; mltac_tactic = "get_res"; } in
  let entry = { mltac_name = name; mltac_index = 0 } in
  let tac args ist =
    let n = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_int) (List.hd args) in
    let init i = Id.Map.find (Id.of_string ("x" ^ string_of_int i)) ist.lfun in
    tactic_res := Array.init n init;
    Proofview.tclUNIT ()
  in
  Tacenv.register_ml_tactic name [| tac |];
  entry

let exec_tactic env sigma n f args =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar CAst.(make id)) in
    (succ i, x :: vars, Id.Map.add id (Value.of_constr arg) lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  (* Build the getter *)
  let lid = List.init n (fun i -> Id.of_string("x"^string_of_int i)) in
  let n = Genarg.in_gen (Genarg.glbwit Stdarg.wit_int) n in
  let get_res = CAst.make (TacML (get_res, [TacGeneric (None, n)])) in
  let getter = Tacexp (CAst.make (TacFun (List.map (fun n -> Name n) lid, get_res))) in
  (* Evaluate the whole result *)
  let _, pv = Proofview.init sigma [env, EConstr.mkProp] in
  let tac = Tacinterp.eval_tactic_ist ist (ltac_call f (args@[getter])) in
  let ((), pv, _, _) = Proofview.apply ~name:(Id.of_string "ring") ~poly:false (Global.env ()) tac pv in
  let sigma = Evd.minimize_universes (Proofview.return pv) in
  let nf c = constr_of sigma c in
  Array.map nf !tactic_res, Evd.universe_context_set sigma

let gen_constant n = lazy (EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref n)))
let gen_reference n = lazy (Coqlib.lib_ref n)

let coq_mk_Setoid = gen_constant "plugins.ring.Build_Setoid_Theory"
let coq_None = gen_reference "core.option.None"
let coq_Some = gen_reference "core.option.Some"
let coq_eq = gen_constant "core.eq.type"

let coq_cons = gen_reference "core.list.cons"
let coq_nil = gen_reference "core.list.nil"

let lapp f args = mkApp(Lazy.force f,args)

let plapp sigma f args =
  let sigma, fc = Evd.fresh_global (Global.env ()) sigma (Lazy.force f) in
  sigma, mkApp(fc,args)

let dest_rel0 sigma t =
  match EConstr.kind sigma t with
  | App(f,args) when Array.length args >= 2 ->
      let rel = mkApp(f,Array.sub args 0 (Array.length args - 2)) in
      if closed0 sigma rel then
        (rel,args.(Array.length args - 2),args.(Array.length args - 1))
      else error "ring: cannot find relation (not closed)"
  | _ -> error "ring: cannot find relation"

let rec dest_rel sigma t =
  match EConstr.kind sigma t with
  | Prod(_,_,c) -> dest_rel sigma c
  | _ -> dest_rel0 sigma t

(****************************************************************************)
(* Library linking *)

let plugin_dir = "setoid_ring"

let cdir = ["Stdlib";plugin_dir]
let plugin_modules =
  List.map (fun d -> cdir@d)
    [["Ring_theory"];["Ring_polynom"]; ["Ring_tac"];["InitialRing"];
     ["Field_tac"]; ["Field_theory"]
    ]

let my_constant c =
  lazy (EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) @@ Coqlib.gen_reference_in_modules "Ring" plugin_modules c))
    [@@ocaml.warning "-3"]
let my_reference c =
  lazy (Coqlib.gen_reference_in_modules "Ring" plugin_modules c)
    [@@ocaml.warning "-3"]

let znew_ring_path =
  DirPath.make (List.map Id.of_string ["InitialRing";plugin_dir;"Stdlib"])
let zltac s =
  lazy(KerName.make (ModPath.MPfile znew_ring_path) (Label.make s))

let mk_cst l s = lazy (Coqlib.coq_reference "ring" l s) [@@ocaml.warning "-3"]
let pol_cst s = mk_cst [plugin_dir;"Ring_polynom"] s

(* Ring theory *)

(* almost_ring defs *)
let coq_almost_ring_theory = my_constant "almost_ring_theory"

(* setoid and morphism utilities *)
let coq_eq_setoid = my_reference "Eqsth"
let coq_eq_morph = my_reference "Eq_ext"
let coq_eq_smorph = my_reference "Eq_s_ext"

(* ring -> almost_ring utilities *)
let coq_ring_theory = my_constant "ring_theory"
let coq_mk_reqe = my_constant "mk_reqe"

(* semi_ring -> almost_ring utilities *)
let coq_semi_ring_theory = my_constant "semi_ring_theory"
let coq_mk_seqe = my_constant "mk_seqe"

let coq_abstract = my_constant"Abstract"
let coq_comp = my_constant"Computational"
let coq_morph = my_constant"Morphism"

(* power function *)
let ltac_inv_morph_nothing = zltac"inv_morph_nothing"

(* hypothesis *)
let coq_mkhypo = my_reference "mkhypo"
let coq_hypo = my_reference "hypo"

(* Equality: do not evaluate but make recursive call on both sides *)
let map_with_eq arg_map env sigma c =
  let (req,_,_) = dest_rel sigma c in
  interp_map env
    ((global_head_of_constr sigma req,(function -1->Prot|_->Rec))::
    List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)

let map_without_eq arg_map env _ _ =
  interp_map env (List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)

let _ = add_map "ring"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    my_reference "IDphi", (function _->Eval);
    my_reference "gen_phiZ", (function _->Eval);
    (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
    pol_cst "Pphi_dev", (function -1|8|9|10|12|14->Eval|11|13->Rec|_->Prot);
    pol_cst "Pphi_pow",
          (function -1|8|9|10|13|15|17->Eval|11|16->Rec|_->Prot);
    (* PEeval: evaluate polynomial, protect ring
       operations and make recursive call on the var map *)
    pol_cst "PEeval", (function -1|10|13->Eval|8|12->Rec|_->Prot)])

(****************************************************************************)
(* Ring database *)

module Cmap = Map.Make(Constr)

let from_carrier = Summary.ref Cmap.empty ~name:"ring-tac-carrier-table"

let print_rings () =
  Feedback.msg_notice (strbrk "The following ring structures have been declared:");
  Cmap.iter (fun _carrier ring ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Feedback.msg_notice
        (hov 2
           (Ppconstr.pr_id ring.ring_name ++ spc() ++
            str"with carrier "++ pr_constr_env env sigma ring.ring_carrier++spc()++
            str"and equivalence relation "++ pr_constr_env env sigma ring.ring_req))
    ) !from_carrier

let ring_for_carrier r = Cmap.find r !from_carrier

let find_ring_structure env sigma l =
  match l with
    | t::cl' ->
        let ty = Retyping.get_type_of env sigma t in
        let check c =
          let ty' = Retyping.get_type_of env sigma c in
          if not (Reductionops.is_conv env sigma ty ty') then
            CErrors.user_err
              (str"Arguments of ring_simplify do not have all the same type.")
        in
        List.iter check cl';
        (try ring_for_carrier (EConstr.to_constr ~abort_on_undefined_evars:false sigma ty)
        with Not_found ->
          CErrors.user_err
            (str"Cannot find a declared ring structure over"++
             spc() ++ str"\"" ++ pr_econstr_env env sigma ty ++ str"\"."))
    | [] -> assert false

let add_entry e =
  from_carrier := Cmap.add e.ring_carrier e !from_carrier

let subst_th (subst,th) =
  let c' = subst_mps subst th.ring_carrier in
  let eq' = subst_mps subst th.ring_req in
  let set' = subst_mps subst th.ring_setoid in
  let ext' = subst_mps subst th.ring_ext in
  let morph' = subst_mps subst th.ring_morph in
  let th' = subst_mps subst th.ring_th in
  let thm1' = subst_mps subst th.ring_lemma1 in
  let thm2' = subst_mps subst th.ring_lemma2 in
  let tac'= Tacsubst.subst_tactic subst th.ring_cst_tac in
  let pow_tac'= Tacsubst.subst_tactic subst th.ring_pow_tac in
  let pretac'= Tacsubst.subst_tactic subst th.ring_pre_tac in
  let posttac'= Tacsubst.subst_tactic subst th.ring_post_tac in
  if c' == th.ring_carrier &&
     eq' == th.ring_req &&
     Constr.equal set' th.ring_setoid &&
     ext' == th.ring_ext &&
     morph' == th.ring_morph &&
     th' == th.ring_th &&
     thm1' == th.ring_lemma1 &&
     thm2' == th.ring_lemma2 &&
     tac' == th.ring_cst_tac &&
     pow_tac' == th.ring_pow_tac &&
     pretac' == th.ring_pre_tac &&
     posttac' == th.ring_post_tac then th
  else
    { ring_name = th.ring_name;
      ring_carrier = c';
      ring_req = eq';
      ring_setoid = set';
      ring_ext = ext';
      ring_morph = morph';
      ring_th = th';
      ring_cst_tac = tac';
      ring_pow_tac = pow_tac';
      ring_lemma1 = thm1';
      ring_lemma2 = thm2';
      ring_pre_tac = pretac';
      ring_post_tac = posttac' }


let theory_to_obj : ring_info -> obj =
  declare_object @@ global_object_nodischarge "tactic-new-ring-theory"
    ~cache:add_entry
    ~subst:(Some subst_th)

let setoid_of_relation env sigma a r =
  try
    let sigma, refl = Rewrite.get_reflexive_proof env sigma a r in
    let sigma, sym = Rewrite.get_symmetric_proof env sigma a r in
    let sigma, trans = Rewrite.get_transitive_proof env sigma a r in
    sigma, lapp coq_mk_Setoid [|a ; r ; refl; sym; trans |]
  with Not_found ->
    CErrors.user_err (str "Cannot find a setoid structure for relation " ++ pr_econstr_env env sigma r ++ str ".")

let op_morph r add mul opp req m1 m2 m3 =
  lapp coq_mk_reqe [| r; add; mul; opp; req; m1; m2; m3 |]

let op_smorph r add mul req m1 m2 =
  lapp coq_mk_seqe [| r; add; mul; req; m1; m2 |]

let ring_equality env sigma (r,add,mul,opp,req) =
  match EConstr.kind sigma req with
    | App (f, [| _ |]) when eq_constr_nounivs sigma f (Lazy.force coq_eq) ->
        let sigma, setoid = plapp sigma coq_eq_setoid [|r|] in
        let sigma, op_morph =
          match opp with
              Some opp -> plapp sigma coq_eq_morph [|r;add;mul;opp|]
          | None -> plapp sigma coq_eq_smorph [|r;add;mul|] in
        let sigma, setoid = Typing.solve_evars env sigma setoid in
        let sigma, op_morph = Typing.solve_evars env sigma op_morph in
        (setoid,op_morph)
    | _ ->
        let sigma, setoid = setoid_of_relation env sigma r req in
        let signature = [Some (r,Some req);Some (r,Some req)],Some(r,Some req) in
        let add_m, add_m_lem =
          try Rewrite.Internal.default_morphism env sigma signature add
          with Not_found ->
            CErrors.user_err (str "Ring addition " ++ pr_econstr_env env sigma add ++ str " should be declared as a morphism.") in
        let mul_m, mul_m_lem =
          try Rewrite.Internal.default_morphism env sigma signature mul
          with Not_found ->
            CErrors.user_err (str "Ring multiplication " ++ pr_econstr_env env sigma mul ++ str " should be declared as a morphism.") in
        let op_morph =
          match opp with
            | Some opp ->
                (let opp_m,opp_m_lem =
                  try Rewrite.Internal.default_morphism env sigma ([Some(r,Some req)],Some(r,Some req)) opp
                  with Not_found ->
                    CErrors.user_err (str "Ring opposite " ++ pr_econstr_env env sigma opp ++ str " should be declared as a morphism.") in
                let op_morph =
                  op_morph r add mul opp req add_m_lem mul_m_lem opp_m_lem in
                  Flags.if_verbose
                    Feedback.msg_info
                    (str"Using setoid \""++ pr_econstr_env env sigma req++str"\""++spc()++
                        str"and morphisms \""++pr_econstr_env env sigma add_m ++
                        str"\","++spc()++ str"\""++pr_econstr_env env sigma mul_m++
                        str"\""++spc()++str"and \""++pr_econstr_env env sigma opp_m++
                        str"\"");
                  op_morph)
            | None ->
                (Flags.if_verbose
                    Feedback.msg_info
                    (str"Using setoid \""++pr_econstr_env env sigma req ++str"\"" ++ spc() ++
                        str"and morphisms \""++pr_econstr_env env sigma add_m ++
                        str"\""++spc()++str"and \""++
                        pr_econstr_env env sigma mul_m++str"\"");
                 op_smorph r add mul req add_m_lem mul_m_lem) in
          (setoid,op_morph)

let build_setoid_params env sigma r add mul opp req eqth =
  match eqth with
      Some th -> th
    | None -> ring_equality env sigma (r,add,mul,opp,req)

let dest_ring env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match EConstr.kind sigma th_typ with
      App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when eq_constr_nounivs sigma f (Lazy.force coq_almost_ring_theory) ->
          (None,r,zero,one,add,mul,Some sub,Some opp,req)
    | App(f,[|r;zero;one;add;mul;req|])
        when eq_constr_nounivs sigma f (Lazy.force coq_semi_ring_theory) ->
        (Some true,r,zero,one,add,mul,None,None,req)
    | App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when eq_constr_nounivs sigma f (Lazy.force coq_ring_theory) ->
        (Some false,r,zero,one,add,mul,Some sub,Some opp,req)
    | _ -> error "bad ring structure"


let reflect_coeff rkind =
  (* We build an ill-typed terms on purpose... *)
  match rkind with
      Abstract -> Lazy.force coq_abstract
    | Computational c -> lapp coq_comp [|c|]
    | Morphism m -> lapp coq_morph [|m|]

let interp_cst_tac env sigma rk kind (zero,one,add,mul,opp) cst_tac =
  match cst_tac with
      Some (CstTac t) -> Tacintern.glob_tactic t
    | Some (Closed lc) ->
        closed_term_ast (List.map Smartlocate.global_with_alias lc)
    | None ->
        let t = ArgArg(Loc.tag @@ Lazy.force ltac_inv_morph_nothing) in
              CAst.make (TacArg (TacCall (CAst.make (t,[]))))

let make_hyp env sigma c =
  let t = Retyping.get_type_of env sigma c in
  plapp sigma coq_mkhypo [|t;c|]

let make_hyp_list env sigma lH =
  let sigma, carrier = Evd.fresh_global env sigma (Lazy.force coq_hypo) in
  let sigma, l =
    List.fold_right
      (fun c (sigma,l) ->
        let sigma, c = make_hyp env sigma c in
        plapp sigma coq_cons [|carrier; c; l|]) lH
        (plapp sigma coq_nil [|carrier|])
  in
  let sigma, l' = Typing.solve_evars env sigma l in
  sigma, l'

let interp_power env sigma pow =
  let sigma, carrier = Evd.fresh_global env sigma (Lazy.force coq_hypo) in
  match pow with
  | None ->
      let t = ArgArg(Loc.tag (Lazy.force ltac_inv_morph_nothing)) in
      let sigma, c = plapp sigma coq_None [|carrier|] in
      sigma, (CAst.make (TacArg (TacCall (CAst.make (t,[])))), c)
  | Some (tac, spec) ->
      let tac =
        match tac with
        | CstTac t -> Tacintern.glob_tactic t
        | Closed lc ->
            closed_term_ast (List.map Smartlocate.global_with_alias lc) in
      let spec = ic_unsafe env sigma spec in
      let sigma, spec = make_hyp env sigma spec in
      let sigma, pow = plapp sigma coq_Some [|carrier; spec|] in
      sigma, (tac, pow)

let interp_sign env sigma sign =
  let sigma, carrier = Evd.fresh_global env sigma (Lazy.force coq_hypo) in
  match sign with
  | None -> plapp sigma coq_None [|carrier|]
  | Some spec ->
      let sigma, spec = make_hyp env sigma (ic_unsafe env sigma spec) in
      plapp sigma coq_Some [|carrier;spec|]
       (* Same remark on ill-typed terms ... *)

let interp_div env sigma div =
  let sigma, carrier = Evd.fresh_global env sigma (Lazy.force coq_hypo) in
  match div with
  | None -> plapp sigma coq_None [|carrier|]
  | Some spec ->
      let sigma, spec = make_hyp env sigma (ic_unsafe env sigma spec) in
      plapp sigma coq_Some [|carrier;spec|]
       (* Same remark on ill-typed terms ... *)

let add_theory0 env sigma name rth eqth morphth cst_tac (pre,post) power sign div =
  check_required_library (cdir@["Ring_base"]);
  let (kind,r,zero,one,add,mul,sub,opp,req) = dest_ring env sigma rth in
  let (sth,ext) = build_setoid_params env sigma r add mul opp req eqth in
  let sigma, (pow_tac, pspec) = interp_power env sigma power in
  let sigma, sspec = interp_sign env sigma sign in
  let sigma, dspec = interp_div env sigma div in
  let rk = reflect_coeff morphth in
  let params,ctx =
    exec_tactic env sigma 5 (zltac "ring_lemmas")
      [sth;ext;rth;pspec;sspec;dspec;rk] in
  let lemma1 = params.(3) in
  let lemma2 = params.(4) in

  let lemma1 =
    decl_constant name "_ring_lemma1" ctx lemma1 in
  let lemma2 =
    decl_constant name "_ring_lemma2" ctx lemma2 in
  let cst_tac =
    interp_cst_tac env sigma morphth kind (zero,one,add,mul,opp) cst_tac in
  let pretac =
    match pre with
        Some t -> Tacintern.glob_tactic t
      | _ -> CAst.make (TacId []) in
  let posttac =
    match post with
        Some t -> Tacintern.glob_tactic t
      | _ -> CAst.make (TacId []) in
  let r = EConstr.to_constr sigma r in
  let req = EConstr.to_constr sigma req in
  let sth = EConstr.to_constr sigma sth in
  let _ =
    Lib.add_leaf
      (theory_to_obj
        { ring_name = name;
          ring_carrier = r;
          ring_req = req;
          ring_setoid = sth;
          ring_ext = params.(1);
          ring_morph = params.(2);
          ring_th = params.(0);
          ring_cst_tac = cst_tac;
          ring_pow_tac = pow_tac;
          ring_lemma1 = lemma1;
          ring_lemma2 = lemma2;
          ring_pre_tac = pretac;
          ring_post_tac = posttac }) in
  ()

let ic_coeff_spec env sigma = function
  | Computational t -> Computational (ic_unsafe env sigma t)
  | Morphism t -> Morphism (ic_unsafe env sigma t)
  | Abstract -> Abstract


let set_once s r v =
  if Option.is_empty !r then r := Some v else error (s^" cannot be set twice")

let process_ring_mods env sigma l =
  let kind = ref None in
  let set = ref None in
  let cst_tac = ref None in
  let pre = ref None in
  let post = ref None in
  let sign = ref None in
  let power = ref None in
  let div = ref None in
  List.iter(function
      Ring_kind k -> set_once "ring kind" kind (ic_coeff_spec env sigma k)
    | Const_tac t -> set_once "tactic recognizing constants" cst_tac t
    | Pre_tac t -> set_once "preprocess tactic" pre t
    | Post_tac t -> set_once "postprocess tactic" post t
    | Setoid(sth,ext) -> set_once "setoid" set (ic_unsafe env sigma sth,ic_unsafe env sigma ext)
    | Pow_spec(t,spec) -> set_once "power" power (t,spec)
    | Sign_spec t -> set_once "sign" sign t
    | Div_spec t -> set_once "div" div t) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !cst_tac, !pre, !post, !power, !sign, !div)

let add_theory id rth l =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, rth = ic env sigma rth in
  let (k,set,cst,pre,post,power,sign, div) = process_ring_mods env sigma l in
  add_theory0 env sigma id rth set k cst (pre,post) power sign div

(*****************************************************************************)
(* The tactics consist then only in a lookup in the ring database and
   call the appropriate ltac. *)

let make_args_list sigma rl t =
  match rl with
  | [] -> let (_,t1,t2) = dest_rel0 sigma t in [t1;t2]
  | _ -> rl

let make_term_list env sigma carrier rl =
  let sigma, l = List.fold_right
    (fun x (sigma,l) -> plapp sigma coq_cons [|carrier;x;l|]) rl
    (plapp sigma coq_nil [|carrier|])
  in
  Typing.solve_evars env sigma l

let carg c = Tacinterp.Value.of_constr (EConstr.of_constr c)
let tacarg expr =
  Tacinterp.Value.of_closure (Tacinterp.default_ist ()) expr

let ltac_ring_structure e =
  let req = carg e.ring_req in
  let sth = carg e.ring_setoid in
  let ext = carg e.ring_ext in
  let morph = carg e.ring_morph in
  let th = carg e.ring_th in
  let cst_tac = tacarg e.ring_cst_tac in
  let pow_tac = tacarg e.ring_pow_tac in
  let lemma1 = carg e.ring_lemma1 in
  let lemma2 = carg e.ring_lemma2 in
  let pretac =  tacarg (CAst.make (TacFun ([Anonymous],e.ring_pre_tac))) in
  let posttac = tacarg (CAst.make (TacFun ([Anonymous],e.ring_post_tac))) in
  [req;sth;ext;morph;th;cst_tac;pow_tac;
   lemma1;lemma2;pretac;posttac]

let ring_lookup (f : Value.t) lH rl t =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Proofview.Goal.env gl in
    let rl = make_args_list sigma rl t in
    let e = find_ring_structure env sigma rl in
    let sigma, l = make_term_list env sigma (EConstr.of_constr e.ring_carrier) rl in
    let rl = Value.of_constr l in
    let sigma, l = make_hyp_list env sigma lH in
    let lH = Value.of_constr l in
    let ring = ltac_ring_structure e in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (Value.apply f (ring@[lH;rl]))
  end

(***********************************************************************)

let new_field_path =
  DirPath.make (List.map Id.of_string ["Field_tac";plugin_dir;"Stdlib"])

let field_ltac s =
  lazy(KerName.make (ModPath.MPfile new_field_path) (Label.make s))


let _ = add_map "field"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    my_reference "IDphi", (function _->Eval);
    my_reference "gen_phiZ", (function _->Eval);
    (* display_linear: evaluate polynomials and coef operations, protect
       field operations and make recursive call on the var map *)
    my_reference "display_linear",
      (function -1|9|10|11|13|15|16->Eval|12|14->Rec|_->Prot);
    my_reference "display_pow_linear",
     (function -1|9|10|11|14|16|18|19->Eval|12|17->Rec|_->Prot);
   (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
    pol_cst "Pphi_dev", (function -1|8|9|10|12|14->Eval|11|13->Rec|_->Prot);
    pol_cst "Pphi_pow",
          (function -1|8|9|10|13|15|17->Eval|11|16->Rec|_->Prot);
    (* PEeval: evaluate polynomial, protect ring
       operations and make recursive call on the var map *)
    pol_cst "PEeval", (function -1|10|13->Eval|8|12->Rec|_->Prot);
    (* FEeval: evaluate polynomial, protect field
       operations and make recursive call on the var map *)
    my_reference "FEeval", (function -1|12|15->Eval|10|14->Rec|_->Prot)]);;

let _ = add_map "field_cond"
  (map_without_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
     coq_nil, (function -1->Eval|_ -> Prot);
     my_reference "IDphi", (function _->Eval);
     my_reference "gen_phiZ", (function _->Eval);
    (* PCond: evaluate denum list, protect ring
       operations and make recursive call on the var map *)
     my_reference "PCond", (function -1|11|14->Eval|9|13->Rec|_->Prot)]);;


let _ = Redexpr.declare_reduction "simpl_field_expr"
  (protect_red "field")



let afield_theory = my_reference "almost_field_theory"
let field_theory = my_reference "field_theory"
let sfield_theory = my_reference "semi_field_theory"
let af_ar = my_reference"AF_AR"
let f_r = my_reference"F_R"
let sf_sr = my_reference"SF_SR"
let dest_field env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match EConstr.kind sigma th_typ with
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when isRefX env sigma (Lazy.force afield_theory) f ->
        let sigma, rth = plapp sigma af_ar
          [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (None,r,zero,one,add,mul,Some sub,Some opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when isRefX env sigma (Lazy.force field_theory) f ->
        let sigma, rth =
          plapp sigma f_r
            [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (Some false,r,zero,one,add,mul,Some sub,Some opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;div;inv;req|])
        when isRefX env sigma (Lazy.force sfield_theory) f ->
        let sigma, rth = plapp sigma sf_sr
          [|r;zero;one;add;mul;div;inv;req;th_spec|] in
        (Some true,r,zero,one,add,mul,None,None,div,inv,req,rth)
    | _ -> error "bad field structure"

let field_from_carrier = Summary.ref Cmap.empty ~name:"field-tac-carrier-table"

let print_fields () =
  Feedback.msg_notice (strbrk "The following field structures have been declared:");
  Cmap.iter (fun _carrier fi ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Feedback.msg_notice
        (hov 2
           (Id.print fi.field_name ++ spc() ++
            str"with carrier "++ pr_constr_env env sigma fi.field_carrier++spc()++
            str"and equivalence relation "++ pr_constr_env env sigma fi.field_req))
    ) !field_from_carrier

let field_for_carrier r = Cmap.find r !field_from_carrier

let find_field_structure env sigma l =
  check_required_library (cdir@["Field_tac"]);
  match l with
    | t::cl' ->
        let ty = Retyping.get_type_of env sigma t in
        let check c =
          let ty' = Retyping.get_type_of env sigma c in
          if not (Reductionops.is_conv env sigma ty ty') then
            CErrors.user_err
              (str"Arguments of field_simplify do not have all the same type.")
        in
        List.iter check cl';
        (try field_for_carrier (EConstr.to_constr sigma ty)
        with Not_found ->
          CErrors.user_err
            (str"Cannot find a declared field structure over"++
             spc()++str"\""++pr_econstr_env env sigma ty++str"\"."))
    | [] -> assert false

let add_field_entry e =
  field_from_carrier := Cmap.add e.field_carrier e !field_from_carrier

let subst_th (subst,th) =
  let c' = subst_mps subst th.field_carrier in
  let eq' = subst_mps subst th.field_req in
  let thm1' = subst_mps subst th.field_ok in
  let thm2' = subst_mps subst th.field_simpl_eq_ok in
  let thm3' = subst_mps subst th.field_simpl_ok in
  let thm4' = subst_mps subst th.field_simpl_eq_in_ok in
  let thm5' = subst_mps subst th.field_cond in
  let tac'= Tacsubst.subst_tactic subst th.field_cst_tac in
  let pow_tac' = Tacsubst.subst_tactic subst th.field_pow_tac in
  let pretac'= Tacsubst.subst_tactic subst th.field_pre_tac in
  let posttac'= Tacsubst.subst_tactic subst th.field_post_tac in
  if c' == th.field_carrier &&
     eq' == th.field_req &&
     thm1' == th.field_ok &&
     thm2' == th.field_simpl_eq_ok &&
     thm3' == th.field_simpl_ok &&
     thm4' == th.field_simpl_eq_in_ok &&
     thm5' == th.field_cond &&
     tac' == th.field_cst_tac &&
     pow_tac' == th.field_pow_tac &&
     pretac' == th.field_pre_tac &&
     posttac' == th.field_post_tac then th
  else
    { field_name = th.field_name;
      field_carrier = c';
      field_req = eq';
      field_cst_tac = tac';
      field_pow_tac = pow_tac';
      field_ok = thm1';
      field_simpl_eq_ok = thm2';
      field_simpl_ok = thm3';
      field_simpl_eq_in_ok = thm4';
      field_cond = thm5';
      field_pre_tac = pretac';
      field_post_tac = posttac' }

let ftheory_to_obj : field_info -> obj =
  declare_object @@ global_object_nodischarge "tactic-new-field-theory"
    ~cache:add_field_entry
    ~subst:(Some subst_th)

let field_equality env sigma r inv req =
  match EConstr.kind sigma req with
    | App (f, [| _ |]) when eq_constr_nounivs sigma f (Lazy.force coq_eq) ->
        let c = UnivGen.constr_of_monomorphic_global (Global.env ()) Coqlib.(lib_ref "core.eq.congr") in
        let c = EConstr.of_constr c in
        mkApp(c,[|r;r;inv|])
    | _ ->
        let _setoid = setoid_of_relation env sigma r req in
        let signature = [Some (r,Some req)],Some(r,Some req) in
        let inv_m, inv_m_lem =
          try Rewrite.Internal.default_morphism env sigma signature inv
          with Not_found ->
            error "field inverse should be declared as a morphism" in
          inv_m_lem

let add_field_theory0 env sigma name fth eqth morphth cst_tac inj (pre,post) power sign odiv =
  let open Constr in
  check_required_library (cdir@["Field_tac"]);
  let (sigma,fth) = ic env sigma fth in
  let (kind,r,zero,one,add,mul,sub,opp,div,inv,req,rth) =
    dest_field env sigma fth in
  let (sth,ext) = build_setoid_params env sigma r add mul opp req eqth in
  let eqth = Some(sth,ext) in
  let _ = add_theory0 env sigma name rth eqth morphth cst_tac (None,None) power sign odiv in
  let sigma, (pow_tac, pspec) = interp_power env sigma power in
  let sigma, sspec = interp_sign env sigma sign in
  let sigma, dspec = interp_div env sigma odiv in
  let inv_m = field_equality env sigma r inv req in
  let rk = reflect_coeff morphth in
  let params,ctx =
    exec_tactic env sigma 9 (field_ltac"field_lemmas")
      [sth;ext;inv_m;fth;pspec;sspec;dspec;rk] in
  let lemma1 = params.(3) in
  let lemma2 = params.(4) in
  let lemma3 = params.(5) in
  let lemma4 = params.(6) in
  let cond_lemma =
    match inj with
      | Some thm -> mkApp(params.(8),[|EConstr.to_constr sigma thm|])
      | None -> params.(7) in
  let lemma1 = decl_constant name "_field_lemma1"
    ctx lemma1 in
  let lemma2 = decl_constant name "_field_lemma2"
    ctx lemma2 in
  let lemma3 = decl_constant name "_field_lemma3"
    ctx lemma3 in
  let lemma4 = decl_constant name "_field_lemma4"
    ctx lemma4 in
  let cond_lemma = decl_constant name "_lemma5"
    ctx cond_lemma in
  let cst_tac =
    interp_cst_tac env sigma morphth kind (zero,one,add,mul,opp) cst_tac in
  let pretac =
    match pre with
        Some t -> Tacintern.glob_tactic t
      | _ -> CAst.make (TacId []) in
  let posttac =
    match post with
        Some t -> Tacintern.glob_tactic t
      | _ -> CAst.make (TacId []) in
  let r = EConstr.to_constr sigma r in
  let req = EConstr.to_constr sigma req in
  let _ =
    Lib.add_leaf
      (ftheory_to_obj
        { field_name = name;
          field_carrier = r;
          field_req = req;
          field_cst_tac = cst_tac;
          field_pow_tac = pow_tac;
          field_ok = lemma1;
          field_simpl_eq_ok = lemma2;
          field_simpl_ok = lemma3;
          field_simpl_eq_in_ok = lemma4;
          field_cond = cond_lemma;
          field_pre_tac = pretac;
          field_post_tac = posttac }) in  ()

let process_field_mods env sigma l =
  let kind = ref None in
  let set = ref None in
  let cst_tac = ref None in
  let pre = ref None in
  let post = ref None in
  let inj = ref None in
  let sign = ref None in
  let power = ref None in
  let div = ref None in
  List.iter(function
      Ring_mod(Ring_kind k) -> set_once "field kind" kind (ic_coeff_spec env sigma k)
    | Ring_mod(Const_tac t) ->
        set_once "tactic recognizing constants" cst_tac t
    | Ring_mod(Pre_tac t) -> set_once "preprocess tactic" pre t
    | Ring_mod(Post_tac t) -> set_once "postprocess tactic" post t
    | Ring_mod(Setoid(sth,ext)) -> set_once "setoid" set (ic_unsafe env sigma sth,ic_unsafe env sigma ext)
    | Ring_mod(Pow_spec(t,spec)) -> set_once "power" power (t,spec)
    | Ring_mod(Sign_spec t) -> set_once "sign" sign t
    | Ring_mod(Div_spec t) -> set_once "div" div t
    | Inject i -> set_once "infinite property" inj (ic_unsafe env sigma i)) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (env, sigma, k, !set, !inj, !cst_tac, !pre, !post, !power, !sign, !div)

let add_field_theory id t mods =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (env,sigma,k,set,inj,cst_tac,pre,post,power,sign,div) = process_field_mods env sigma mods in
  add_field_theory0 env sigma id t set k cst_tac inj (pre,post) power sign div

let ltac_field_structure e =
  let req = carg e.field_req in
  let cst_tac = tacarg e.field_cst_tac in
  let pow_tac = tacarg e.field_pow_tac in
  let field_ok = carg e.field_ok in
  let field_simpl_ok = carg e.field_simpl_ok in
  let field_simpl_eq_ok = carg e.field_simpl_eq_ok in
  let field_simpl_eq_in_ok = carg e.field_simpl_eq_in_ok in
  let cond_ok = carg e.field_cond in
  let pretac =  tacarg (CAst.make (TacFun ([Anonymous],e.field_pre_tac))) in
  let posttac = tacarg (CAst.make (TacFun ([Anonymous],e.field_post_tac))) in
  [req;cst_tac;pow_tac;field_ok;field_simpl_ok;field_simpl_eq_ok;
   field_simpl_eq_in_ok;cond_ok;pretac;posttac]

let field_lookup (f : Value.t) lH rl t =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Proofview.Goal.env gl in
    let rl = make_args_list sigma rl t in
    let e = find_field_structure env sigma rl in
    let sigma, c = make_term_list env sigma (EConstr.of_constr e.field_carrier) rl in
    let rl = Value.of_constr c in
    let sigma, l = make_hyp_list env sigma lH in
    let lH = Value.of_constr l in
    let field = ltac_field_structure e in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) (Value.apply f (field@[lH;rl]))
  end
