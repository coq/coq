(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is the interface between the c-c algorithm and Coq *)

open Evd
open Names
open Inductiveops
open Declarations
open Constr
open EConstr
open Vars
open Tactics
open Typing
open Ccalgo
open Ccproof
open Pp
open Util
open Proofview.Notations

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let reference dir s = lazy (Coqlib.coq_reference "CC" dir s)

let _f_equal = reference ["Init";"Logic"] "f_equal"
let _eq_rect = reference ["Init";"Logic"] "eq_rect"
let _refl_equal = reference ["Init";"Logic"] "eq_refl"
let _sym_eq = reference ["Init";"Logic"] "eq_sym"
let _trans_eq = reference ["Init";"Logic"] "eq_trans"
let _eq = reference ["Init";"Logic"] "eq"
let _False = reference ["Init";"Logic"] "False"
let _True = reference ["Init";"Logic"] "True"
let _I = reference ["Init";"Logic"] "I"

let whd env sigma t =
  Reductionops.clos_whd_flags CClosure.betaiotazeta env sigma t

let whd_delta env sigma t =
  Reductionops.clos_whd_flags CClosure.all env sigma t

(* decompose member of equality in an applicative format *)

(** FIXME: evar leak *)
let sf_of env sigma c = snd (sort_of env sigma c)

let rec decompose_term env sigma t=
    match EConstr.kind sigma (whd env sigma t) with
      App (f,args)->
	let tf=decompose_term env sigma f in
	let targs=Array.map (decompose_term env sigma) args in
	  Array.fold_left (fun s t->Appli (s,t)) tf targs
    | Prod (_,a,_b) when noccurn sigma 1 _b ->
	let b = Termops.pop _b in
	let sort_b = sf_of env sigma b in
	let sort_a = sf_of env sigma a in
	Appli(Appli(Product (sort_a,sort_b) ,
		    decompose_term env sigma a),
	      decompose_term env sigma b)
    | Construct c ->
	let (((mind,i_ind),i_con),u)= c in 
	let u = EInstance.kind sigma u in
	let canon_mind = MutInd.make1 (MutInd.canonical mind) in
	let canon_ind = canon_mind,i_ind in
	let (oib,_)=Global.lookup_inductive (canon_ind) in
	let nargs=constructor_nallargs_env env (canon_ind,i_con) in
	  Constructor {ci_constr= ((canon_ind,i_con),u);
		       ci_arity=nargs;
		       ci_nhyps=nargs-oib.mind_nparams}
    | Ind c -> 
	let (mind,i_ind),u = c in 
	let u = EInstance.kind sigma u in
	let canon_mind = MutInd.make1 (MutInd.canonical mind) in
	let canon_ind = canon_mind,i_ind in  (Symb (Constr.mkIndU (canon_ind,u)))
    | Const (c,u) -> 
	let u = EInstance.kind sigma u in
	let canon_const = Constant.make1 (Constant.canonical c) in 
	  (Symb (Constr.mkConstU (canon_const,u)))
    | Proj (p, c) -> 
        let canon_mind kn = MutInd.make1 (MutInd.canonical kn) in
        let p' = Projection.map canon_mind p in
	let c = Retyping.expand_projection env sigma p' c [] in
	decompose_term env sigma c
    | _ ->
       let t = Termops.strip_outer_cast sigma t in
       if closed0 sigma t then Symb (EConstr.to_constr ~abort_on_undefined_evars:false sigma t) else raise Not_found

(* decompose equality in members and type *)
open Termops

let atom_of_constr env sigma term =
  let wh = whd_delta env sigma term in
  let kot = EConstr.kind sigma wh in
    match kot with
      App (f,args)->
	if is_global sigma (Lazy.force _eq) f && Int.equal (Array.length args) 3
	  then `Eq (args.(0),
		   decompose_term env sigma args.(1),
		   decompose_term env sigma args.(2))
	  else `Other (decompose_term env sigma term)
    | _ -> `Other (decompose_term env sigma term)

let rec pattern_of_constr env sigma c =
  match EConstr.kind sigma (whd env sigma c) with
      App (f,args)->
	let pf = decompose_term env sigma f in
	let pargs,lrels = List.split
	  (Array.map_to_list (pattern_of_constr env sigma) args) in
	  PApp (pf,List.rev pargs),
	List.fold_left Int.Set.union Int.Set.empty lrels
    | Prod (_,a,_b) when noccurn sigma 1 _b ->
	let b = Termops.pop _b in
	let pa,sa = pattern_of_constr env sigma a in
	let pb,sb = pattern_of_constr env sigma b in
	let sort_b = sf_of env sigma b in
	let sort_a = sf_of env sigma a in
	  PApp(Product (sort_a,sort_b),
	       [pa;pb]),(Int.Set.union sa sb)
    | Rel i -> PVar i,Int.Set.singleton i
    | _ ->
	let pf = decompose_term env sigma c in
	  PApp (pf,[]),Int.Set.empty

let non_trivial = function
    PVar _ -> false
  | _ -> true

let patterns_of_constr env sigma nrels term=
  let f,args=
    try destApp sigma (whd_delta env sigma term) with DestKO -> raise Not_found in
	if is_global sigma (Lazy.force _eq) f && Int.equal (Array.length args) 3
	then
	  let patt1,rels1 = pattern_of_constr env sigma args.(1)
	  and patt2,rels2 = pattern_of_constr env sigma args.(2) in
	  let valid1 =
	    if not (Int.equal (Int.Set.cardinal rels1) nrels) then Creates_variables
	    else if non_trivial patt1 then Normal
	    else Trivial (EConstr.to_constr sigma args.(0))
	  and valid2 =
	    if not (Int.equal (Int.Set.cardinal rels2) nrels) then Creates_variables
	    else if non_trivial patt2 then Normal
	    else Trivial (EConstr.to_constr sigma args.(0)) in
	    if valid1 != Creates_variables
	      || valid2 != Creates_variables  then
	      nrels,valid1,patt1,valid2,patt2
	    else raise Not_found
	else raise Not_found

let rec quantified_atom_of_constr env sigma nrels term =
  match EConstr.kind sigma (whd_delta env sigma term) with
      Prod (id,atom,ff) -> 
	if is_global sigma (Lazy.force _False) ff then
	  let patts=patterns_of_constr env sigma nrels atom in
	      `Nrule patts
	else 
	  quantified_atom_of_constr (EConstr.push_rel (RelDecl.LocalAssum (id,atom)) env) sigma (succ nrels) ff
    | _ ->  
	let patts=patterns_of_constr env sigma nrels term in
	    `Rule patts

let litteral_of_constr env sigma term=
  match EConstr.kind sigma (whd_delta env sigma term) with
    | Prod (id,atom,ff) -> 
	if is_global sigma (Lazy.force _False) ff then
	  match (atom_of_constr env sigma atom) with
	      `Eq(t,a,b) -> `Neq(t,a,b)
	    | `Other(p) -> `Nother(p)
	else
	  begin
	    try 
	      quantified_atom_of_constr (EConstr.push_rel (RelDecl.LocalAssum (id,atom)) env) sigma 1 ff
	    with Not_found ->
	      `Other (decompose_term env sigma term)
	  end
    | _ ->
	atom_of_constr env sigma term


(* store all equalities from the context *)

let make_prb gls depth additionnal_terms =
  let open Tacmach.New in
  let env=pf_env gls in
  let sigma=project gls in
  let state = empty depth {it = Proofview.Goal.goal gls; sigma } in
  let pos_hyps = ref [] in
  let neg_hyps =ref [] in
    List.iter
      (fun c ->
	 let t = decompose_term env sigma c in
	   ignore (add_term state t)) additionnal_terms;
    List.iter
      (fun decl ->
         let id = NamedDecl.get_id decl in
	 begin
	   let cid=Constr.mkVar id in
	   match litteral_of_constr env sigma (NamedDecl.get_type decl) with
	       `Eq (t,a,b) -> add_equality state cid a b
	     | `Neq (t,a,b) -> add_disequality state (Hyp cid) a b
	     | `Other ph ->
		 List.iter
		   (fun (cidn,nh) ->
		      add_disequality state (HeqnH (cid,cidn)) ph nh)
		   !neg_hyps;
		 pos_hyps:=(cid,ph):: !pos_hyps
	     | `Nother nh ->
		 List.iter
		   (fun (cidp,ph) ->
		      add_disequality state (HeqnH (cidp,cid)) ph nh)
		   !pos_hyps;
		 neg_hyps:=(cid,nh):: !neg_hyps
	     | `Rule patts -> add_quant state id true patts
	     | `Nrule patts -> add_quant state id false patts
	 end) (Proofview.Goal.hyps gls);
    begin
      match atom_of_constr env sigma (pf_concl gls) with
	  `Eq (t,a,b) -> add_disequality state Goal a b
	|	`Other g ->
		  List.iter
	      (fun (idp,ph) ->
		 add_disequality state (HeqG idp) ph g) !pos_hyps
    end;
    state

(* indhyps builds the array of arrays of constructor hyps for (ind largs) *)

let build_projection intype (cstr:pconstructor) special default gls=
  let open Tacmach.New in
  let ci= (snd(fst cstr)) in
  let sigma = project gls in
  let body=Equality.build_selector (pf_env gls) sigma ci (mkRel 1) intype special default in
  let id=pf_get_new_id (Id.of_string "t") gls in
  sigma, mkLambda(Name id,intype,body)

(* generate an adhoc tactic following the proof tree  *)

let app_global f args k =
  Tacticals.New.pf_constr_of_global (Lazy.force f) >>= fun fc -> k (mkApp (fc, args))

let rec gen_holes env sigma t n accu =
  if Int.equal n 0 then (sigma, List.rev accu)
  else match EConstr.kind sigma t with
  | Prod (_, u, t) ->
    let (sigma, ev) = Evarutil.new_evar env sigma u in
    let t = EConstr.Vars.subst1 ev t in
    gen_holes env sigma t (pred n) (ev :: accu)
  | _ -> assert false

let app_global_with_holes f args n =
  Proofview.Goal.enter begin fun gl ->
    Tacticals.New.pf_constr_of_global (Lazy.force f) >>= fun fc ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    Refine.refine ~typecheck:false begin fun sigma ->
      let t = Tacmach.New.pf_get_type_of gl fc in
      let t = Termops.prod_applist sigma t (Array.to_list args) in
      let ans = mkApp (fc, args) in
      let (sigma, holes) = gen_holes env sigma t n [] in
      let ans = applist (ans, holes) in
      let sigma = Typing.check env sigma ans concl in
      (sigma, ans)
    end
  end

let assert_before n c =
  Proofview.Goal.enter begin fun gl ->
    let evm, _ = Tacmach.New.pf_apply type_of gl c in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm)
    (assert_before n c)
  end

let refresh_type env evm ty =
  Evarsolve.refresh_universes ~status:Evd.univ_flexible ~refreshset:true
			      (Some false) env evm ty

let refresh_universes ty k =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let evm = Tacmach.New.project gl in
    let evm, ty = refresh_type env evm ty in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm) (k ty)
  end

let constr_of_term c = EConstr.of_constr (constr_of_term c)

let rec proof_tac p : unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
  let type_of t = Tacmach.New.pf_unsafe_type_of gl t in
  try (* type_of can raise exceptions *)
  match p.p_rule with
      Ax c -> exact_check (EConstr.of_constr c)
    | SymAx c ->
        let c = EConstr.of_constr c in
	let l=constr_of_term p.p_lhs and
	    r=constr_of_term p.p_rhs in
	refresh_universes (type_of l) (fun typ ->
        app_global _sym_eq [|typ;r;l;c|] exact_check)
    | Refl t ->
	let lr = constr_of_term t in
	refresh_universes (type_of lr) (fun typ ->
        app_global _refl_equal [|typ;constr_of_term t|] exact_check)
    | Trans (p1,p2)->
	let t1 = constr_of_term p1.p_lhs and
	    t2 = constr_of_term p1.p_rhs and
	    t3 = constr_of_term p2.p_rhs in
	refresh_universes (type_of t2) (fun typ ->
	let prf = app_global_with_holes _trans_eq [|typ;t1;t2;t3;|] 2 in
          Tacticals.New.tclTHENS prf [(proof_tac p1);(proof_tac p2)])
    | Congr (p1,p2)->
	let tf1=constr_of_term p1.p_lhs
	and tx1=constr_of_term p2.p_lhs
	and tf2=constr_of_term p1.p_rhs
	and tx2=constr_of_term p2.p_rhs in
	refresh_universes (type_of tf1) (fun typf ->
	refresh_universes (type_of tx1) (fun typx ->
	refresh_universes (type_of (mkApp (tf1,[|tx1|]))) (fun typfx ->
        let id = Tacmach.New.pf_get_new_id (Id.of_string "f") gl in
	let appx1 = mkLambda(Name id,typf,mkApp(mkRel 1,[|tx1|])) in
	let lemma1 = app_global_with_holes _f_equal [|typf;typfx;appx1;tf1;tf2|] 1 in
	let lemma2 = app_global_with_holes _f_equal [|typx;typfx;tf2;tx1;tx2|] 1 in
	let prf =
	  app_global_with_holes _trans_eq
		[|typfx;
		  mkApp(tf1,[|tx1|]);
		  mkApp(tf2,[|tx1|]);
		  mkApp(tf2,[|tx2|])|] 2 in
	  Tacticals.New.tclTHENS prf
	    [Tacticals.New.tclTHEN lemma1 (proof_tac p1);
  	     Tacticals.New.tclFIRST
	       [Tacticals.New.tclTHEN lemma2 (proof_tac p2);
		reflexivity;
                Tacticals.New.tclZEROMSG
		    (Pp.str
		       "I don't know how to handle dependent equality")]])))
  | Inject (prf,cstr,nargs,argind) ->
	 let ti=constr_of_term prf.p_lhs in
	 let tj=constr_of_term prf.p_rhs in
	 let default=constr_of_term p.p_lhs in
	 let special=mkRel (1+nargs-argind) in
	 refresh_universes (type_of ti) (fun intype ->
         refresh_universes (type_of default) (fun outtype ->
         let sigma, proj =
           build_projection intype cstr special default gl
         in
	 let injt=
           app_global_with_holes _f_equal [|intype;outtype;proj;ti;tj|] 1 in
	 Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
                               (Tacticals.New.tclTHEN injt (proof_tac prf))))
  with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
  end

let refute_tac c t1 t2 p =
  Proofview.Goal.enter begin fun gl ->
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let hid = Tacmach.New.pf_get_new_id (Id.of_string "Heq") gl in
  let false_t=mkApp (c,[|mkVar hid|]) in
  let k intype =
    let neweq= app_global _eq [|intype;tt1;tt2|] in
    Tacticals.New.tclTHENS (neweq (assert_before (Name hid)))
      [proof_tac p; simplest_elim false_t]
  in refresh_universes (Tacmach.New.pf_unsafe_type_of gl tt1) k
  end

let refine_exact_check c =
  Proofview.Goal.enter begin fun gl ->
    let evm, _ = Tacmach.New.pf_apply type_of gl c in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm) (exact_check c)
  end

let convert_to_goal_tac c t1 t2 p = 
  Proofview.Goal.enter begin fun gl ->
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let k sort =
    let neweq= app_global _eq [|sort;tt1;tt2|] in
    let e = Tacmach.New.pf_get_new_id (Id.of_string "e") gl in
    let x = Tacmach.New.pf_get_new_id (Id.of_string "X") gl in
    let identity=mkLambda (Name x,sort,mkRel 1) in
    let endt = app_global _eq_rect [|sort;tt1;identity;c;tt2;mkVar e|] in
    Tacticals.New.tclTHENS (neweq (assert_before (Name e)))
			   [proof_tac p; endt refine_exact_check]
  in refresh_universes (Tacmach.New.pf_unsafe_type_of gl tt2) k
  end

let convert_to_hyp_tac c1 t1 c2 t2 p =
  Proofview.Goal.enter begin fun gl ->
  let tt2=constr_of_term t2 in
  let h = Tacmach.New.pf_get_new_id (Id.of_string "H") gl in
  let false_t=mkApp (c2,[|mkVar h|]) in
    Tacticals.New.tclTHENS (assert_before (Name h) tt2)
      [convert_to_goal_tac c1 t1 t2 p;
       simplest_elim false_t]
  end

(* Essentially [assert (Heq : lhs = rhs) by proof_tac p; discriminate Heq] *)
let discriminate_tac cstru p =
  Proofview.Goal.enter begin fun gl ->
    let lhs=constr_of_term p.p_lhs and rhs=constr_of_term p.p_rhs in
    let env = Proofview.Goal.env gl in
    let evm = Tacmach.New.project gl in
    let evm, intype = refresh_type env evm (Tacmach.New.pf_unsafe_type_of gl lhs) in
    let hid = Tacmach.New.pf_get_new_id (Id.of_string "Heq") gl in
    let neweq=app_global _eq [|intype;lhs;rhs|] in
    Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evm)
			  (Tacticals.New.tclTHENS (neweq (assert_before (Name hid)))
      [proof_tac p; Equality.discrHyp hid])
  end

(* wrap everything *)

let build_term_to_complete uf pac =
  let cinfo = get_constructor_info uf pac.cnode in
  let real_args = List.rev_map (fun i -> constr_of_term (term uf i)) pac.args in
  let (kn, u) = cinfo.ci_constr in
  (applist (mkConstructU (kn, EInstance.make u), real_args), pac.arity)

let cc_tactic depth additionnal_terms =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    Coqlib.check_required_library Coqlib.logic_module_name;
    let _ = debug (fun () -> Pp.str "Reading subgoal ...") in
    let state = make_prb gl depth additionnal_terms in
    let _ = debug (fun () -> Pp.str "Problem built, solving ...") in
    let sol = execute true state in
    let _ = debug (fun () -> Pp.str "Computation completed.") in
    let uf=forest state in
    match sol with
      None -> Tacticals.New.tclFAIL 0 (str "congruence failed")
    | Some reason ->
	debug (fun () -> Pp.str "Goal solved, generating proof ...");
	match reason with
	  Discrimination (i,ipac,j,jpac) ->
	    let p=build_proof uf (`Discr (i,ipac,j,jpac)) in
	    let cstr=(get_constructor_info uf ipac.cnode).ci_constr in
	    discriminate_tac cstr p
	| Incomplete ->
            let open Glob_term in
            let env = Proofview.Goal.env gl in
            let terms_to_complete = List.map (build_term_to_complete uf) (epsilons uf) in
            let hole = DAst.make @@ GHole (Evar_kinds.InternalHole, Namegen.IntroAnonymous, None) in
            let pr_missing (c, missing) =
              let c = Detyping.detype Detyping.Now ~lax:true false Id.Set.empty env sigma c in
              let holes = List.init missing (fun _ -> hole) in
              Printer.pr_glob_constr_env env (DAst.make @@ GApp (c, holes))
            in
	    Feedback.msg_info
	      (Pp.str "Goal is solvable by congruence but some arguments are missing.");
	    Feedback.msg_info
	      (Pp.str "  Try " ++
		 hov 8
		 begin
		   str "\"congruence with (" ++
		     prlist_with_sep
		     (fun () -> str ")" ++ spc () ++ str "(")
		     pr_missing
		     terms_to_complete ++
		     str ")\","
		 end ++
		 Pp.str "  replacing metavariables by arbitrary terms.");
	    Tacticals.New.tclFAIL 0 (str "Incomplete")
	| Contradiction dis ->
	    let p=build_proof uf (`Prove (dis.lhs,dis.rhs)) in
	    let ta=term uf dis.lhs and tb=term uf dis.rhs in
	    match dis.rule with
	      Goal -> proof_tac p
	    | Hyp id -> refute_tac (EConstr.of_constr id) ta tb p
	    | HeqG id ->
                let id = EConstr.of_constr id in
		convert_to_goal_tac id ta tb p
	    | HeqnH (ida,idb) ->
                let ida = EConstr.of_constr ida in
                let idb = EConstr.of_constr idb in
		convert_to_hyp_tac ida ta idb tb p
  end

let cc_fail =
  Tacticals.New.tclZEROMSG (Pp.str "congruence failed.")

let congruence_tac depth l =
  Tacticals.New.tclORELSE
    (Tacticals.New.tclTHEN (Tacticals.New.tclREPEAT introf) (cc_tactic depth l))
    cc_fail

(* Beware: reflexivity = constructor 1 = apply refl_equal
   might be slow now, let's rather do something equivalent
   to a "simple apply refl_equal" *)

(* The [f_equal] tactic.

   It mimics the use of lemmas [f_equal], [f_equal2], etc.
   This isn't particularly related with congruence, apart from
   the fact that congruence is called internally.
*)

let mk_eq f c1 c2 k =
  Tacticals.New.pf_constr_of_global (Lazy.force f) >>= fun fc ->
  Proofview.Goal.enter begin fun gl ->
    let open Tacmach.New in
    let evm, ty = pf_apply type_of gl c1 in
    let evm, ty = Evarsolve.refresh_universes (Some false) (pf_env gl) evm ty in
    let term = mkApp (fc, [| ty; c1; c2 |]) in
    let evm, _ =  type_of (pf_env gl) evm term in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm) (k term)
    end

let f_equal =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.New.project gl in
    let cut_eq c1 c2 =
      try (* type_of can raise an exception *)
        Tacticals.New.tclTHENS
	  (mk_eq _eq c1 c2 Tactics.cut)
	  [Proofview.tclUNIT ();Tacticals.New.tclTRY ((app_global _refl_equal [||]) apply)]
      with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
    in
    Proofview.tclORELSE
      begin match EConstr.kind sigma concl with
      | App (r,[|_;t;t'|]) when is_global sigma (Lazy.force _eq) r ->
	  begin match EConstr.kind sigma t, EConstr.kind sigma t' with
	  | App (f,v), App (f',v') when Int.equal (Array.length v) (Array.length v') ->
	      let rec cuts i =
		if i < 0 then Tacticals.New.tclTRY (congruence_tac 1000 [])
		else Tacticals.New.tclTHENFIRST (cut_eq v.(i) v'.(i)) (cuts (i-1))
	      in cuts (Array.length v - 1)
	  | _ -> Proofview.tclUNIT ()
	  end
      | _ -> Proofview.tclUNIT ()
      end
      begin function (e, info) -> match e with
        | Pretype_errors.PretypeError _ | Type_errors.TypeError _ -> Proofview.tclUNIT ()
        | e -> Proofview.tclZERO ~info e
      end
  end
