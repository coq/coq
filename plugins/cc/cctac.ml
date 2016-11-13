(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is the interface between the c-c algorithm and Coq *)

open Evd
open Names
open Inductiveops
open Declarations
open Term
open Vars
open Tacmach
open Tactics
open Typing
open Ccalgo
open Ccproof
open Pp
open CErrors
open Util
open Proofview.Notations

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let reference dir s = lazy (Coqlib.gen_reference "CC" dir s)

let _f_equal = reference ["Init";"Logic"] "f_equal"
let _eq_rect = reference ["Init";"Logic"] "eq_rect"
let _refl_equal = reference ["Init";"Logic"] "eq_refl"
let _sym_eq = reference ["Init";"Logic"] "eq_sym"
let _trans_eq = reference ["Init";"Logic"] "eq_trans"
let _eq = reference ["Init";"Logic"] "eq"
let _False = reference ["Init";"Logic"] "False"
let _True = reference ["Init";"Logic"] "True"
let _I = reference ["Init";"Logic"] "I"

let whd env=
  let infos=CClosure.create_clos_infos CClosure.betaiotazeta env in
    (fun t -> CClosure.whd_val infos (CClosure.inject t))

let whd_delta env=
   let infos=CClosure.create_clos_infos CClosure.all env in
    (fun t -> CClosure.whd_val infos (CClosure.inject t))

(* decompose member of equality in an applicative format *)

(** FIXME: evar leak *)
let sf_of env sigma c = e_sort_of env (ref sigma) (EConstr.of_constr c)

let rec decompose_term env sigma t=
    match kind_of_term (whd env t) with
      App (f,args)->
	let tf=decompose_term env sigma f in
	let targs=Array.map (decompose_term env sigma) args in
	  Array.fold_left (fun s t->Appli (s,t)) tf targs
    | Prod (_,a,_b) when EConstr.Vars.noccurn sigma 1 (EConstr.of_constr _b) ->
	let b = Termops.pop (EConstr.of_constr _b) in
	let sort_b = sf_of env sigma b in
	let sort_a = sf_of env sigma a in
	Appli(Appli(Product (sort_a,sort_b) ,
		    decompose_term env sigma a),
	      decompose_term env sigma b)
    | Construct c ->
	let (((mind,i_ind),i_con),u)= c in 
	let canon_mind = mind_of_kn (canonical_mind mind) in
	let canon_ind = canon_mind,i_ind in
	let (oib,_)=Global.lookup_inductive (canon_ind) in
	let nargs=constructor_nallargs_env env (canon_ind,i_con) in
	  Constructor {ci_constr= ((canon_ind,i_con),u);
		       ci_arity=nargs;
		       ci_nhyps=nargs-oib.mind_nparams}
    | Ind c -> 
	let (mind,i_ind),u = c in 
	let canon_mind = mind_of_kn (canonical_mind mind) in
	let canon_ind = canon_mind,i_ind in  (Symb (mkIndU (canon_ind,u)))
    | Const (c,u) -> 
	let canon_const = constant_of_kn (canonical_con c) in 
	  (Symb (mkConstU (canon_const,u)))
    | Proj (p, c) -> 
	let canon_const kn = constant_of_kn (canonical_con kn) in 
	let p' = Projection.map canon_const p in
	(Appli (Symb (mkConst (Projection.constant p')), decompose_term env sigma c))
    | _ ->
       let t = Termops.strip_outer_cast sigma (EConstr.of_constr t) in
       if closed0 t then Symb t else raise Not_found

(* decompose equality in members and type *)
open Globnames

let atom_of_constr env sigma term =
  let wh =  (whd_delta env term) in
  let kot = kind_of_term wh in
    match kot with
      App (f,args)->
	if is_global (Lazy.force _eq) f && Int.equal (Array.length args) 3
	  then `Eq (args.(0),
		   decompose_term env sigma args.(1),
		   decompose_term env sigma args.(2))
	  else `Other (decompose_term env sigma term)
    | _ -> `Other (decompose_term env sigma term)

let rec pattern_of_constr env sigma c =
  match kind_of_term (whd env c) with
      App (f,args)->
	let pf = decompose_term env sigma f in
	let pargs,lrels = List.split
	  (Array.map_to_list (pattern_of_constr env sigma) args) in
	  PApp (pf,List.rev pargs),
	List.fold_left Int.Set.union Int.Set.empty lrels
    | Prod (_,a,_b) when EConstr.Vars.noccurn sigma 1 (EConstr.of_constr _b) ->
	let b = Termops.pop (EConstr.of_constr _b) in
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
    try destApp (whd_delta env term) with DestKO -> raise Not_found in
	if is_global (Lazy.force _eq) f && Int.equal (Array.length args) 3
	then
	  let patt1,rels1 = pattern_of_constr env sigma args.(1)
	  and patt2,rels2 = pattern_of_constr env sigma args.(2) in
	  let valid1 =
	    if not (Int.equal (Int.Set.cardinal rels1) nrels) then Creates_variables
	    else if non_trivial patt1 then Normal
	    else Trivial args.(0)
	  and valid2 =
	    if not (Int.equal (Int.Set.cardinal rels2) nrels) then Creates_variables
	    else if non_trivial patt2 then Normal
	    else Trivial args.(0) in
	    if valid1 != Creates_variables
	      || valid2 != Creates_variables  then
	      nrels,valid1,patt1,valid2,patt2
	    else raise Not_found
	else raise Not_found

let rec quantified_atom_of_constr env sigma nrels term =
  match kind_of_term (whd_delta env term) with
      Prod (id,atom,ff) -> 
	if is_global (Lazy.force _False) ff then
	  let patts=patterns_of_constr env sigma nrels atom in
	      `Nrule patts
	else 
	  quantified_atom_of_constr (Environ.push_rel (RelDecl.LocalAssum (id,atom)) env) sigma (succ nrels) ff
    | _ ->  
	let patts=patterns_of_constr env sigma nrels term in
	    `Rule patts

let litteral_of_constr env sigma term=
  match kind_of_term (whd_delta env term) with
    | Prod (id,atom,ff) -> 
	if is_global (Lazy.force _False) ff then
	  match (atom_of_constr env sigma atom) with
	      `Eq(t,a,b) -> `Neq(t,a,b)
	    | `Other(p) -> `Nother(p)
	else
	  begin
	    try 
	      quantified_atom_of_constr (Environ.push_rel (RelDecl.LocalAssum (id,atom)) env) sigma 1 ff
	    with Not_found ->
	      `Other (decompose_term env sigma term)
	  end
    | _ ->
	atom_of_constr env sigma term


(* store all equalities from the context *)

let make_prb gls depth additionnal_terms =
  let env=pf_env gls in
  let sigma=sig_sig gls in
  let state = empty depth gls in
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
	   let cid=mkVar id in
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
	 end) (Environ.named_context_of_val (Goal.V82.nf_hyps gls.sigma gls.it));
    begin
      match atom_of_constr env sigma (Evarutil.nf_evar sigma (pf_concl gls)) with
	  `Eq (t,a,b) -> add_disequality state Goal a b
	|	`Other g ->
		  List.iter
	      (fun (idp,ph) ->
		 add_disequality state (HeqG idp) ph g) !pos_hyps
    end;
    state

(* indhyps builds the array of arrays of constructor hyps for (ind largs) *)

let build_projection intype (cstr:pconstructor) special default gls=
  let ci= (snd(fst cstr)) in
  let body=Equality.build_selector (pf_env gls) (project gls) ci (mkRel 1) intype special default in
  let id=pf_get_new_id (Id.of_string "t") gls in
    mkLambda(Name id,intype,body)

(* generate an adhoc tactic following the proof tree  *)

let _M =mkMeta

let app_global f args k =
  Tacticals.pf_constr_of_global (Lazy.force f) (fun fc -> k (EConstr.of_constr (mkApp (fc, args))))

let new_app_global f args k =
  Tacticals.New.pf_constr_of_global (Lazy.force f) (fun fc -> k (EConstr.of_constr (mkApp (fc, args))))

let new_refine c = Proofview.V82.tactic (refine c)
let refine c = refine c

let assert_before n c =
  Proofview.Goal.enter { enter = begin fun gl ->
    let evm, _ = Tacmach.New.pf_apply type_of gl c in
      Tacticals.New.tclTHEN (Proofview.V82.tactic (Refiner.tclEVARS evm)) (assert_before n c)
  end }

let refresh_type env evm ty =
  Evarsolve.refresh_universes ~status:Evd.univ_flexible ~refreshset:true
			      (Some false) env evm ty

let refresh_universes ty k =
  Proofview.Goal.enter { enter = begin fun gl ->
    let env = Proofview.Goal.env gl in
    let evm = Tacmach.New.project gl in
    let evm, ty = refresh_type env evm (EConstr.of_constr ty) in
    Tacticals.New.tclTHEN (Proofview.V82.tactic (Refiner.tclEVARS evm)) (k ty)
  end }

let rec proof_tac p : unit Proofview.tactic =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
  let type_of t = Tacmach.New.pf_unsafe_type_of gl (EConstr.of_constr t) in
  try (* type_of can raise exceptions *)
  match p.p_rule with
      Ax c -> exact_check (EConstr.of_constr c)
    | SymAx c ->
	let l=constr_of_term p.p_lhs and
	    r=constr_of_term p.p_rhs in
	refresh_universes (type_of l) (fun typ ->
        new_app_global _sym_eq [|typ;r;l;c|] exact_check)
    | Refl t ->
	let lr = constr_of_term t in
	refresh_universes (type_of lr) (fun typ ->
        new_app_global _refl_equal [|typ;constr_of_term t|] exact_check)
    | Trans (p1,p2)->
	let t1 = constr_of_term p1.p_lhs and
	    t2 = constr_of_term p1.p_rhs and
	    t3 = constr_of_term p2.p_rhs in
	refresh_universes (type_of t2) (fun typ ->
	let prf = new_app_global _trans_eq [|typ;t1;t2;t3;_M 1;_M 2|] in
          Tacticals.New.tclTHENS (prf new_refine) [(proof_tac p1);(proof_tac p2)])
    | Congr (p1,p2)->
	let tf1=constr_of_term p1.p_lhs
	and tx1=constr_of_term p2.p_lhs
	and tf2=constr_of_term p1.p_rhs
	and tx2=constr_of_term p2.p_rhs in
	refresh_universes (type_of tf1) (fun typf ->
	refresh_universes (type_of tx1) (fun typx ->
	refresh_universes (type_of (mkApp (tf1,[|tx1|]))) (fun typfx ->
        let id = Tacmach.New.of_old (fun gls -> pf_get_new_id (Id.of_string "f") gls) gl in
	let appx1 = mkLambda(Name id,typf,mkApp(mkRel 1,[|tx1|])) in
	let lemma1 = app_global _f_equal [|typf;typfx;appx1;tf1;tf2;_M 1|] in
	let lemma2 = app_global _f_equal [|typx;typfx;tf2;tx1;tx2;_M 1|] in
	let prf =
	  app_global _trans_eq
		[|typfx;
		  mkApp(tf1,[|tx1|]);
		  mkApp(tf2,[|tx1|]);
		  mkApp(tf2,[|tx2|]);_M 2;_M 3|] in
	  Tacticals.New.tclTHENS (Proofview.V82.tactic (prf refine))
	    [Tacticals.New.tclTHEN (Proofview.V82.tactic (lemma1 refine)) (proof_tac p1);
  	     Tacticals.New.tclFIRST
	       [Tacticals.New.tclTHEN (Proofview.V82.tactic (lemma2 refine)) (proof_tac p2);
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
         let proj =
           Tacmach.New.of_old (build_projection intype cstr special default) gl
         in
	 let injt=
           app_global _f_equal [|intype;outtype;proj;ti;tj;_M 1|] in
	   Tacticals.New.tclTHEN (Proofview.V82.tactic (injt refine)) (proof_tac prf)))
  with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
  end }

let refute_tac c t1 t2 p =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let hid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "Heq")) gl in
  let false_t=mkApp (c,[|mkVar hid|]) in
  let false_t = EConstr.of_constr false_t in
  let k intype =
    let neweq= new_app_global _eq [|intype;tt1;tt2|] in
    Tacticals.New.tclTHENS (neweq (assert_before (Name hid)))
      [proof_tac p; simplest_elim false_t]
  in refresh_universes (Tacmach.New.pf_unsafe_type_of gl (EConstr.of_constr tt1)) k
  end }

let refine_exact_check c gl =
  let evm, _ = pf_apply type_of gl c in
    Tacticals.tclTHEN (Refiner.tclEVARS evm) (Proofview.V82.of_tactic (exact_check c)) gl

let convert_to_goal_tac c t1 t2 p = 
  Proofview.Goal.nf_enter { enter = begin fun gl ->
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let k sort =
    let neweq= new_app_global _eq [|sort;tt1;tt2|] in
    let e = Tacmach.New.of_old (pf_get_new_id (Id.of_string "e")) gl in
    let x = Tacmach.New.of_old (pf_get_new_id (Id.of_string "X")) gl in
    let identity=mkLambda (Name x,sort,mkRel 1) in
    let endt=app_global _eq_rect [|sort;tt1;identity;c;tt2;mkVar e|] in
    Tacticals.New.tclTHENS (neweq (assert_before (Name e)))
			   [proof_tac p; Proofview.V82.tactic (endt refine_exact_check)]
  in refresh_universes (Tacmach.New.pf_unsafe_type_of gl (EConstr.of_constr tt2)) k
  end }

let convert_to_hyp_tac c1 t1 c2 t2 p =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
  let tt2=constr_of_term t2 in
  let h = Tacmach.New.of_old (pf_get_new_id (Id.of_string "H")) gl in
  let false_t=mkApp (c2,[|mkVar h|]) in
  let false_t = EConstr.of_constr false_t in
  let tt2 = EConstr.of_constr tt2 in
    Tacticals.New.tclTHENS (assert_before (Name h) tt2)
      [convert_to_goal_tac c1 t1 t2 p;
       simplest_elim false_t]
  end }

let discriminate_tac (cstr,u as cstru) p =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    let t1=constr_of_term p.p_lhs and t2=constr_of_term p.p_rhs in
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let xid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "X")) gl in
    let identity = Universes.constr_of_global (Lazy.force _I) in
    let trivial = Universes.constr_of_global (Lazy.force _True) in
    let evm = Tacmach.New.project gl in
    let evm, intype = refresh_type env evm (EConstr.of_constr (Tacmach.New.pf_unsafe_type_of gl (EConstr.of_constr t1))) in
    let evm, outtype = Evd.new_sort_variable Evd.univ_flexible evm in
    let outtype = mkSort outtype in
    let pred = mkLambda(Name xid,outtype,mkRel 1) in
    let hid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "Heq")) gl in
    let proj = Tacmach.New.of_old (build_projection intype cstru trivial concl) gl in
    let injt=app_global _f_equal
			[|intype;outtype;proj;t1;t2;mkVar hid|] in
    let endt k =
      injt (fun injt ->
            let injt = EConstr.Unsafe.to_constr injt in
            app_global _eq_rect
		       [|outtype;trivial;pred;identity;concl;injt|] k) in
    let neweq=new_app_global _eq [|intype;t1;t2|] in
    Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evm)
			  (Tacticals.New.tclTHENS (neweq (assert_before (Name hid)))
      [proof_tac p; Proofview.V82.tactic (endt refine_exact_check)])
  end }

(* wrap everything *)

let build_term_to_complete uf meta pac =
  let cinfo = get_constructor_info uf pac.cnode in
  let real_args = List.map (fun i -> constr_of_term (term uf i)) pac.args in
  let dummy_args = List.rev (List.init pac.arity meta) in
  let all_args = List.rev_append real_args dummy_args in
    applistc (mkConstructU cinfo.ci_constr) all_args

let cc_tactic depth additionnal_terms =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    Coqlib.check_required_library Coqlib.logic_module_name;
    let _ = debug (fun () -> Pp.str "Reading subgoal ...") in
    let state = Tacmach.New.of_old (fun gls -> make_prb gls depth additionnal_terms) gl in
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
            let env = Proofview.Goal.env gl in
	    let metacnt = ref 0 in
	    let newmeta _ = incr metacnt; _M !metacnt in
	    let terms_to_complete =
	      List.map
		(build_term_to_complete uf newmeta)
		(epsilons uf) in
	    Feedback.msg_info
	      (Pp.str "Goal is solvable by congruence but \
 some arguments are missing.");
	    Feedback.msg_info
	      (Pp.str "  Try " ++
		 hov 8
		 begin
		   str "\"congruence with (" ++
		     prlist_with_sep
		     (fun () -> str ")" ++ spc () ++ str "(")
		     (Termops.print_constr_env env)
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
	    | Hyp id -> refute_tac id ta tb p
	    | HeqG id ->
		convert_to_goal_tac id ta tb p
	    | HeqnH (ida,idb) ->
		convert_to_hyp_tac ida ta idb tb p
  end }

let cc_fail gls =
  user_err ~hdr:"Congruence" (Pp.str "congruence failed.")

let congruence_tac depth l =
  Tacticals.New.tclORELSE
    (Tacticals.New.tclTHEN (Tacticals.New.tclREPEAT introf) (cc_tactic depth l))
    (Proofview.V82.tactic cc_fail)

(* Beware: reflexivity = constructor 1 = apply refl_equal
   might be slow now, let's rather do something equivalent
   to a "simple apply refl_equal" *)

(* The [f_equal] tactic.

   It mimics the use of lemmas [f_equal], [f_equal2], etc.
   This isn't particularly related with congruence, apart from
   the fact that congruence is called internally.
*)

let mk_eq f c1 c2 k =
  Tacticals.New.pf_constr_of_global (Lazy.force f) (fun fc ->
  Proofview.Goal.enter { enter = begin fun gl ->
    let open Tacmach.New in
    let evm, ty = pf_apply type_of gl (EConstr.of_constr c1) in
    let evm, ty = Evarsolve.refresh_universes (Some false) (pf_env gl) evm (EConstr.of_constr ty) in
    let term = mkApp (fc, [| ty; c1; c2 |]) in
    let evm, _ =  type_of (pf_env gl) evm (EConstr.of_constr term) in
    Tacticals.New.tclTHEN (Proofview.V82.tactic (Refiner.tclEVARS evm))
			  (k (EConstr.of_constr term))
    end })

let f_equal =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let cut_eq c1 c2 =
      try (* type_of can raise an exception *)
        Tacticals.New.tclTHENS
	  (mk_eq _eq c1 c2 Tactics.cut)
	  [Proofview.tclUNIT ();Tacticals.New.tclTRY ((new_app_global _refl_equal [||]) apply)]
      with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
    in
    Proofview.tclORELSE
      begin match kind_of_term concl with
      | App (r,[|_;t;t'|]) when Globnames.is_global (Lazy.force _eq) r ->
	  begin match kind_of_term t, kind_of_term t' with
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
  end }
