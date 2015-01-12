(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Errors
open Util

let reference dir s = Coqlib.gen_reference "CC" dir s

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
  let infos=Closure.create_clos_infos Closure.betaiotazeta env in
    (fun t -> Closure.whd_val infos (Closure.inject t))

let whd_delta env=
   let infos=Closure.create_clos_infos Closure.betadeltaiota env in
    (fun t -> Closure.whd_val infos (Closure.inject t))

(* decompose member of equality in an applicative format *)

(** FIXME: evar leak *)
let sf_of env sigma c = family_of_sort (sort_of env (ref sigma) c)

let rec decompose_term env sigma t=
    match kind_of_term (whd env t) with
      App (f,args)->
	let tf=decompose_term env sigma f in
	let targs=Array.map (decompose_term env sigma) args in
	  Array.fold_left (fun s t->Appli (s,t)) tf targs
    | Prod (_,a,_b) when not (Termops.dependent (mkRel 1) _b) ->
	let b = Termops.pop _b in
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
    | _ ->if closed0 t then (Symb t) else raise Not_found

(* decompose equality in members and type *)
open Globnames

let atom_of_constr env sigma term =
  let wh =  (whd_delta env term) in
  let kot = kind_of_term wh in
    match kot with
      App (f,args)->
	if is_global _eq f && Int.equal (Array.length args) 3
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
    | Prod (_,a,_b) when not (Termops.dependent (mkRel 1) _b) ->
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
    try destApp (whd_delta env term) with DestKO -> raise Not_found in
	if is_global _eq f && Int.equal (Array.length args) 3
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
	if is_global _False ff then
	  let patts=patterns_of_constr env sigma nrels atom in
	      `Nrule patts
	else 
	  quantified_atom_of_constr (Environ.push_rel (id,None,atom) env) sigma (succ nrels) ff
    | _ ->  
	let patts=patterns_of_constr env sigma nrels term in
	    `Rule patts

let litteral_of_constr env sigma term=
  match kind_of_term (whd_delta env term) with
    | Prod (id,atom,ff) -> 
	if is_global _False ff then
	  match (atom_of_constr env sigma atom) with
	      `Eq(t,a,b) -> `Neq(t,a,b)
	    | `Other(p) -> `Nother(p)
	else
	  begin
	    try 
	      quantified_atom_of_constr (Environ.push_rel (id,None,atom) env) sigma 1 ff  
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
      (fun (id,_,e) ->
	 begin
	   let cid=mkVar id in
	   match litteral_of_constr env sigma e with
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

let build_projection intype outtype (cstr:pconstructor) special default gls=
  let env=pf_env gls in
  let (h,argv) = try destApp intype with DestKO -> (intype,[||]) in
  let ind,u=destInd h in
  let types=Inductiveops.arities_of_constructors env (ind,u) in
  let lp=Array.length types in
  let ci=pred (snd(fst cstr)) in
  let branch i=
    let ti= prod_appvect types.(i) argv in
    let rc=fst (decompose_prod_assum ti) in
    let head=
      if Int.equal i ci then special else default in
      it_mkLambda_or_LetIn head rc in
  let branches=Array.init lp branch in
  let casee=mkRel 1 in
  let pred=mkLambda(Anonymous,intype,outtype) in
  let case_info=make_case_info (pf_env gls) ind RegularStyle in
  let body= mkCase(case_info, pred, casee, branches) in
  let id=pf_get_new_id (Id.of_string "t") gls in
    mkLambda(Name id,intype,body)

(* generate an adhoc tactic following the proof tree  *)

let _M =mkMeta

let app_global f args k = 
  Tacticals.pf_constr_of_global f (fun fc -> k (mkApp (fc, args)))

let new_app_global f args k = 
  Tacticals.New.pf_constr_of_global f (fun fc -> k (mkApp (fc, args)))

let new_refine c = Proofview.V82.tactic (refine c)

let rec proof_tac p : unit Proofview.tactic =
  Proofview.Goal.nf_enter begin fun gl ->
  let type_of t = Tacmach.New.pf_type_of gl t in
  try (* type_of can raise exceptions *)
  match p.p_rule with
      Ax c -> exact_check c
    | SymAx c ->
	let l=constr_of_term p.p_lhs and
	    r=constr_of_term p.p_rhs in
        let typ = (* Termops.refresh_universes *) type_of l in
        new_app_global _sym_eq [|typ;r;l;c|] exact_check
    | Refl t ->
	let lr = constr_of_term t in
	let typ = (* Termops.refresh_universes *) type_of lr in
        new_app_global _refl_equal [|typ;constr_of_term t|] exact_check
    | Trans (p1,p2)->
	let t1 = constr_of_term p1.p_lhs and
	    t2 = constr_of_term p1.p_rhs and
	    t3 = constr_of_term p2.p_rhs in
	let typ = (* Termops.refresh_universes *) (type_of t2) in
	let prf = new_app_global _trans_eq [|typ;t1;t2;t3;_M 1;_M 2|] in
          Tacticals.New.tclTHENS (prf new_refine) [(proof_tac p1);(proof_tac p2)]
    | Congr (p1,p2)->
	let tf1=constr_of_term p1.p_lhs
	and tx1=constr_of_term p2.p_lhs
	and tf2=constr_of_term p1.p_rhs
	and tx2=constr_of_term p2.p_rhs in
	let typf = (* Termops.refresh_universes  *)(type_of tf1) in
	let typx = (* Termops.refresh_universes *) (type_of tx1) in
	let typfx = (* Termops.refresh_universes *) (type_of (mkApp (tf1,[|tx1|]))) in
        let id = Tacmach.New.of_old (fun gls -> pf_get_new_id (Id.of_string "f") gls) gl in
	let appx1 = mkLambda(Name id,typf,mkApp(mkRel 1,[|tx1|])) in
	let lemma1 =
	  app_global _f_equal
		[|typf;typfx;appx1;tf1;tf2;_M 1|] in
	let lemma2=
	  app_global _f_equal
		[|typx;typfx;tf2;tx1;tx2;_M 1|] in
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
                Proofview.tclZERO (UserError ("Congruence" ,
		    (Pp.str
		       "I don't know how to handle dependent equality")))]]
  | Inject (prf,cstr,nargs,argind) ->
	 let ti=constr_of_term prf.p_lhs in
	 let tj=constr_of_term prf.p_rhs in
	 let default=constr_of_term p.p_lhs in
	 let intype = (* Termops.refresh_universes *) (type_of ti) in
	 let outtype = (* Termops.refresh_universes *) (type_of default) in
	 let special=mkRel (1+nargs-argind) in
         let proj =
           Tacmach.New.of_old (build_projection intype outtype cstr special default) gl
         in
	 let injt=
           app_global _f_equal [|intype;outtype;proj;ti;tj;_M 1|] in
	   Tacticals.New.tclTHEN (Proofview.V82.tactic (injt refine)) (proof_tac prf)
  with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
  end

let refute_tac c t1 t2 p =
  Proofview.Goal.nf_enter begin fun gl ->
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let intype =
    Tacmach.New.of_old (fun gls -> (* Termops.refresh_universes *) (pf_type_of gls tt1)) gl
  in
  let neweq= new_app_global _eq [|intype;tt1;tt2|] in
  let hid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "Heq")) gl in
  let false_t=mkApp (c,[|mkVar hid|]) in
    Tacticals.New.tclTHENS (neweq (assert_before (Name hid)))
      [proof_tac p; simplest_elim false_t]
  end

let refine_exact_check c gl =
  let evm, _ = pf_apply e_type_of gl c in
    Tacticals.tclTHEN (Refiner.tclEVARS evm) (Proofview.V82.of_tactic (exact_check c)) gl

let convert_to_goal_tac c t1 t2 p = 
  Proofview.Goal.nf_enter begin fun gl ->
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let sort =
    Tacmach.New.of_old (fun gls -> (* Termops.refresh_universes *) (pf_type_of gls tt2)) gl
  in
  let neweq= new_app_global _eq [|sort;tt1;tt2|] in
  let e = Tacmach.New.of_old (pf_get_new_id (Id.of_string "e")) gl in
  let x = Tacmach.New.of_old (pf_get_new_id (Id.of_string "X")) gl in
  let identity=mkLambda (Name x,sort,mkRel 1) in
  let endt=app_global _eq_rect [|sort;tt1;identity;c;tt2;mkVar e|] in
    Tacticals.New.tclTHENS (neweq (assert_before (Name e)))
      [proof_tac p; Proofview.V82.tactic (endt refine_exact_check)]
  end

let convert_to_hyp_tac c1 t1 c2 t2 p =
  Proofview.Goal.nf_enter begin fun gl ->
  let tt2=constr_of_term t2 in
  let h = Tacmach.New.of_old (pf_get_new_id (Id.of_string "H")) gl in
  let false_t=mkApp (c2,[|mkVar h|]) in
    Tacticals.New.tclTHENS (assert_before (Name h) tt2)
      [convert_to_goal_tac c1 t1 t2 p;
       simplest_elim false_t]
  end

let discriminate_tac (cstr,u as cstru) p =
  Proofview.Goal.nf_enter begin fun gl ->
    let t1=constr_of_term p.p_lhs and t2=constr_of_term p.p_rhs in
    let intype =
      Tacmach.New.of_old (fun gls -> (* Termops.refresh_universes *) (pf_type_of gls t1)) gl
    in
    let concl = Proofview.Goal.concl gl in
    (* let evm,outsort = Evd.new_sort_variable Evd.univ_rigid (project gls) in  *)
    (* let outsort = mkSort outsort in *)
    let xid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "X")) gl in
    (* let tid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "t")) gl in *)
    (* let identity=mkLambda(Name xid,outsort,mkLambda(Name tid,mkRel 1,mkRel 1)) in *)
    let identity = Universes.constr_of_global _I in
    (* let trivial=pf_type_of gls identity in *)
    let trivial = Universes.constr_of_global _True in
    let evm, outtype = Evd.new_sort_variable Evd.univ_flexible (Proofview.Goal.sigma gl) in 
    let outtype = mkSort outtype in
    let pred=mkLambda(Name xid,outtype,mkRel 1) in
    let hid = Tacmach.New.of_old (pf_get_new_id (Id.of_string "Heq")) gl in
    let proj = Tacmach.New.of_old (build_projection intype outtype cstru trivial concl) gl in
    let injt=app_global _f_equal
                    [|intype;outtype;proj;t1;t2;mkVar hid|] in
    let endt k =
      injt (fun injt ->
        app_global _eq_rect
          [|outtype;trivial;pred;identity;concl;injt|] k) in
    let neweq=new_app_global _eq [|intype;t1;t2|] in
    Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evm)
      (Tacticals.New.tclTHENS (neweq (assert_before (Name hid)))
        [proof_tac p; Proofview.V82.tactic (endt refine_exact_check)])
  end

(* wrap everything *)

let build_term_to_complete uf meta pac =
  let cinfo = get_constructor_info uf pac.cnode in
  let real_args = List.map (fun i -> constr_of_term (term uf i)) pac.args in
  let dummy_args = List.rev (List.init pac.arity meta) in
  let all_args = List.rev_append real_args dummy_args in
    applistc (mkConstructU cinfo.ci_constr) all_args

let cc_tactic depth additionnal_terms =
  Proofview.Goal.nf_enter begin fun gl ->
    Coqlib.check_required_library Coqlib.logic_module_name;
    let _ = debug (Pp.str "Reading subgoal ...") in
    let state = Tacmach.New.of_old (fun gls -> make_prb gls depth additionnal_terms) gl in
    let _ = debug (Pp.str "Problem built, solving ...") in
    let sol = execute true state in
    let _ = debug (Pp.str "Computation completed.") in
    let uf=forest state in
    match sol with
      None -> Tacticals.New.tclFAIL 0 (str "congruence failed")
    | Some reason ->
	debug (Pp.str "Goal solved, generating proof ...");
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
	    Pp.msg_info
	      (Pp.str "Goal is solvable by congruence but \
 some arguments are missing.");
	    Pp.msg_info
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
  end

let cc_fail gls =
  errorlabstrm  "Congruence" (Pp.str "congruence failed.")

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

let f_equal =
  Proofview.Goal.nf_enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let type_of = Tacmach.New.pf_type_of gl in
    let cut_eq c1 c2 =
      try (* type_of can raise an exception *)
        let ty = (* Termops.refresh_universes *) (type_of c1) in
        if eq_constr_nounivs c1 c2 then Proofview.tclUNIT ()
        else
          Tacticals.New.tclTRY (Tacticals.New.tclTHEN
          ((new_app_global _eq [|ty; c1; c2|]) Tactics.cut)
          (Tacticals.New.tclTRY ((new_app_global _refl_equal [||]) apply)))
      with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
    in
    Proofview.tclORELSE
      begin match kind_of_term concl with
      | App (r,[|_;t;t'|]) when Globnames.is_global _eq r ->
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
        | Type_errors.TypeError _ -> Proofview.tclUNIT ()
        | e -> Proofview.tclZERO ~info e
      end
  end
