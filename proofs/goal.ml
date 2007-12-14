(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term

(* This module implements the abstract interface to goals *)

(* type of the goals *)
type goal = {
  content : Evd.evar_info; (* logical information hyps |- concl and alike *)
  name : string option     (* optional name of the goal to be displayed *)
}

(* access primitive *)
let hyps gl = gl.content.Evd.evar_hyps
let concl gl = gl.content.Evd.evar_concl
let name gl = gl.name


(* Builds a new goal named [name] with hypotheses [hyps] and conclusion [gl] *)
let build ?name ~hyps ~concl =
  { content = Evd.make_evar hyps concl ;
    name = name
  }

(* builds a goal out of an evar_info, not quite meant to be exported *)
let of_info ?name evi = 
  { content = evi ;
    name = name
  }

(* Returns [true] if the goal has been partially resolved. *)
let is_defined evars { content = e }

(* return type of the Goal.refine function *)
(* it contains the new subgoals to produce, a function to reconstruct
   the proof to the current goal knowing the result of the subgoals,
   the type and constraint information about the evars of the proof
   (which has been extended with new ones), and the definitions of
   the evars to instantiate *)
type refinement = { reconstruct: Term.constr array -> Term.constr ;
                    subgoals: goal array ;
                    new_defs: Evd.evar_defs ;
                    to_instantiate: Evd.evar_map;
                    dependencies: Evd.evar option array}

(* a pessimistic (i.e : there won't be many positive answers) filter
   over evar_maps *)
let evar_map_filter f evm =
  Evd.fold (fun ev evi r -> 
	      if f ev evi then 
		Evd.add r ev evi 
	      else 
		r
	   ) 
           evm 
           Evd.empty

(* Inverts an array into a gmap (expectingly an array of evars) *)
(* arnaud: expliquer pour evar vs evar*evar_info *)
let invert a =
  let m = ref Gmap.empty in
  Array.iteri (fun i (e,_) -> m := Gmap.add e i !m) a;
  !m

(* arnaud:
(* Does [e] occur in a type in [evi] *)
let depends e evi =
  (* arnaud: *)
  fail_with "Goal.depends: not yet implemented" *)

(* [trigger_evar cont t] executes [cont] on every evar
   of [t]*)
let rec trigger_evar cont t = 
  match kind_of_term t with
  (* arnaud: est-ce bien nécessaire de fouiller la substitution ? *)
  | Evar (e, s) -> cont e; Array.iter (trigger_evar cont) s
  | Var _ | Meta _ | Const _ | Ind _ | Construct _ | Rel _ | Sort _ -> ()
  | Cast (c1, _, c2) 
  | Prod (_, c1, c2)
  | Lambda (_, c1, c2) -> trigger_evar cont c1; trigger_evar cont c2
  | LetIn (_, c1, c2, c3) -> trigger_evar cont c1; 
                             trigger_evar cont c2; 
			     trigger_evar cont c3
  | App (f, cs) -> trigger_evar cont f; Array.iter (trigger_evar cont) cs
  | Case (_, c1, c2, cs) -> trigger_evar cont c1;
                            trigger_evar cont c2;
			    Array.iter (trigger_evar cont) cs
  | Fix (_, (_, bs, ts))
  | CoFix (_, (_, bs, ts)) -> Array.iter (trigger_evar cont) bs; 
                              Array.iter (trigger_evar cont) ts

(* Turns an array of evars (actually evar*evar_info) (together with its 
   inversion trough the function [invert] above) into an array of 
   bool, in the same order, representing those which are dependent 
   (i.e. refered to in other ones contexts). 
   It is non-destructive. *)
let dependent evars subst =
  let n = Array.length evars in
  let res = Array.make n None in
  if n <= 1 then
    res
  else
    let evar_info_iter f {Evd.evar_concl= concl; Evd.evar_hyps = hyps } =
      f concl; Environ.iter_named_val f hyps
    in
    let make_depend e =
      try
	res.(Gmap.find e subst) <- Some e
      with Not_found -> 
	()
    in
    Array.iter (fun (_,evi) -> evar_info_iter (trigger_evar (make_depend)) evi) evars;
    res
  

(* takes a [Term.constr], an inverted array of evars and instantiates
   these evars according to an array of [constr]. *)
(* arnaud: would benefit of curried mkTruc *)
let rec reconstruct constr subst subconstr =
  match kind_of_term constr with
  | Evar (e,_) -> (try subconstr.(Gmap.find e subst) with Not_found -> constr)
  | Var _ 
  | Meta _ 
  | Const _ 
  | Ind _ 
  | Construct _ 
  | Rel _
  | Sort _  -> constr
  | Cast (c,k,t) -> mkCast (reconstruct c subst subconstr,
                            k,
                            reconstruct t subst subconstr)
  | Prod (n,t,b) -> mkProd (n,
                            reconstruct t subst subconstr,
                            reconstruct b subst subconstr)
  | Lambda (n,t,b) -> mkLambda (n,
                                reconstruct t subst subconstr,
                                reconstruct b subst subconstr)
  | LetIn (n,c,t,b) -> mkLetIn (n,
                                 reconstruct c subst subconstr,
                                 reconstruct t subst subconstr,
                                 reconstruct b subst subconstr)
  | App (f, cs) -> mkApp (reconstruct f subst subconstr, 
                          Array.map (fun c -> reconstruct c subst subconstr) cs)
  | Case (ci, c, d, bs) -> mkCase (ci,
                                   reconstruct c subst subconstr,
                                   reconstruct d subst subconstr,
                                   Array.map (fun c -> reconstruct c subst subconstr) bs)
  | Fix (i, (ns, bs, ts))-> mkFix (i,(ns,
				       Array.map (fun c -> reconstruct c subst subconstr) bs,
				       Array.map (fun c -> reconstruct c subst subconstr) ts))
  | CoFix (i, (ns, bs, ts)) -> mkCoFix (i,(ns,
				           Array.map (fun c -> reconstruct c subst subconstr) bs,
				           Array.map (fun c -> reconstruct c subst subconstr) ts))
  

(* arnaud: à commenter un brin  *)
let refine defs env check_type step gl =
  (* building an environement containing [env] and [hyps gl] *)
  let env = Environ.reset_with_named_context (hyps gl) env in
  (* if [check_type] is true, then creates a type constraint for the 
     proof-to-be *)
  let tycon = Pretyping.OfType (Option.init check_type (concl gl)) in
  (* the [defs] must be passed as a reference, redefs will be modified by
     the [understand_...] procedure *)
  let rdefs = ref defs in
  (* call to [understand_tcc_evars] returns a constr with undefined evars
     these evars will be our new goals *)
  let refine_step = Pretyping.Default.understand_tcc_evars rdefs env tycon step in
  (* [!rdefs] contains the modified evar_defs *)
  let new_defs = !rdefs in
  (* [delta_evars] holds the evars that have been introduced by this
     refinement (but not immediatly solved) *)
  (* arnaud: probablement à speeder up un bit *)
  let delta_evars = evar_map_filter (fun ev evi ->
                                      evi.Evd.evar_body = Evd.Evar_empty &&
                                      (* arnaud: factoriser la map ?*)
                                      not (Evd.mem (Evd.evars_of defs) ev)
				   )
                                   (Evd.evars_of new_defs)
  in
  (* [delta_evars] in the shape of an array *)
  let subst_array = Array.of_list (Evd.to_list delta_evars) in
  (* subgoals to return *)
  (* arnaud: et les noms? *)
  let subgoals = Array.map (fun (_, evi) -> of_info evi ) subst_array in
  (* [subst] allows to retrieve the indice of an evar in [subst_array] *)
  let subst = invert subst_array in
  (* final reconstruction function *)
  let freconstruct = reconstruct refine_step subst in
  (* evars that have been resolved by the refinement *)
  let newly_defined = evar_map_filter (fun ev evi ->
					 evi.Evd.evar_body <> Evd.Evar_empty &&
					 try 
					   not (Evd.is_defined (Evd.evars_of defs) ev)
					 with Not_found -> false
				      )
                                      (Evd.evars_of new_defs)
  in
  (* Array of dependencies. [dependencies.(i)] is [None] if no other subgoal
     depend on the i-th one, and [Some e] if it corresponds to 
     the evar named [e] in other subgoals *)
  let dependencies = dependent subst_array subst 
  in
  { reconstruct = freconstruct ;
    subgoals = subgoals ;
    new_defs = new_defs ;
    to_instantiate = newly_defined;
    dependencies = dependencies
  }


(* This function returns a new goal where the evars have been
   instantiated according to an evar_map *)
(* arnaud Evarutil ou Reductionops ou Pretype_errors ? *)
let instantiate em gl =
  (* note: goals don't have an evar_body *)
  let content = gl.content in
  let instantiate =  Evarutil.nf_evar em in
  { gl with
  
    content = { content with
                (* arnaud: map_named_val est a priori ok: si [t] n'a pas
		   d'evar alors [instantiate t] = [t], sinon [t] n'a
                   pas de forme compilé donc ça reste correct. Commenter
                   dans environ.ml(i) (et pre_env.ml(i)?) si ça fonctionne.*)
		Evd.evar_hyps = Environ.map_named_val instantiate content.Evd.evar_hyps;
		Evd.evar_concl = instantiate content.Evd.evar_concl
	      }
  }
