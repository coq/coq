(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id: eauto.ml4 10346 2007-12-05 21:11:19Z aspiwack $ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Reduction
open Proof_type
open Proof_trees
open Declarations
open Tacticals
open Tacmach
open Evar_refiner
open Tactics
open Pattern
open Clenv
open Auto
open Rawterm
open Hiddentac
open Typeclasses
open Typeclasses_errors

let e_give_exact c gl = 
  let t1 = (pf_type_of gl c) and t2 = pf_concl gl in 
  if occur_existential t1 or occur_existential t2 then 
     tclTHEN (Clenvtac.unify t1) (exact_check c) gl
  else exact_check c gl

let assumption id = e_give_exact (mkVar id)

let morphism_class = lazy (class_info (id_of_string "Morphism"))
let morphism2_class = lazy (class_info (id_of_string "BinaryMorphism"))
let morphism3_class = lazy (class_info (id_of_string "TernaryMorphism"))

let get_respect cl = 
  Option.get (List.hd (Recordops.lookup_projections cl.cl_impl))

let respect_proj = lazy (get_respect (Lazy.force morphism_class))
let respect2_proj = lazy (get_respect (Lazy.force morphism2_class))
let respect3_proj = lazy (get_respect (Lazy.force morphism3_class))

let setoid_refl_proj = lazy (mkConst (Lib.make_con (id_of_string "equiv_refl")))

let gen_constant dir s = Coqlib.gen_constant "Class_setoid" dir s
let coq_proj1 = lazy(gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = lazy(gen_constant ["Init"; "Logic"] "proj2")

let arrow_morphism a b = 
  mkLambda (Name (id_of_string "A"), a, 
	   mkLambda (Name (id_of_string "B"), b, 
		    mkProd (Anonymous, mkRel 2, mkRel 2)))
    
let setoid_refl l sa x = 
  applistc (Lazy.force setoid_refl_proj) (l @ [sa ; x])

let resolve_morphism env oldt m args args' = 
  let evars = ref (Evd.create_evar_defs Evd.empty) in
  let morph_instance, proj, evs, len = 
    let cl, proj = 
      match Array.length args with
	  1 -> Lazy.force morphism_class, Lazy.force respect_proj
	| 2 -> Lazy.force morphism2_class, Lazy.force respect2_proj
	| 3 -> Lazy.force morphism3_class, Lazy.force respect3_proj
	| _ -> raise Not_found
    in
    let ctxevs = substitution_of_named_context evars env cl.cl_name 0 [] cl.cl_context in
    let len = List.length ctxevs in
    let superevs = substitution_of_named_context evars env cl.cl_name len ctxevs cl.cl_super in
    let args = List.rev_map (fun (_, c) -> c) superevs in
    let app = applistc (mkInd cl.cl_impl) (args @ [m]) in
      resolve_one_typeclass_evd env evars app, proj, args, len
  in 
  evars := Evarutil.nf_evar_defs !evars;
  let evm = Evd.evars_of !evars in
  let ctxargs = List.map (Reductionops.nf_evar evm) evs in
  let ctx, sup = Util.list_chop len ctxargs in
  let appproj = applistc (mkConst proj) (ctxargs @ [m ; morph_instance]) in 
  let projargs, respars, ressetoid, typeargs = 
    array_fold_left2 
      (fun (acc, ctx, sup, typeargs') x y -> 
	let par, ctx = list_chop 2 ctx in
	let setoid, sup = List.hd sup, List.tl sup in
	  match y with
	      None ->
		let refl_proof = setoid_refl par setoid x in
		  [ refl_proof ; x ; x ] @ acc, ctx, sup, x :: typeargs'
	    | Some (p, (_, _, _, _, t')) ->
		[ p ; t'; x ] @ acc, ctx, sup, t' :: typeargs')
      ([], ctx, sup, []) args args'
  in
  let proof = applistc appproj (List.rev projargs) in
  let newt = applistc m (List.rev typeargs) in
    match respars, ressetoid with
	[ a ; r ], [ s ] -> (proof, (a, r, s, oldt, newt))
      | _ -> assert(false)
      
let build_new gl env setoid origt newt hyp hypinfo concl =
  let rec aux t = 
    match kind_of_term t with
      | _ when eq_constr t origt -> 
	  Some (hyp, hypinfo)
      | App (m, args) ->
	  let args' = Array.map aux args in
	    if array_for_all (fun x -> x = None) args' then None
	    else 
	      (try Some (resolve_morphism env t m args args')
		with Not_found -> None)
      | Prod (_, x, b) -> 
	  let x', b' = aux x, aux b in
	    if x' = None && b' = None then None
	    else 
	      (try Some (resolve_morphism env t (arrow_morphism (pf_type_of gl x) (pf_type_of gl b)) [| x ; b |] [| x' ; b' |])
		with Not_found -> None)
		
      | _ -> None
  in aux concl
 
let decompose_setoid_eqhyp env id t = 
  match kind_of_term t with
    | App (equiv, [| a; r; s; x; y |]) -> (mkVar id, (a, r, s, x, y))
    | App (r, [| x ; y |]) -> 
	(try 
	    let (p, (a, r, s, _, _)) = resolve_morphism env t r [| x ; y |] [| None; None |] in
	      (mkVar id, (a, r, s, x, y))
	  with Not_found -> error "Not a (declared) setoid equality")
    | _ -> error "Not a setoid equality"

let cl_rewrite id gl =
  let env = pf_env gl in
  let hyp = pf_get_hyp_typ gl id in
  let hypt, (typ, rel, setoid, origt, newt as hypinfo) = decompose_setoid_eqhyp env id hyp in
  let concl = pf_concl gl in
  let _concltyp = pf_type_of gl concl in
  let eq = build_new gl env setoid origt newt hypt hypinfo concl in
    match eq with  
	Some (p, (_, _, _, _, t)) -> 
	  let proj = applistc (Lazy.force coq_proj2) [ mkProd (Anonymous, concl, t) ; mkProd (Anonymous, t, concl) ; p ] in
	    (Tactics.apply proj) gl
      | None -> tclIDTAC gl
	  
TACTIC EXTEND class_rewrite
| [ "clrewrite" ident(id) ] -> [ cl_rewrite id ]
END
