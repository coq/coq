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

let gen_constant dir s = Coqlib.gen_constant "Class_setoid" dir s
let coq_proj1 = lazy(gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = lazy(gen_constant ["Init"; "Logic"] "proj2")
let iff = lazy (gen_constant ["Init"; "Logic"] "iff")

let iff_setoid = lazy (gen_constant ["Classes"; "Setoid"] "iff_setoid")
let setoid_equiv = lazy (gen_constant ["Classes"; "Setoid"] "equiv")
let setoid_morphism = lazy (gen_constant ["Classes"; "Setoid"] "setoid_morphism")
let setoid_refl_proj = lazy (gen_constant ["Classes"; "Setoid"] "equiv_refl")
  
let arrow_morphism a b = 
  mkLambda (Name (id_of_string "A"), a, 
	   mkLambda (Name (id_of_string "B"), b, 
		    mkProd (Anonymous, mkRel 2, mkRel 2)))
    
let setoid_refl l sa x = 
  applistc (Lazy.force setoid_refl_proj) (l @ [sa ; x])
      
let class_one = lazy (Lazy.force morphism_class, Lazy.force respect_proj)
let class_two = lazy (Lazy.force morphism2_class, Lazy.force respect2_proj)
let class_three = lazy (Lazy.force morphism3_class, Lazy.force respect3_proj)

exception Found of (constr * constant * constr list * int * constr * constr array *
		       (constr * (constr * constr * constr * constr * constr)) option array)

let resolve_morphism_evd env evd app = 
  let ev = Evarutil.e_new_evar evd env app in
  let evd' = resolve_typeclasses ~check:false env (Evd.evars_of !evd) !evd in
  let evm' = Evd.evars_of evd' in
    match Evd.evar_body (Evd.find evm' (fst (destEvar ev))) with
	Evd.Evar_empty -> raise Not_found
      | Evd.Evar_defined c -> evd := Evarutil.nf_evar_defs evd'; c

let is_equiv env sigma t = 
  isConst t && Reductionops.is_conv env sigma (Lazy.force setoid_equiv) t

let resolve_morphism env sigma direction oldt m args args' = 
  let evars = ref (Evd.create_evar_defs Evd.empty) in
  let morph_instance, proj, subst, len, m', args, args' = 
    if is_equiv env sigma m then 
      let params, rest = array_chop 3 args in
      let a, r, s = params.(0), params.(1), params.(2) in
      let params', rest' = array_chop 3 args' in
      let inst = mkApp (Lazy.force setoid_morphism, params) in
	(* Equiv gives a binary morphism *)
      let (cl, proj) = Lazy.force class_two in
      let ctxargs = [ a; r; a; r; mkProp; Lazy.force iff; s; s; Lazy.force iff_setoid; ] in
      let m' = mkApp (m, [| a; r; s |]) in
	inst, proj, ctxargs, 6, m', rest, rest'
    else
      let cls =
	match Array.length args with
	    1 -> [Lazy.force class_one, 1]
	  | 2 -> [Lazy.force class_two, 2; Lazy.force class_one, 1]
	  | 3 -> [Lazy.force class_three, 3; Lazy.force class_two, 2; Lazy.force class_one, 1]
	  | n -> [Lazy.force class_three, 3; Lazy.force class_two, 2; Lazy.force class_one, 1]
      in
	try 
	  List.iter (fun ((cl, proj), n) ->
	    evars := Evd.create_evar_defs Evd.empty;
	    let ctxevs = substitution_of_named_context evars env cl.cl_name 0 [] cl.cl_context in
	    let len = List.length ctxevs in
	    let superevs = substitution_of_named_context evars env cl.cl_name len ctxevs cl.cl_super in
	    let morphargs, morphobjs = array_chop (Array.length args - n) args in
	    let morphargs', morphobjs' = array_chop (Array.length args - n) args' in
	    let args = List.rev_map (fun (_, c) -> c) superevs in
	    let appm = mkApp(m, morphargs) in
	    let appmtype = Typing.type_of env sigma appm in
	    let app = applistc (mkInd cl.cl_impl) (args @ [appm]) in
	    let mtype = replace_vars superevs (pi3 (List.hd cl.cl_params)) in
	      try 
		evars := Unification.w_unify true env CONV ~mod_delta:true appmtype mtype !evars;
		evars := Evarutil.nf_evar_defs !evars;
		let app = Evarutil.nf_isevar !evars app in
		  raise (Found (resolve_morphism_evd env evars app, proj, args, len, appm, morphobjs, morphobjs'))
	      with Not_found -> ()
		| Stdpp.Exc_located (_, Pretype_errors.PretypeError _) 
		| Pretype_errors.PretypeError _ -> ())
	    cls; 
	  raise Not_found
	with Found x -> x
  in 
  evars := Evarutil.nf_evar_defs !evars;
  let evm = Evd.evars_of !evars in
  let ctxargs = List.map (Reductionops.nf_evar evm) subst in
  let ctx, sup = Util.list_chop len ctxargs in
  let m' = Reductionops.nf_evar evm m' in
  let appproj = applistc (mkConst proj) (ctxargs @ [m' ; morph_instance]) in
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
		if direction then
		  [ p ; t'; x ] @ acc, ctx, sup, t' :: typeargs'
		else [ p ; x; t' ] @ acc, ctx, sup, t' :: typeargs')
      ([], ctx, sup, []) args args'
  in
  let proof = applistc appproj (List.rev projargs) in
  let newt = applistc m' (List.rev typeargs) in
    match respars, ressetoid with
	[ a ; r ], [ s ] -> (proof, (a, r, s, oldt, newt))
      | _ -> assert(false)
      
let build_new gl env setoid direction origt newt hyp hypinfo concl =
  let rec aux t = 
    match kind_of_term t with
      | _ when eq_constr t origt -> 
	  Some (hyp, hypinfo)
      | App (m, args) ->
	  let args' = Array.map aux args in
	    if array_for_all (fun x -> x = None) args' then None
	    else 
	      (try Some (resolve_morphism env (project gl) direction t m args args')
		with Not_found -> None)
      | Prod (_, x, b) -> 
	  let x', b' = aux x, aux b in
	    if x' = None && b' = None then None
	    else 
	      (try Some (resolve_morphism env (project gl) direction t (arrow_morphism (pf_type_of gl x) (pf_type_of gl b)) [| x ; b |] [| x' ; b' |])
		with Not_found -> None)
		
      | _ -> None
  in aux concl

let decompose_setoid_eqhyp env sigma c dir t = 
  match kind_of_term t with
    | App (equiv, [| a; r; s; x; y |]) ->
	if dir then (c, (a, r, s, x, y))
	else (c, (a, r, s, y, x))
    | App (r, args) when Array.length args >= 2 -> 
	(try 
	    let (p, (a, r, s, _, _)) = resolve_morphism env sigma dir t r args (Array.map (fun _ -> None) args) in
	    let _, args = array_chop (Array.length args - 2) args in
	      if dir then (c, (a, r, s, args.(0), args.(1)))
	      else (c, (a, r, s, args.(1), args.(0)))
	  with Not_found -> error "Not a (declared) setoid equality")
    | _ -> error "Not a setoid equality"

let cl_rewrite c left2right gl =
  let env = pf_env gl in
  let sigma = project gl in
  let hyp = pf_type_of gl c in
  let hypt, (typ, rel, setoid, origt, newt as hypinfo) = decompose_setoid_eqhyp env sigma c left2right hyp in
  let concl = pf_concl gl in
  let _concltyp = pf_type_of gl concl in
  let eq = build_new gl env setoid left2right origt newt hypt hypinfo concl in
    match eq with  
	Some (p, (_, _, _, _, t)) -> 
	  let proj = 
	    if left2right then 
	      applistc (Lazy.force coq_proj2)
		[ mkProd (Anonymous, concl, t) ; mkProd (Anonymous, t, concl) ; p ] 
	    else 
	      applistc (Lazy.force coq_proj1)
		[ mkProd (Anonymous, t, concl) ; mkProd (Anonymous, concl, t) ; p ] 
	  in
	    (Tactics.apply proj) gl
      | None -> tclIDTAC gl
	  
open Extraargs

TACTIC EXTEND class_rewrite
| [ "clrewrite" orient(o) constr(c) ] -> [ cl_rewrite c o ]
END
