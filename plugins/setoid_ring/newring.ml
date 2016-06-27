(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Term
open Vars
open Closure
open Environ
open Libnames
open Globnames
open Glob_term
open Tacticals
open Tacexpr
open Coqlib
open Mod_subst
open Tacinterp
open Libobject
open Printer
open Declare
open Decl_kinds
open Entries
open Misctypes
open Newring_ast
open Proofview.Notations

(****************************************************************************)
(* controlled reduction *)

type protect_flag = Eval|Prot|Rec

let tag_arg tag_rec map subs i c =
  match map i with
      Eval -> mk_clos subs c
    | Prot -> mk_atom c
    | Rec -> if Int.equal i (-1) then mk_clos subs c else tag_rec c

let global_head_of_constr c = 
  let f, args = decompose_app c in
    try global_of_constr f
    with Not_found -> anomaly (str "global_head_of_constr")

let global_of_constr_nofail c = 
  try global_of_constr c
  with Not_found -> VarRef (Id.of_string "dummy")

let rec mk_clos_but f_map subs t =
  match f_map (global_of_constr_nofail t) with
    | Some map -> tag_arg (mk_clos_but f_map subs) map subs (-1) t
    | None ->
        (match kind_of_term t with
            App(f,args) -> mk_clos_app_but f_map subs f args 0
          | Prod _ -> mk_clos_deep (mk_clos_but f_map) subs t
          | _ -> mk_atom t)

and mk_clos_app_but f_map subs f args n =
  if n >= Array.length args then mk_atom(mkApp(f, args))
  else
    let fargs, args' = Array.chop n args in
    let f' = mkApp(f,fargs) in
    match f_map (global_of_constr_nofail f') with
    | Some map ->
       let f i t = tag_arg (mk_clos_but f_map subs) map subs i t in
       mk_red (FApp (f (-1) f', Array.mapi f args'))
    | None -> mk_atom (mkApp (f, args))

let interp_map l t =
  try Some(List.assoc_f eq_gr t l) with Not_found -> None

let protect_maps = ref String.Map.empty
let add_map s m = protect_maps := String.Map.add s m !protect_maps
let lookup_map map =
  try String.Map.find map !protect_maps
  with Not_found ->
    errorlabstrm"lookup_map"(str"map "++qs map++str"not found")

let protect_red map env sigma c =
  kl (create_clos_infos betadeltaiota env)
    (mk_clos_but (lookup_map map c) (Esubst.subs_id 0) c);;

let protect_tac map =
  Tactics.reduct_option (protect_red map,DEFAULTcast) None

let protect_tac_in map id =
  Tactics.reduct_option (protect_red map,DEFAULTcast) (Some(id, Locus.InHyp))


(****************************************************************************)

let closed_term t l =
  let open Quote_plugin in
  let l = List.map Universes.constr_of_global l in
  let cs = List.fold_right Quote.ConstrSet.add l Quote.ConstrSet.empty in
  if Quote.closed_under cs t then Proofview.tclUNIT () else Tacticals.New.tclFAIL 0 (mt())

(* TACTIC EXTEND echo
| [ "echo" constr(t) ] ->
  [ Pp.msg (Termops.print_constr t);  Tacinterp.eval_tactic (TacId []) ]
END;;*)

(*
let closed_term_ast l =
  TacFun([Some(Id.of_string"t")],
  TacAtom(Loc.ghost,TacExtend(Loc.ghost,"closed_term",
  [Genarg.in_gen Constrarg.wit_constr (mkVar(Id.of_string"t"));
   Genarg.in_gen (Genarg.wit_list Constrarg.wit_ref) l])))
*)
let closed_term_ast l =
  let tacname = {
    mltac_plugin = "newring_plugin";
    mltac_tactic = "closed_term";
  } in
  let tacname = {
    mltac_name = tacname;
    mltac_index = 0;
  } in
  let l = List.map (fun gr -> ArgArg(Loc.ghost,gr)) l in
  TacFun([Some(Id.of_string"t")],
  TacML(Loc.ghost,tacname,
  [TacGeneric (Genarg.in_gen (Genarg.glbwit Constrarg.wit_constr) (GVar(Loc.ghost,Id.of_string"t"),None));
   TacGeneric (Genarg.in_gen (Genarg.glbwit (Genarg.wit_list Constrarg.wit_ref)) l)]))
(*
let _ = add_tacdef false ((Loc.ghost,Id.of_string"ring_closed_term"
*)

(****************************************************************************)

let ic c =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  Constrintern.interp_open_constr env sigma c

let ic_unsafe c = (*FIXME remove *)
  let env = Global.env() in
  let sigma = Evd.from_env env in
    fst (Constrintern.interp_constr env sigma c)

let decl_constant na ctx c =
  let vars = Universes.universes_of_constr c in
  let ctx = Universes.restrict_universe_context (Univ.ContextSet.of_context ctx) vars in
  mkConst(declare_constant (Id.of_string na) 
	    (DefinitionEntry (definition_entry ~opaque:true
				~univs:(Univ.ContextSet.to_context ctx) c),
	     IsProof Lemma))

(* Calling a global tactic *)
let ltac_call tac (args:glob_tactic_arg list) =
  TacArg(Loc.ghost,TacCall(Loc.ghost, ArgArg(Loc.ghost, Lazy.force tac),args))

(* Calling a locally bound tactic *)
let ltac_lcall tac args =
  TacArg(Loc.ghost,TacCall(Loc.ghost, ArgVar(Loc.ghost, Id.of_string tac),args))

let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.ghost, id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let dummy_goal env sigma =
  let (gl,_,sigma) = 
    Goal.V82.mk_goal sigma (named_context_val env) mkProp Evd.Store.empty in
  {Evd.it = gl; Evd.sigma = sigma}

let constr_of v = match Value.to_constr v with
  | Some c -> c
  | None -> failwith "Ring.exec_tactic: anomaly"

let tactic_res = ref [||]

let get_res =
  let open Tacexpr in
  let name = { mltac_plugin = "newring_plugin"; mltac_tactic = "get_res"; } in
  let entry = { mltac_name = name; mltac_index = 0 } in
  let tac args ist =
    let n = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_int) (List.hd args) in
    let init i = Id.Map.find (Id.of_string ("x" ^ string_of_int i)) ist.lfun in
    tactic_res := Array.init n init;
    Proofview.tclUNIT ()
  in
  Tacenv.register_ml_tactic name [| tac |];
  entry

let exec_tactic env evd n f args =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.ghost, id)) in
    (succ i, x :: vars, Id.Map.add id (Value.of_constr arg) lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  (** Build the getter *)
  let lid = List.init n (fun i -> Id.of_string("x"^string_of_int i)) in
  let n = Genarg.in_gen (Genarg.glbwit Stdarg.wit_int) n in
  let get_res = TacML (Loc.ghost, get_res, [TacGeneric n]) in
  let getter = Tacexp (TacFun (List.map (fun id -> Some id) lid, get_res)) in
  (** Evaluate the whole result *)
  let gl = dummy_goal env evd in
  let gls = Proofview.V82.of_tactic (Tacinterp.eval_tactic_ist ist (ltac_call f (args@[getter]))) gl in
  let evd, nf = Evarutil.nf_evars_and_universes (Refiner.project gls) in
    Array.map (fun x -> nf (constr_of x)) !tactic_res, snd (Evd.universe_context evd)

let stdlib_modules =
  [["Coq";"Setoids";"Setoid"];
   ["Coq";"Lists";"List"];
   ["Coq";"Init";"Datatypes"];
   ["Coq";"Init";"Logic"];
  ]

let coq_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" stdlib_modules c)
let coq_reference c =
  lazy (Coqlib.gen_reference_in_modules "Ring" stdlib_modules c)

let coq_mk_Setoid = coq_constant "Build_Setoid_Theory"
let coq_None = coq_reference "None"
let coq_Some = coq_reference "Some"
let coq_eq = coq_constant "eq"

let coq_cons = coq_reference "cons"
let coq_nil = coq_reference "nil"

let lapp f args = mkApp(Lazy.force f,args)

let plapp evd f args = 
  let fc = Evarutil.e_new_global evd (Lazy.force f) in
    mkApp(fc,args)

let dest_rel0 t =
  match kind_of_term t with
  | App(f,args) when Array.length args >= 2 ->
      let rel = mkApp(f,Array.sub args 0 (Array.length args - 2)) in
      if closed0 rel then
        (rel,args.(Array.length args - 2),args.(Array.length args - 1))
      else error "ring: cannot find relation (not closed)"
  | _ -> error "ring: cannot find relation"

let rec dest_rel t =
  match kind_of_term t with
  | Prod(_,_,c) -> dest_rel c
  | _ -> dest_rel0 t

(****************************************************************************)
(* Library linking *)

let plugin_dir = "setoid_ring"

let cdir = ["Coq";plugin_dir]
let plugin_modules =
  List.map (fun d -> cdir@d)
    [["Ring_theory"];["Ring_polynom"]; ["Ring_tac"];["InitialRing"];
     ["Field_tac"]; ["Field_theory"]
    ]

let my_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" plugin_modules c)
let my_reference c =
  lazy (Coqlib.gen_reference_in_modules "Ring" plugin_modules c)

let new_ring_path =
  DirPath.make (List.map Id.of_string ["Ring_tac";plugin_dir;"Coq"])
let znew_ring_path =
  DirPath.make (List.map Id.of_string ["InitialRing";plugin_dir;"Coq"])
let zltac s =
  lazy(make_kn (MPfile znew_ring_path) DirPath.empty (Label.make s))

let mk_cst l s = lazy (Coqlib.gen_reference "newring" l s);;
let pol_cst s = mk_cst [plugin_dir;"Ring_polynom"] s ;;

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
let map_with_eq arg_map c =
  let (req,_,_) = dest_rel c in
  interp_map
    ((global_head_of_constr req,(function -1->Prot|_->Rec))::
    List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)

let map_without_eq arg_map _ =
  interp_map (List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)

let _ = add_map "ring"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
    pol_cst "Pphi_dev", (function -1|8|9|10|11|12|14->Eval|13->Rec|_->Prot);
    pol_cst "Pphi_pow",
          (function -1|8|9|10|11|13|15|17->Eval|16->Rec|_->Prot);
    (* PEeval: evaluate morphism and polynomial, protect ring
       operations and make recursive call on the var map *)
    pol_cst "PEeval", (function -1|7|9|12->Eval|11->Rec|_->Prot)])

(****************************************************************************)
(* Ring database *)

module Cmap = Map.Make(Constr)

let from_carrier = Summary.ref Cmap.empty ~name:"ring-tac-carrier-table"
let from_name = Summary.ref Spmap.empty ~name:"ring-tac-name-table"

let ring_for_carrier r = Cmap.find r !from_carrier

let find_ring_structure env sigma l =
  match l with
    | t::cl' ->
        let ty = Retyping.get_type_of env sigma t in
        let check c =
          let ty' = Retyping.get_type_of env sigma c in
          if not (Reductionops.is_conv env sigma ty ty') then
            errorlabstrm "ring"
              (str"arguments of ring_simplify do not have all the same type")
        in
        List.iter check cl';
        (try ring_for_carrier ty
        with Not_found ->
          errorlabstrm "ring"
            (str"cannot find a declared ring structure over"++
             spc()++str"\""++pr_constr ty++str"\""))
    | [] -> assert false

let add_entry (sp,_kn) e =
  from_carrier := Cmap.add e.ring_carrier e !from_carrier;
  from_name := Spmap.add sp e !from_name


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
     eq_constr set' th.ring_setoid &&
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
    { ring_carrier = c';
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
  let cache_th (name,th) = add_entry name th in
  declare_object
    {(default_object "tactic-new-ring-theory") with
      open_function = (fun i o -> if Int.equal i 1 then cache_th o);
      cache_function = cache_th;
      subst_function = subst_th;
      classify_function = (fun x -> Substitute x)}


let setoid_of_relation env evd a r =
  try
    let evm = !evd in
    let evm, refl = Rewrite.get_reflexive_proof env evm a r in
    let evm, sym = Rewrite.get_symmetric_proof env evm a r in
    let evm, trans = Rewrite.get_transitive_proof env evm a r in
      evd := evm;
      lapp coq_mk_Setoid [|a ; r ; refl; sym; trans |]
  with Not_found ->
    error "cannot find setoid relation"

let op_morph r add mul opp req m1 m2 m3 =
  lapp coq_mk_reqe [| r; add; mul; opp; req; m1; m2; m3 |]

let op_smorph r add mul req m1 m2 =
  lapp coq_mk_seqe [| r; add; mul; req; m1; m2 |]

(* let default_ring_equality (r,add,mul,opp,req) = *)
(*   let is_setoid = function *)
(*       {rel_refl=Some _; rel_sym=Some _;rel_trans=Some _;rel_aeq=rel} -> *)
(*         eq_constr_nounivs req rel (\* Qu: use conversion ? *\) *)
(*     | _ -> false in *)
(*   match default_relation_for_carrier ~filter:is_setoid r with *)
(*       Leibniz _ -> *)
(*         let setoid = lapp coq_eq_setoid [|r|] in *)
(*         let op_morph = *)
(*           match opp with *)
(*               Some opp -> lapp coq_eq_morph [|r;add;mul;opp|] *)
(*             | None -> lapp coq_eq_smorph [|r;add;mul|] in *)
(*         (setoid,op_morph) *)
(*     | Relation rel -> *)
(*         let setoid = setoid_of_relation rel in *)
(*         let is_endomorphism = function *)
(*             { args=args } -> List.for_all *)
(*                 (function (var,Relation rel) -> *)
(*                   var=None && eq_constr_nounivs req rel *)
(*                   | _ -> false) args in *)
(*         let add_m = *)
(*           try default_morphism ~filter:is_endomorphism add *)
(*           with Not_found -> *)
(*             error "ring addition should be declared as a morphism" in *)
(*         let mul_m = *)
(*           try default_morphism ~filter:is_endomorphism mul *)
(*           with Not_found -> *)
(*             error "ring multiplication should be declared as a morphism" in *)
(*         let op_morph = *)
(*           match opp with *)
(*             | Some opp -> *)
(*             (let opp_m = *)
(*               try default_morphism ~filter:is_endomorphism opp *)
(*               with Not_found -> *)
(*                 error "ring opposite should be declared as a morphism" in *)
(*              let op_morph = *)
(*                op_morph r add mul opp req add_m.lem mul_m.lem opp_m.lem in *)
(*              msgnl *)
(*                (str"Using setoid \""++pr_constr rel.rel_aeq++str"\""++spc()++   *)
(*                str"and morphisms \""++pr_constr add_m.morphism_theory++ *)
(*                str"\","++spc()++ str"\""++pr_constr mul_m.morphism_theory++ *)
(*                str"\""++spc()++str"and \""++pr_constr opp_m.morphism_theory++ *)
(*                str"\""); *)
(*              op_morph) *)
(*             | None -> *)
(*             (msgnl *)
(*               (str"Using setoid \""++pr_constr rel.rel_aeq++str"\"" ++ spc() ++   *)
(*                str"and morphisms \""++pr_constr add_m.morphism_theory++ *)
(*                str"\""++spc()++str"and \""++ *)
(*                pr_constr mul_m.morphism_theory++str"\""); *)
(*             op_smorph r add mul req add_m.lem mul_m.lem) in *)
(*         (setoid,op_morph) *)

let ring_equality env evd (r,add,mul,opp,req) =
  match kind_of_term req with
    | App (f, [| _ |]) when eq_constr_nounivs f (Lazy.force coq_eq) ->
	let setoid = plapp evd coq_eq_setoid [|r|] in
	let op_morph =
	  match opp with
              Some opp -> plapp evd coq_eq_morph [|r;add;mul;opp|]
            | None -> plapp evd coq_eq_smorph [|r;add;mul|] in
	let setoid = Typing.e_solve_evars env evd setoid in
	let op_morph = Typing.e_solve_evars env evd op_morph in
	  (setoid,op_morph)
    | _ ->
	let setoid = setoid_of_relation (Global.env ()) evd r req in
	let signature = [Some (r,Some req);Some (r,Some req)],Some(r,Some req) in
	let add_m, add_m_lem =
	  try Rewrite.default_morphism signature add
          with Not_found ->
            error "ring addition should be declared as a morphism" in
	let mul_m, mul_m_lem =
          try Rewrite.default_morphism signature mul
          with Not_found ->
            error "ring multiplication should be declared as a morphism" in
        let op_morph =
          match opp with
            | Some opp ->
		(let opp_m,opp_m_lem =
		  try Rewrite.default_morphism ([Some(r,Some req)],Some(r,Some req)) opp
		  with Not_found ->
                    error "ring opposite should be declared as a morphism" in
		let op_morph =
		  op_morph r add mul opp req add_m_lem mul_m_lem opp_m_lem in
		  Flags.if_verbose
		    Feedback.msg_info
		    (str"Using setoid \""++pr_constr req++str"\""++spc()++
			str"and morphisms \""++pr_constr add_m_lem ++
			str"\","++spc()++ str"\""++pr_constr mul_m_lem++
			str"\""++spc()++str"and \""++pr_constr opp_m_lem++
			str"\"");
		  op_morph)
            | None ->
		(Flags.if_verbose
		    Feedback.msg_info
		    (str"Using setoid \""++pr_constr req ++str"\"" ++ spc() ++
			str"and morphisms \""++pr_constr add_m_lem ++
			str"\""++spc()++str"and \""++
			pr_constr mul_m_lem++str"\"");
		 op_smorph r add mul req add_m_lem mul_m_lem) in
          (setoid,op_morph)

let build_setoid_params env evd r add mul opp req eqth =
  match eqth with
      Some th -> th
    | None -> ring_equality env evd (r,add,mul,opp,req)

let dest_ring env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match kind_of_term th_typ with
      App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when eq_constr_nounivs f (Lazy.force coq_almost_ring_theory) ->
          (None,r,zero,one,add,mul,Some sub,Some opp,req)
    | App(f,[|r;zero;one;add;mul;req|])
        when eq_constr_nounivs f (Lazy.force coq_semi_ring_theory) ->
        (Some true,r,zero,one,add,mul,None,None,req)
    | App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when eq_constr_nounivs f (Lazy.force coq_ring_theory) ->
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
        let t = ArgArg(Loc.ghost,Lazy.force ltac_inv_morph_nothing) in
              TacArg(Loc.ghost,TacCall(Loc.ghost,t,[]))

let make_hyp env evd c =
  let t = Retyping.get_type_of env !evd c in
   plapp evd coq_mkhypo [|t;c|]

let make_hyp_list env evd lH =
  let carrier = Evarutil.e_new_global evd (Lazy.force coq_hypo) in
  let l = 
    List.fold_right
      (fun c l -> plapp evd coq_cons [|carrier; (make_hyp env evd c); l|]) lH
      (plapp evd coq_nil [|carrier|])
  in 
  let l' = Typing.e_solve_evars env evd l in
    Evarutil.nf_evars_universes !evd l'

let interp_power env evd pow =
  let carrier = Evarutil.e_new_global evd (Lazy.force coq_hypo) in
  match pow with
  | None ->
      let t = ArgArg(Loc.ghost, Lazy.force ltac_inv_morph_nothing) in
      (TacArg(Loc.ghost,TacCall(Loc.ghost,t,[])), plapp evd coq_None [|carrier|])
  | Some (tac, spec) ->
      let tac =
        match tac with
        | CstTac t -> Tacintern.glob_tactic t
        | Closed lc ->
            closed_term_ast (List.map Smartlocate.global_with_alias lc) in
      let spec = make_hyp env evd (ic_unsafe spec) in
      (tac, plapp evd coq_Some [|carrier; spec|])

let interp_sign env evd sign =
  let carrier = Evarutil.e_new_global evd (Lazy.force coq_hypo) in
  match sign with
  | None -> plapp evd coq_None [|carrier|]
  | Some spec ->
      let spec = make_hyp env evd (ic_unsafe spec) in
      plapp evd coq_Some [|carrier;spec|]
       (* Same remark on ill-typed terms ... *)

let interp_div env evd div =
  let carrier = Evarutil.e_new_global evd (Lazy.force coq_hypo) in
  match div with
  | None -> plapp evd coq_None [|carrier|]
  | Some spec ->
      let spec = make_hyp env evd (ic_unsafe spec) in
      plapp evd coq_Some [|carrier;spec|]
       (* Same remark on ill-typed terms ... *)

let add_theory name (sigma,rth) eqth morphth cst_tac (pre,post) power sign div =
  check_required_library (cdir@["Ring_base"]);
  let env = Global.env() in
  let (kind,r,zero,one,add,mul,sub,opp,req) = dest_ring env sigma rth in
  let evd = ref sigma in
  let (sth,ext) = build_setoid_params env evd r add mul opp req eqth in
  let (pow_tac, pspec) = interp_power env evd power in
  let sspec = interp_sign env evd sign in
  let dspec = interp_div env evd div in
  let rk = reflect_coeff morphth in
  let params,ctx =
    exec_tactic env !evd 5 (zltac "ring_lemmas")
      [sth;ext;rth;pspec;sspec;dspec;rk] in
  let lemma1 = params.(3) in
  let lemma2 = params.(4) in

  let lemma1 =
    decl_constant (Id.to_string name^"_ring_lemma1") ctx lemma1 in
  let lemma2 =
    decl_constant (Id.to_string name^"_ring_lemma2") ctx lemma2 in
  let cst_tac =
    interp_cst_tac env sigma morphth kind (zero,one,add,mul,opp) cst_tac in
  let pretac =
    match pre with
        Some t -> Tacintern.glob_tactic t
      | _ -> TacId [] in
  let posttac =
    match post with
        Some t -> Tacintern.glob_tactic t
      | _ -> TacId [] in
  let _ =
    Lib.add_leaf name
      (theory_to_obj
        { ring_carrier = r;
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

let ic_coeff_spec = function
  | Computational t -> Computational (ic_unsafe t)
  | Morphism t -> Morphism (ic_unsafe t)
  | Abstract -> Abstract


let set_once s r v =
  if Option.is_empty !r then r := Some v else error (s^" cannot be set twice")

let process_ring_mods l =
  let kind = ref None in
  let set = ref None in
  let cst_tac = ref None in
  let pre = ref None in
  let post = ref None in
  let sign = ref None in
  let power = ref None in
  let div = ref None in
  List.iter(function
      Ring_kind k -> set_once "ring kind" kind (ic_coeff_spec k)
    | Const_tac t -> set_once "tactic recognizing constants" cst_tac t
    | Pre_tac t -> set_once "preprocess tactic" pre t
    | Post_tac t -> set_once "postprocess tactic" post t
    | Setoid(sth,ext) -> set_once "setoid" set (ic_unsafe sth,ic_unsafe ext)
    | Pow_spec(t,spec) -> set_once "power" power (t,spec)
    | Sign_spec t -> set_once "sign" sign t
    | Div_spec t -> set_once "div" div t) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !cst_tac, !pre, !post, !power, !sign, !div)

(*****************************************************************************)
(* The tactics consist then only in a lookup in the ring database and
   call the appropriate ltac. *)

let make_args_list rl t =
  match rl with
  | [] -> let (_,t1,t2) = dest_rel0 t in [t1;t2]
  | _ -> rl

let make_term_list env evd carrier rl =
  let l = List.fold_right
    (fun x l -> plapp evd coq_cons [|carrier;x;l|]) rl
    (plapp evd coq_nil [|carrier|])
  in Typing.e_solve_evars env evd l

let carg = Tacinterp.Value.of_constr
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
  let pretac = tacarg (TacFun([None],e.ring_pre_tac)) in
  let posttac = tacarg (TacFun([None],e.ring_post_tac)) in
  [req;sth;ext;morph;th;cst_tac;pow_tac;
   lemma1;lemma2;pretac;posttac]

let ring_lookup (f : Value.t) lH rl t =
  Proofview.Goal.enter { enter = begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    try (* find_ring_strucure can raise an exception *)
      let evdref = ref sigma in
      let rl = make_args_list rl t in
      let e = find_ring_structure env sigma rl in
      let rl = carg (make_term_list env evdref e.ring_carrier rl) in
      let lH = carg (make_hyp_list env evdref lH) in
      let ring = ltac_ring_structure e in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS !evdref) (ltac_apply f (ring@[lH;rl]))
    with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
  end }

(***********************************************************************)

let new_field_path =
  DirPath.make (List.map Id.of_string ["Field_tac";plugin_dir;"Coq"])

let field_ltac s =
  lazy(make_kn (MPfile new_field_path) DirPath.empty (Label.make s))


let _ = add_map "field"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    (* display_linear: evaluate polynomials and coef operations, protect
       field operations and make recursive call on the var map *)
    my_reference "display_linear",
      (function -1|9|10|11|12|13|15|16->Eval|14->Rec|_->Prot);
    my_reference "display_pow_linear",
     (function -1|9|10|11|12|13|14|16|18|19->Eval|17->Rec|_->Prot);
   (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
    pol_cst "Pphi_dev", (function -1|8|9|10|11|12|14->Eval|13->Rec|_->Prot);
    pol_cst "Pphi_pow",
          (function -1|8|9|10|11|13|15|17->Eval|16->Rec|_->Prot);
    (* PEeval: evaluate morphism and polynomial, protect ring
       operations and make recursive call on the var map *)
    pol_cst "PEeval", (function -1|7|9|12->Eval|11->Rec|_->Prot);
    (* FEeval: evaluate morphism, protect field
       operations and make recursive call on the var map *)
    my_reference "FEeval", (function -1|8|9|10|11|14->Eval|13->Rec|_->Prot)]);;

let _ = add_map "field_cond"
  (map_without_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
     coq_nil, (function -1->Eval|_ -> Prot);
    (* PCond: evaluate morphism and denum list, protect ring
       operations and make recursive call on the var map *)
     my_reference "PCond", (function -1|9|11|14->Eval|13->Rec|_->Prot)]);;
(*                       (function -1|9|11->Eval|10->Rec|_->Prot)]);;*)


let _ = Redexpr.declare_reduction "simpl_field_expr"
  (protect_red "field")



let afield_theory = my_reference "almost_field_theory"
let field_theory = my_reference "field_theory"
let sfield_theory = my_reference "semi_field_theory"
let af_ar = my_reference"AF_AR"
let f_r = my_reference"F_R"
let sf_sr = my_reference"SF_SR"
let dest_field env evd th_spec =
  let th_typ = Retyping.get_type_of env !evd th_spec in
  match kind_of_term th_typ with
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when is_global (Lazy.force afield_theory) f ->
        let rth = plapp evd af_ar
          [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (None,r,zero,one,add,mul,Some sub,Some opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when is_global (Lazy.force field_theory) f ->
        let rth =
          plapp evd f_r
            [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (Some false,r,zero,one,add,mul,Some sub,Some opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;div;inv;req|])
        when is_global (Lazy.force sfield_theory) f ->
        let rth = plapp evd sf_sr
          [|r;zero;one;add;mul;div;inv;req;th_spec|] in
        (Some true,r,zero,one,add,mul,None,None,div,inv,req,rth)
    | _ -> error "bad field structure"

let field_from_carrier = Summary.ref Cmap.empty ~name:"field-tac-carrier-table"
let field_from_name = Summary.ref Spmap.empty ~name:"field-tac-name-table"

let field_for_carrier r = Cmap.find r !field_from_carrier

let find_field_structure env sigma l =
  check_required_library (cdir@["Field_tac"]);
  match l with
    | t::cl' ->
        let ty = Retyping.get_type_of env sigma t in
        let check c =
          let ty' = Retyping.get_type_of env sigma c in
          if not (Reductionops.is_conv env sigma ty ty') then
            errorlabstrm "field"
              (str"arguments of field_simplify do not have all the same type")
        in
        List.iter check cl';
        (try field_for_carrier ty
        with Not_found ->
          errorlabstrm "field"
            (str"cannot find a declared field structure over"++
             spc()++str"\""++pr_constr ty++str"\""))
    | [] -> assert false

let add_field_entry (sp,_kn) e =
  field_from_carrier := Cmap.add e.field_carrier e !field_from_carrier;
  field_from_name := Spmap.add sp e !field_from_name

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
    { field_carrier = c';
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
  let cache_th (name,th) = add_field_entry name th in
  declare_object
    {(default_object "tactic-new-field-theory") with
      open_function = (fun i o -> if Int.equal i 1 then cache_th o);
      cache_function = cache_th;
      subst_function = subst_th;
      classify_function = (fun x -> Substitute x) }

let field_equality evd r inv req =
  match kind_of_term req with
    | App (f, [| _ |]) when eq_constr_nounivs f (Lazy.force coq_eq) ->
        mkApp(Universes.constr_of_global (Coqlib.build_coq_eq_data()).congr,[|r;r;inv|])
    | _ ->
	let _setoid = setoid_of_relation (Global.env ()) evd r req in
	let signature = [Some (r,Some req)],Some(r,Some req) in
	let inv_m, inv_m_lem =
	  try Rewrite.default_morphism signature inv
          with Not_found ->
            error "field inverse should be declared as a morphism" in
	  inv_m_lem

let add_field_theory name (sigma,fth) eqth morphth cst_tac inj (pre,post) power sign odiv =
  check_required_library (cdir@["Field_tac"]);
  let env = Global.env() in
  let evd = ref sigma in
  let (kind,r,zero,one,add,mul,sub,opp,div,inv,req,rth) =
    dest_field env evd fth in
  let (sth,ext) = build_setoid_params env evd r add mul opp req eqth in
  let eqth = Some(sth,ext) in
  let _ = add_theory name (!evd,rth) eqth morphth cst_tac (None,None) power sign odiv in
  let (pow_tac, pspec) = interp_power env evd power in
  let sspec = interp_sign env evd sign in
  let dspec = interp_div env evd odiv in
  let inv_m = field_equality evd r inv req in
  let rk = reflect_coeff morphth in
  let params,ctx =
    exec_tactic env !evd 9 (field_ltac"field_lemmas")
      [sth;ext;inv_m;fth;pspec;sspec;dspec;rk] in
  let lemma1 = params.(3) in
  let lemma2 = params.(4) in
  let lemma3 = params.(5) in
  let lemma4 = params.(6) in
  let cond_lemma =
    match inj with
      | Some thm -> mkApp(params.(8),[|thm|])
      | None -> params.(7) in
  let lemma1 = decl_constant (Id.to_string name^"_field_lemma1")
    ctx lemma1 in
  let lemma2 = decl_constant (Id.to_string name^"_field_lemma2") 
    ctx lemma2 in
  let lemma3 = decl_constant (Id.to_string name^"_field_lemma3") 
    ctx lemma3 in
  let lemma4 = decl_constant (Id.to_string name^"_field_lemma4") 
    ctx lemma4 in
  let cond_lemma = decl_constant (Id.to_string name^"_lemma5") 
    ctx cond_lemma in
  let cst_tac =
    interp_cst_tac env sigma morphth kind (zero,one,add,mul,opp) cst_tac in
  let pretac =
    match pre with
        Some t -> Tacintern.glob_tactic t
      | _ -> TacId [] in
  let posttac =
    match post with
        Some t -> Tacintern.glob_tactic t
      | _ -> TacId [] in
  let _ =
    Lib.add_leaf name
      (ftheory_to_obj
        { field_carrier = r;
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

let process_field_mods l =
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
      Ring_mod(Ring_kind k) -> set_once "field kind" kind (ic_coeff_spec k)
    | Ring_mod(Const_tac t) ->
        set_once "tactic recognizing constants" cst_tac t
    | Ring_mod(Pre_tac t) -> set_once "preprocess tactic" pre t
    | Ring_mod(Post_tac t) -> set_once "postprocess tactic" post t
    | Ring_mod(Setoid(sth,ext)) -> set_once "setoid" set (ic_unsafe sth,ic_unsafe ext)
    | Ring_mod(Pow_spec(t,spec)) -> set_once "power" power (t,spec)
    | Ring_mod(Sign_spec t) -> set_once "sign" sign t
    | Ring_mod(Div_spec t) -> set_once "div" div t
    | Inject i -> set_once "infinite property" inj (ic_unsafe i)) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !inj, !cst_tac, !pre, !post, !power, !sign, !div)

let ltac_field_structure e =
  let req = carg e.field_req in
  let cst_tac = tacarg e.field_cst_tac in
  let pow_tac = tacarg e.field_pow_tac in
  let field_ok = carg e.field_ok in
  let field_simpl_ok = carg e.field_simpl_ok in
  let field_simpl_eq_ok = carg e.field_simpl_eq_ok in
  let field_simpl_eq_in_ok = carg e.field_simpl_eq_in_ok in
  let cond_ok = carg e.field_cond in
  let pretac = tacarg (TacFun([None],e.field_pre_tac)) in
  let posttac = tacarg (TacFun([None],e.field_post_tac)) in
  [req;cst_tac;pow_tac;field_ok;field_simpl_ok;field_simpl_eq_ok;
   field_simpl_eq_in_ok;cond_ok;pretac;posttac]

let field_lookup (f : Value.t) lH rl t =
  Proofview.Goal.enter { enter = begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    try
      let evdref = ref sigma in
      let rl = make_args_list rl t in
      let e = find_field_structure env sigma rl in
      let rl = carg (make_term_list env evdref e.field_carrier rl) in
      let lH = carg (make_hyp_list env evdref lH) in
      let field = ltac_field_structure e in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS !evdref) (ltac_apply f (field@[lH;rl]))
    with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e
  end }
