(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Closure
open Environ
open Libnames
open Tactics
open Rawterm
open Tacticals
open Tacexpr
open Pcoq
open Tactic
open Constr
open Setoid_replace
open Proof_type
open Coqlib
open Tacmach
open Mod_subst
open Tacinterp
open Libobject
open Printer
open Declare
open Decl_kinds
open Entries

(****************************************************************************)
(* controlled reduction *)

let mark_arg i c = mkEvar(i,[|c|])
let unmark_arg f c =
  match destEvar c with
    | (i,[|c|]) -> f i c
    | _ -> assert false

type protect_flag = Eval|Prot|Rec

let tag_arg tag_rec map subs i c =
  match map i with
      Eval -> mk_clos subs c
    | Prot -> mk_atom c
    | Rec -> if i = -1 then mk_clos subs c else tag_rec c

let rec mk_clos_but f_map subs t =
  match f_map t with
    | Some map -> tag_arg (mk_clos_but f_map subs) map subs (-1) t
    | None ->
        (match kind_of_term t with
            App(f,args) -> mk_clos_app_but f_map subs f args 0
          | Prod _ -> mk_clos_deep (mk_clos_but f_map) subs t
          | _ -> mk_atom t)

and mk_clos_app_but f_map subs f args n =
  if n >= Array.length args then mk_atom(mkApp(f, args))
  else
    let fargs, args' = array_chop n args in
    let f' = mkApp(f,fargs) in
    match f_map f' with
        Some map ->
          mk_clos_deep
            (fun s' -> unmark_arg (tag_arg (mk_clos_but f_map s') map s'))
            subs
            (mkApp (mark_arg (-1) f', Array.mapi mark_arg args'))
      | None -> mk_clos_app_but f_map subs f args (n+1)


let interp_map l c =
  try
    let (im,am) = List.assoc c l in
    Some(fun i ->
      if List.mem i im then Eval
      else if List.mem i am then Prot
      else if i = -1 then Eval
      else Rec)
  with Not_found -> None

let interp_map l t =
  try Some(List.assoc t l) with Not_found -> None

let protect_maps = ref ([]:(string*(constr->'a)) list)
let add_map s m = protect_maps := (s,m) :: !protect_maps
let lookup_map map =
  try List.assoc map !protect_maps
  with Not_found ->
    errorlabstrm"lookup_map"(str"map "++qs map++str"not found")

let protect_red map env sigma c =
  kl (create_clos_infos betadeltaiota env)
    (mk_clos_but (lookup_map map c) (Esubst.ESID 0) c);;

let protect_tac map =
  Tactics.reduct_option (protect_red map,DEFAULTcast) None ;;

let protect_tac_in map id =
  Tactics.reduct_option (protect_red map,DEFAULTcast)
    (Some((all_occurrences_expr,id),InHyp));;


TACTIC EXTEND protect_fv
  [ "protect_fv" string(map) "in" ident(id) ] -> 
    [ protect_tac_in map id ]
| [ "protect_fv" string(map) ] -> 
    [ protect_tac map ]
END;;

(****************************************************************************)

let closed_term t l =
  let l = List.map constr_of_global l in
  let cs = List.fold_right Quote.ConstrSet.add l Quote.ConstrSet.empty in
  if Quote.closed_under cs t then tclIDTAC else tclFAIL 0 (mt())
;;

TACTIC EXTEND closed_term
  [ "closed_term" constr(t) "[" ne_reference_list(l) "]" ] ->
    [ closed_term t l ]
END
;;

TACTIC EXTEND echo 
| [ "echo" constr(t) ] -> 
  [ Pp.msg (Termops.print_constr t);  Tacinterp.eval_tactic (TacId []) ]
END;;

(*
let closed_term_ast l =
  TacFun([Some(id_of_string"t")],
  TacAtom(dummy_loc,TacExtend(dummy_loc,"closed_term",
  [Genarg.in_gen Genarg.wit_constr (mkVar(id_of_string"t"));
   Genarg.in_gen (Genarg.wit_list1 Genarg.wit_ref) l])))
*)
let closed_term_ast l =
  let l = List.map (fun gr -> ArgArg(dummy_loc,gr)) l in
  TacFun([Some(id_of_string"t")],
  TacAtom(dummy_loc,TacExtend(dummy_loc,"closed_term",
  [Genarg.in_gen Genarg.globwit_constr (RVar(dummy_loc,id_of_string"t"),None);
   Genarg.in_gen (Genarg.wit_list1 Genarg.globwit_ref) l])))
(*
let _ = add_tacdef false ((dummy_loc,id_of_string"ring_closed_term"
*)

(****************************************************************************)

let ic c =
  let env = Global.env() and sigma = Evd.empty in
  Constrintern.interp_constr sigma env c

let ty c = Typing.type_of (Global.env()) Evd.empty c

let decl_constant na c =
  mkConst(declare_constant (id_of_string na) (DefinitionEntry 
    { const_entry_body = c;
      const_entry_type = None;
      const_entry_opaque = true;
      const_entry_boxed = true}, 
    IsProof Lemma))

let ltac_call tac (args:glob_tactic_arg list) =
  TacArg(TacCall(dummy_loc, ArgArg(dummy_loc, Lazy.force tac),args))
let ltac_acall tac (args:glob_tactic_arg list) =
  TacCall(dummy_loc, ArgArg(dummy_loc, Lazy.force tac),args)

let ltac_lcall tac args =
  TacArg(TacCall(dummy_loc, ArgVar(dummy_loc, id_of_string tac),args))

let carg c = TacDynamic(dummy_loc,Pretyping.constr_in c)

let dummy_goal env = 
  {Evd.it = Evd.make_evar (named_context_val env) mkProp;
   Evd.sigma = Evd.empty}

let exec_tactic env n f args =
  let lid = list_tabulate(fun i -> id_of_string("x"^string_of_int i)) n in
  let res = ref [||] in
  let get_res ist =
    let l = List.map (fun id ->  List.assoc id ist.lfun) lid in
    res := Array.of_list l;
    TacId[] in
  let getter =
    Tacexp(TacFun(List.map(fun id -> Some id) lid,
                  glob_tactic(tacticIn get_res))) in
  let _ =
    Tacinterp.eval_tactic(ltac_call f (args@[getter])) (dummy_goal env) in
  !res

let constr_of = function
  | VConstr c -> c
  | _ -> failwith "Ring.exec_tactic: anomaly"

let stdlib_modules =
  [["Coq";"Setoids";"Setoid"];
   ["Coq";"Lists";"List"];
   ["Coq";"Init";"Datatypes"];
   ["Coq";"Init";"Logic"];
  ]

let coq_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" stdlib_modules c)

let coq_mk_Setoid = coq_constant "Build_Setoid_Theory"
let coq_cons = coq_constant "cons"
let coq_nil = coq_constant "nil"
let coq_None = coq_constant "None"
let coq_Some = coq_constant "Some"
let coq_eq = coq_constant "eq"

let lapp f args = mkApp(Lazy.force f,args)

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

let contrib_name = "setoid_ring"

let cdir = ["Coq";contrib_name]
let contrib_modules =
  List.map (fun d -> cdir@d)
    [["Ring_theory"];["Ring_polynom"]; ["Ring_tac"];["InitialRing"];
     ["Field_tac"]; ["Field_theory"]
    ]

let my_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" contrib_modules c)

let new_ring_path =
  make_dirpath (List.map id_of_string ["Ring_tac";contrib_name;"Coq"])
let ltac s =
  lazy(make_kn (MPfile new_ring_path) (make_dirpath []) (mk_label s))
let znew_ring_path =
  make_dirpath (List.map id_of_string ["InitialRing";contrib_name;"Coq"])
let zltac s =
  lazy(make_kn (MPfile znew_ring_path) (make_dirpath []) (mk_label s))

let mk_cst l s = lazy (Coqlib.gen_constant "newring" l s);;
let pol_cst s = mk_cst [contrib_name;"Ring_polynom"] s ;;

(* Ring theory *)

(* almost_ring defs *)
let coq_almost_ring_theory = my_constant "almost_ring_theory"

(* setoid and morphism utilities *)
let coq_eq_setoid = my_constant "Eqsth"
let coq_eq_morph = my_constant "Eq_ext"
let coq_eq_smorph = my_constant "Eq_s_ext"

(* ring -> almost_ring utilities *)
let coq_ring_theory = my_constant "ring_theory"
let coq_mk_reqe = my_constant "mk_reqe"

(* semi_ring -> almost_ring utilities *)
let coq_semi_ring_theory = my_constant "semi_ring_theory"
let coq_mk_seqe = my_constant "mk_seqe"

let ltac_inv_morph_gen = zltac"inv_gen_phi"
let ltac_inv_morphZ = zltac"inv_gen_phiZ"
let ltac_inv_morphN = zltac"inv_gen_phiN"
let ltac_inv_morphNword = zltac"inv_gen_phiNword"
let coq_abstract = my_constant"Abstract"
let coq_comp = my_constant"Computational"
let coq_morph = my_constant"Morphism"

(* morphism *)
let coq_ring_morph = my_constant "ring_morph"
let coq_semi_morph = my_constant "semi_morph"

(* power function *)
let ltac_inv_morph_nothing = zltac"inv_morph_nothing"
let coq_pow_N_pow_N = my_constant "pow_N_pow_N"

(* hypothesis *)
let coq_mkhypo = my_constant "mkhypo"
let coq_hypo = my_constant "hypo"

(* Equality: do not evaluate but make recursive call on both sides *)
let map_with_eq arg_map c =
  let (req,_,_) = dest_rel c in
  interp_map
    ((req,(function -1->Prot|_->Rec))::
    List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)

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

type ring_info =
    { ring_carrier : types;
      ring_req : constr;
      ring_setoid : constr;
      ring_ext : constr;
      ring_morph : constr;
      ring_th : constr;
      ring_cst_tac : glob_tactic_expr;
      ring_pow_tac : glob_tactic_expr;
      ring_lemma1 : constr;
      ring_lemma2 : constr;
      ring_pre_tac : glob_tactic_expr;
      ring_post_tac : glob_tactic_expr }

module Cmap = Map.Make(struct type t = constr let compare = compare end)

let from_carrier = ref Cmap.empty
let from_relation = ref Cmap.empty
let from_name = ref Spmap.empty

let ring_for_carrier r = Cmap.find r !from_carrier
let ring_for_relation rel = Cmap.find rel !from_relation
let ring_lookup_by_name ref =
  Spmap.find (Nametab.locate_obj (snd(qualid_of_reference ref))) !from_name


let find_ring_structure env sigma l oname =
  match oname, l with
      Some rf, _ ->
        (try ring_lookup_by_name rf
        with Not_found ->
          errorlabstrm "ring"
            (str "found no ring named "++pr_reference rf))
    | None, t::cl' ->
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
    | None, [] -> assert false
(*
        let (req,_,_) = dest_rel cl in
        (try ring_for_relation req
        with Not_found ->
          errorlabstrm "ring"
            (str"cannot find a declared ring structure for equality"++
             spc()++str"\""++pr_constr req++str"\"")) *)

let _ = 
  Summary.declare_summary "tactic-new-ring-table"
    { Summary.freeze_function =
        (fun () -> !from_carrier,!from_relation,!from_name);
      Summary.unfreeze_function =
        (fun (ct,rt,nt) ->
          from_carrier := ct; from_relation := rt; from_name := nt);
      Summary.init_function =
        (fun () ->
          from_carrier := Cmap.empty; from_relation := Cmap.empty;
          from_name := Spmap.empty);
      Summary.survive_module = false;
      Summary.survive_section = false }

let add_entry (sp,_kn) e =
(*  let _ = ty e.ring_lemma1 in
  let _ = ty e.ring_lemma2 in
*)
  from_carrier := Cmap.add e.ring_carrier e !from_carrier;
  from_relation := Cmap.add e.ring_req e !from_relation;
  from_name := Spmap.add sp e !from_name 


let subst_th (_,subst,th) = 
  let c' = subst_mps subst th.ring_carrier in                   
  let eq' = subst_mps subst th.ring_req in
  let set' = subst_mps subst th.ring_setoid in
  let ext' = subst_mps subst th.ring_ext in
  let morph' = subst_mps subst th.ring_morph in
  let th' = subst_mps subst th.ring_th in
  let thm1' = subst_mps subst th.ring_lemma1 in
  let thm2' = subst_mps subst th.ring_lemma2 in
  let tac'= subst_tactic subst th.ring_cst_tac in
  let pow_tac'= subst_tactic subst th.ring_pow_tac in
  let pretac'= subst_tactic subst th.ring_pre_tac in
  let posttac'= subst_tactic subst th.ring_post_tac in
  if c' == th.ring_carrier &&
     eq' == th.ring_req &&
     set' = th.ring_setoid &&
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


let (theory_to_obj, obj_to_theory) = 
  let cache_th (name,th) = add_entry name th
  and export_th x = Some x in
  declare_object
    {(default_object "tactic-new-ring-theory") with
      open_function = (fun i o -> if i=1 then cache_th o);
      cache_function = cache_th;
      subst_function = subst_th;
      classify_function = (fun (_,x) -> Substitute x);
      export_function = export_th }


let setoid_of_relation env a r =
  let evm = Evd.empty in
  try 
    lapp coq_mk_Setoid
      [|a ; r ; 
	Class_tactics.reflexive_proof env evm a r ; 
	Class_tactics.symmetric_proof env evm a r ; 
	Class_tactics.transitive_proof env evm a r |]
  with Not_found ->
    error "cannot find setoid relation"

let op_morph r add mul opp req m1 m2 m3 =
  lapp coq_mk_reqe [| r; add; mul; opp; req; m1; m2; m3 |]

let op_smorph r add mul req m1 m2 =
  lapp coq_mk_seqe [| r; add; mul; req; m1; m2 |]

(* let default_ring_equality (r,add,mul,opp,req) = *)
(*   let is_setoid = function *)
(*       {rel_refl=Some _; rel_sym=Some _;rel_trans=Some _;rel_aeq=rel} -> *)
(*         eq_constr req rel (\* Qu: use conversion ? *\) *)
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
(*                   var=None && eq_constr req rel *)
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

let ring_equality (r,add,mul,opp,req) =
  match kind_of_term req with
    | App (f, [| _ |]) when eq_constr f (Lazy.force coq_eq) ->
	let setoid = lapp coq_eq_setoid [|r|] in
	let op_morph =
	  match opp with
              Some opp -> lapp coq_eq_morph [|r;add;mul;opp|]
            | None -> lapp coq_eq_smorph [|r;add;mul|] in
	  (setoid,op_morph)
    | _ ->
	let setoid = setoid_of_relation (Global.env ()) r req in
	let signature = [Some (r,req);Some (r,req)],Some(Lazy.lazy_from_val (r,req)) in
	let add_m, add_m_lem =
	  try Class_tactics.default_morphism signature add
          with Not_found ->
            error "ring addition should be declared as a morphism" in
	let mul_m, mul_m_lem =
          try Class_tactics.default_morphism signature mul
          with Not_found ->
            error "ring multiplication should be declared as a morphism" in
        let op_morph =
          match opp with
            | Some opp ->
		(let opp_m,opp_m_lem =
		  try Class_tactics.default_morphism ([Some(r,req)],Some(Lazy.lazy_from_val (r,req))) opp
		  with Not_found ->
                    error "ring opposite should be declared as a morphism" in
		let op_morph =
		  op_morph r add mul opp req add_m_lem mul_m_lem opp_m_lem in
		  Flags.if_verbose 
		    msgnl
		    (str"Using setoid \""++pr_constr req++str"\""++spc()++  
			str"and morphisms \""++pr_constr add_m_lem ++
			str"\","++spc()++ str"\""++pr_constr mul_m_lem++
			str"\""++spc()++str"and \""++pr_constr opp_m_lem++
			str"\"");
		  op_morph)
            | None ->
		(Flags.if_verbose
		    msgnl
		    (str"Using setoid \""++pr_constr req ++str"\"" ++ spc() ++  
			str"and morphisms \""++pr_constr add_m_lem ++
			str"\""++spc()++str"and \""++
			pr_constr mul_m_lem++str"\"");
		 op_smorph r add mul req add_m_lem mul_m_lem) in
          (setoid,op_morph)
	    
let build_setoid_params r add mul opp req eqth =
  match eqth with
      Some th -> th
    | None -> ring_equality (r,add,mul,opp,req)

let dest_ring env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match kind_of_term th_typ with
      App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when f = Lazy.force coq_almost_ring_theory ->
          (None,r,zero,one,add,mul,Some sub,Some opp,req)
    | App(f,[|r;zero;one;add;mul;req|])
        when f = Lazy.force coq_semi_ring_theory ->
        (Some true,r,zero,one,add,mul,None,None,req)
    | App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when f = Lazy.force coq_ring_theory ->
        (Some false,r,zero,one,add,mul,Some sub,Some opp,req)
    | _ -> error "bad ring structure"


let dest_morph env sigma m_spec =
  let m_typ = Retyping.get_type_of env sigma m_spec in
  match kind_of_term m_typ with
      App(f,[|r;zero;one;add;mul;sub;opp;req;
              c;czero;cone;cadd;cmul;csub;copp;ceqb;phi|])
        when f = Lazy.force coq_ring_morph ->
          (c,czero,cone,cadd,cmul,Some csub,Some copp,ceqb,phi)
    | App(f,[|r;zero;one;add;mul;req;c;czero;cone;cadd;cmul;ceqb;phi|])
        when f = Lazy.force coq_semi_morph ->
        (c,czero,cone,cadd,cmul,None,None,ceqb,phi)
    | _ -> error "bad morphism structure"


type coeff_spec =
    Computational of constr (* equality test *)
  | Abstract (* coeffs = Z *)
  | Morphism of constr (* general morphism *)


let reflect_coeff rkind =
  (* We build an ill-typed terms on purpose... *)
  match rkind with
      Abstract -> Lazy.force coq_abstract
    | Computational c -> lapp coq_comp [|c|]
    | Morphism m -> lapp coq_morph [|m|]

type cst_tac_spec =
    CstTac of raw_tactic_expr
  | Closed of reference list

let interp_cst_tac env sigma rk kind (zero,one,add,mul,opp) cst_tac =
  match cst_tac with
      Some (CstTac t) -> Tacinterp.glob_tactic t
    | Some (Closed lc) ->
        closed_term_ast (List.map Syntax_def.global_with_alias lc)
    | None ->
        (match rk, opp, kind with
            Abstract, None, _ ->
              let t = ArgArg(dummy_loc,Lazy.force ltac_inv_morphN) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul]))
          | Abstract, Some opp, Some _ ->
              let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morphZ) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul;opp]))
          | Abstract, Some opp, None ->
              let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morphNword) in
              TacArg
                (TacCall(dummy_loc,t,List.map carg [zero;one;add;mul;opp]))
          | Computational _,_,_ ->
              let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morph_gen) in
              TacArg
                (TacCall(dummy_loc,t,List.map carg [zero;one;zero;one]))
          | Morphism mth,_,_ ->
              let (_,czero,cone,_,_,_,_,_,_) = dest_morph env sigma mth in
              let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morph_gen) in
              TacArg
                (TacCall(dummy_loc,t,List.map carg [zero;one;czero;cone])))

let make_hyp env c =
  let t = Retyping.get_type_of env Evd.empty c in
  lapp coq_mkhypo [|t;c|]

let make_hyp_list env lH =
  let carrier = Lazy.force coq_hypo in
  List.fold_right 
    (fun c l -> lapp coq_cons [|carrier; (make_hyp env c); l|]) lH
    (lapp coq_nil [|carrier|])

let interp_power env pow =  
  let carrier = Lazy.force coq_hypo in
  match pow with
  | None -> 
      let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morph_nothing) in
      (TacArg(TacCall(dummy_loc,t,[])), lapp coq_None [|carrier|])
  | Some (tac, spec) -> 
      let tac = 
        match tac with
        | CstTac t -> Tacinterp.glob_tactic t
        | Closed lc ->
            closed_term_ast (List.map Syntax_def.global_with_alias lc) in
      let spec = make_hyp env (ic spec) in
      (tac, lapp coq_Some [|carrier; spec|])

let interp_sign env sign =
  let carrier = Lazy.force coq_hypo in
  match sign with
  | None -> lapp coq_None [|carrier|] 
  | Some spec -> 
      let spec = make_hyp env (ic spec) in
      lapp coq_Some [|carrier;spec|]
       (* Same remark on ill-typed terms ... *)

let interp_div env div =
  let carrier = Lazy.force coq_hypo in
  match div with
  | None -> lapp coq_None [|carrier|] 
  | Some spec -> 
      let spec = make_hyp env (ic spec) in
      lapp coq_Some [|carrier;spec|]
       (* Same remark on ill-typed terms ... *)

let add_theory name rth eqth morphth cst_tac (pre,post) power sign div =
  check_required_library (cdir@["Ring_base"]);
  let env = Global.env() in
  let sigma = Evd.empty in
  let (kind,r,zero,one,add,mul,sub,opp,req) = dest_ring env sigma rth in
  let (sth,ext) = build_setoid_params r add mul opp req eqth in
  let (pow_tac, pspec) = interp_power env power in 
  let sspec = interp_sign env sign in
  let dspec = interp_div env div in
  let rk = reflect_coeff morphth in
  let params =
    exec_tactic env 5 (zltac "ring_lemmas") 
      (List.map carg[sth;ext;rth;pspec;sspec;dspec;rk]) in
  let lemma1 = constr_of params.(3) in
  let lemma2 = constr_of params.(4) in

  let lemma1 = decl_constant (string_of_id name^"_ring_lemma1") lemma1 in
  let lemma2 = decl_constant (string_of_id name^"_ring_lemma2") lemma2 in
  let cst_tac =
    interp_cst_tac env sigma morphth kind (zero,one,add,mul,opp) cst_tac in
  let pretac =
    match pre with
        Some t -> Tacinterp.glob_tactic t
      | _ -> TacId [] in
  let posttac =
    match post with
        Some t -> Tacinterp.glob_tactic t
      | _ -> TacId [] in
  let _ =
    Lib.add_leaf name
      (theory_to_obj
        { ring_carrier = r;
          ring_req = req;
          ring_setoid = sth;
          ring_ext = constr_of params.(1);
          ring_morph = constr_of params.(2);
          ring_th = constr_of params.(0);
          ring_cst_tac = cst_tac;
	  ring_pow_tac = pow_tac;
          ring_lemma1 = lemma1;
          ring_lemma2 = lemma2;
          ring_pre_tac = pretac;
          ring_post_tac = posttac }) in
  ()

type ring_mod =
    Ring_kind of coeff_spec
  | Const_tac of cst_tac_spec
  | Pre_tac of raw_tactic_expr
  | Post_tac of raw_tactic_expr
  | Setoid of Topconstr.constr_expr * Topconstr.constr_expr
  | Pow_spec of cst_tac_spec * Topconstr.constr_expr
           (* Syntaxification tactic , correctness lemma *)
  | Sign_spec of Topconstr.constr_expr
  | Div_spec of Topconstr.constr_expr


VERNAC ARGUMENT EXTEND ring_mod
  | [ "decidable" constr(eq_test) ] -> [ Ring_kind(Computational (ic eq_test)) ]
  | [ "abstract" ] -> [ Ring_kind Abstract ]
  | [ "morphism" constr(morph) ] -> [ Ring_kind(Morphism (ic morph)) ]
  | [ "constants" "[" tactic(cst_tac) "]" ] -> [ Const_tac(CstTac cst_tac) ]
  | [ "closed" "[" ne_global_list(l) "]" ] -> [ Const_tac(Closed l) ]
  | [ "preprocess" "[" tactic(pre) "]" ] -> [ Pre_tac pre ]
  | [ "postprocess" "[" tactic(post) "]" ] -> [ Post_tac post ]
  | [ "setoid" constr(sth) constr(ext) ] -> [ Setoid(sth,ext) ]
  | [ "sign" constr(sign_spec) ] -> [ Sign_spec sign_spec ]
  | [ "power" constr(pow_spec) "[" ne_global_list(l) "]" ] ->
           [ Pow_spec (Closed l, pow_spec) ]   
  | [ "power_tac" constr(pow_spec) "[" tactic(cst_tac) "]" ] ->
           [ Pow_spec (CstTac cst_tac, pow_spec) ]
  | [ "div" constr(div_spec) ] -> [ Div_spec div_spec ]
END

let set_once s r v =
  if !r = None then r := Some v else error (s^" cannot be set twice")

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
      Ring_kind k -> set_once "ring kind" kind k
    | Const_tac t -> set_once "tactic recognizing constants" cst_tac t
    | Pre_tac t -> set_once "preprocess tactic" pre t
    | Post_tac t -> set_once "postprocess tactic" post t
    | Setoid(sth,ext) -> set_once "setoid" set (ic sth,ic ext) 
    | Pow_spec(t,spec) -> set_once "power" power (t,spec)
    | Sign_spec t -> set_once "sign" sign t
    | Div_spec t -> set_once "div" div t) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !cst_tac, !pre, !post, !power, !sign, !div)

VERNAC COMMAND EXTEND AddSetoidRing
  | [ "Add" "Ring" ident(id) ":" constr(t) ring_mods(l) ] ->
    [ let (k,set,cst,pre,post,power,sign, div) = process_ring_mods l in
      add_theory id (ic t) set k cst (pre,post) power sign div]
END

(*****************************************************************************)
(* The tactics consist then only in a lookup in the ring database and
   call the appropriate ltac. *)

let make_args_list rl t = 
  match rl with
  | [] -> let (_,t1,t2) = dest_rel0 t in [t1;t2]
  | _ -> rl

let make_term_list carrier rl =
  List.fold_right
    (fun x l -> lapp coq_cons [|carrier;x;l|]) rl
    (lapp coq_nil [|carrier|])


let ring_lookup (f:glob_tactic_expr) lH rl t gl =
  let env = pf_env gl in
  let sigma = project gl in
  let rl = make_args_list rl t in
  let e = find_ring_structure env sigma rl None in
  let rl = carg (make_term_list e.ring_carrier rl) in
  let lH = carg (make_hyp_list env lH) in
  let req = carg e.ring_req in
  let sth = carg e.ring_setoid in
  let ext = carg e.ring_ext in
  let morph = carg e.ring_morph in
  let th = carg e.ring_th in
  let cst_tac = Tacexp e.ring_cst_tac in
  let pow_tac = Tacexp e.ring_pow_tac in
  let lemma1 = carg e.ring_lemma1 in
  let lemma2 = carg e.ring_lemma2 in
  let pretac = Tacexp(TacFun([None],e.ring_pre_tac)) in
  let posttac = Tacexp(TacFun([None],e.ring_post_tac)) in
  Tacinterp.eval_tactic
    (TacLetIn
      (false,[(dummy_loc,id_of_string"f"),Tacexp f],
       ltac_lcall "f"
         [req;sth;ext;morph;th;cst_tac;pow_tac;
          lemma1;lemma2;pretac;posttac;lH;rl])) gl

TACTIC EXTEND ring_lookup
| [ "ring_lookup" tactic0(f) "[" constr_list(lH) "]" ne_constr_list(lrt) ] ->
    [ let (t,lr) = list_sep_last lrt in ring_lookup (fst f) lH lr t]
END


 
(***********************************************************************)

let new_field_path =
  make_dirpath (List.map id_of_string ["Field_tac";contrib_name;"Coq"])

let field_ltac s =
  lazy(make_kn (MPfile new_field_path) (make_dirpath []) (mk_label s))


let _ = add_map "field"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    (* display_linear: evaluate polynomials and coef operations, protect
       field operations and make recursive call on the var map *)
    my_constant "display_linear",
      (function -1|9|10|11|12|13|15|16->Eval|14->Rec|_->Prot);
    my_constant "display_pow_linear",
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
    my_constant "FEeval", (function -1|8|9|10|11|14->Eval|13->Rec|_->Prot)]);;

let _ = add_map "field_cond"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
     coq_nil, (function -1->Eval|_ -> Prot);
    (* PCond: evaluate morphism and denum list, protect ring
       operations and make recursive call on the var map *)
     my_constant "PCond", (function -1|8|10|13->Eval|12->Rec|_->Prot)]);;
(*                       (function -1|8|10->Eval|9->Rec|_->Prot)]);;*)


let afield_theory = my_constant "almost_field_theory"
let field_theory = my_constant "field_theory"
let sfield_theory = my_constant "semi_field_theory"
let af_ar = my_constant"AF_AR"
let f_r = my_constant"F_R"
let sf_sr = my_constant"SF_SR"
let dest_field env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match kind_of_term th_typ with
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when f = Lazy.force afield_theory ->
        let rth = lapp af_ar
          [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (None,r,zero,one,add,mul,Some sub,Some opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when f = Lazy.force field_theory ->
        let rth =
          lapp f_r
            [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (Some false,r,zero,one,add,mul,Some sub,Some opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;div;inv;req|])
        when f = Lazy.force sfield_theory ->
        let rth = lapp sf_sr
          [|r;zero;one;add;mul;div;inv;req;th_spec|] in
        (Some true,r,zero,one,add,mul,None,None,div,inv,req,rth)
    | _ -> error "bad field structure"

type field_info =
    { field_carrier : types;
      field_req : constr;
      field_cst_tac : glob_tactic_expr;
      field_pow_tac : glob_tactic_expr;
      field_ok : constr;
      field_simpl_eq_ok : constr;
      field_simpl_ok : constr;
      field_simpl_eq_in_ok : constr;
      field_cond : constr;
      field_pre_tac : glob_tactic_expr;
      field_post_tac : glob_tactic_expr }

let field_from_carrier = ref Cmap.empty
let field_from_relation = ref Cmap.empty
let field_from_name = ref Spmap.empty


let field_for_carrier r = Cmap.find r !field_from_carrier
let field_for_relation rel = Cmap.find rel !field_from_relation
let field_lookup_by_name ref =
  Spmap.find (Nametab.locate_obj (snd(qualid_of_reference ref)))
    !field_from_name


let find_field_structure env sigma l oname =
  check_required_library (cdir@["Field_tac"]);
  match oname, l with
      Some rf, _ ->
        (try field_lookup_by_name rf
        with Not_found ->
          errorlabstrm "field"
            (str "found no field named "++pr_reference rf))
    | None, t::cl' ->
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
    | None, [] -> assert false
(*        let (req,_,_) = dest_rel cl in
        (try field_for_relation req
        with Not_found ->
          errorlabstrm "field"
            (str"cannot find a declared field structure for equality"++
             spc()++str"\""++pr_constr req++str"\"")) *)

let _ = 
  Summary.declare_summary "tactic-new-field-table"
    { Summary.freeze_function =
        (fun () -> !field_from_carrier,!field_from_relation,!field_from_name);
      Summary.unfreeze_function =
        (fun (ct,rt,nt) ->
          field_from_carrier := ct; field_from_relation := rt;
          field_from_name := nt);
      Summary.init_function =
        (fun () ->
          field_from_carrier := Cmap.empty; field_from_relation := Cmap.empty;
          field_from_name := Spmap.empty);
      Summary.survive_module = false;
      Summary.survive_section = false }

let add_field_entry (sp,_kn) e =
(*
  let _ = ty e.field_ok in
  let _ = ty e.field_simpl_eq_ok in
  let _ = ty e.field_simpl_ok in
  let _ = ty e.field_cond in
*)
  field_from_carrier := Cmap.add e.field_carrier e !field_from_carrier;
  field_from_relation := Cmap.add e.field_req e !field_from_relation;
  field_from_name := Spmap.add sp e !field_from_name 

let subst_th (_,subst,th) = 
  let c' = subst_mps subst th.field_carrier in                   
  let eq' = subst_mps subst th.field_req in
  let thm1' = subst_mps subst th.field_ok in
  let thm2' = subst_mps subst th.field_simpl_eq_ok in
  let thm3' = subst_mps subst th.field_simpl_ok in
  let thm4' = subst_mps subst th.field_simpl_eq_in_ok in
  let thm5' = subst_mps subst th.field_cond in
  let tac'= subst_tactic subst th.field_cst_tac in
  let pow_tac' = subst_tactic subst th.field_pow_tac in
  let pretac'= subst_tactic subst th.field_pre_tac in
  let posttac'= subst_tactic subst th.field_post_tac in
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

let (ftheory_to_obj, obj_to_ftheory) = 
  let cache_th (name,th) = add_field_entry name th
  and export_th x = Some x in
  declare_object
    {(default_object "tactic-new-field-theory") with
      open_function = (fun i o -> if i=1 then cache_th o);
      cache_function = cache_th;
      subst_function = subst_th;
      classify_function = (fun (_,x) -> Substitute x);
      export_function = export_th }

let field_equality r inv req =
  match kind_of_term req with
    | App (f, [| _ |]) when eq_constr f (Lazy.force coq_eq) ->
        mkApp((Coqlib.build_coq_eq_data()).congr,[|r;r;inv|])
    | _ ->
	let _setoid = setoid_of_relation (Global.env ()) r req in
	let signature = [Some (r,req)],Some(Lazy.lazy_from_val (r,req)) in
	let inv_m, inv_m_lem =
	  try Class_tactics.default_morphism signature inv
          with Not_found ->
            error "field inverse should be declared as a morphism" in
	  inv_m_lem
	    
let add_field_theory name fth eqth morphth cst_tac inj (pre,post) power sign odiv =
  check_required_library (cdir@["Field_tac"]);
  let env = Global.env() in
  let sigma = Evd.empty in
  let (kind,r,zero,one,add,mul,sub,opp,div,inv,req,rth) =
    dest_field env sigma fth in
  let (sth,ext) = build_setoid_params r add mul opp req eqth in
  let eqth = Some(sth,ext) in
  let _ = add_theory name rth eqth morphth cst_tac (None,None) power sign odiv in
  let (pow_tac, pspec) = interp_power env power in 
  let sspec = interp_sign env sign in
  let dspec = interp_div env odiv in
  let inv_m = field_equality r inv req in
  let rk = reflect_coeff morphth in
  let params =
    exec_tactic env 9 (field_ltac"field_lemmas")
      (List.map carg[sth;ext;inv_m;fth;pspec;sspec;dspec;rk]) in
  let lemma1 = constr_of params.(3) in
  let lemma2 = constr_of params.(4) in
  let lemma3 = constr_of params.(5) in
  let lemma4 = constr_of params.(6) in
  let cond_lemma =
    match inj with
      | Some thm -> mkApp(constr_of params.(8),[|thm|])
      | None -> constr_of params.(7) in
  let lemma1 = decl_constant (string_of_id name^"_field_lemma1") lemma1 in
  let lemma2 = decl_constant (string_of_id name^"_field_lemma2") lemma2 in
  let lemma3 = decl_constant (string_of_id name^"_field_lemma3") lemma3 in
  let lemma4 = decl_constant (string_of_id name^"_field_lemma4") lemma4 in
  let cond_lemma = decl_constant (string_of_id name^"_lemma5") cond_lemma in
  let cst_tac =
    interp_cst_tac env sigma morphth kind (zero,one,add,mul,opp) cst_tac in
  let pretac =
    match pre with
        Some t -> Tacinterp.glob_tactic t
      | _ -> TacId [] in
  let posttac =
    match post with
        Some t -> Tacinterp.glob_tactic t
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

type field_mod =
    Ring_mod of ring_mod
  | Inject of Topconstr.constr_expr

VERNAC ARGUMENT EXTEND field_mod
  | [ ring_mod(m) ] -> [ Ring_mod m ]
  | [ "completeness" constr(inj) ] -> [ Inject inj ]
END

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
      Ring_mod(Ring_kind k) -> set_once "field kind" kind k
    | Ring_mod(Const_tac t) ->
        set_once "tactic recognizing constants" cst_tac t
    | Ring_mod(Pre_tac t) -> set_once "preprocess tactic" pre t
    | Ring_mod(Post_tac t) -> set_once "postprocess tactic" post t
    | Ring_mod(Setoid(sth,ext)) -> set_once "setoid" set (ic sth,ic ext)
    | Ring_mod(Pow_spec(t,spec)) -> set_once "power" power (t,spec)
    | Ring_mod(Sign_spec t) -> set_once "sign" sign t
    | Ring_mod(Div_spec t) -> set_once "div" div t
    | Inject i -> set_once "infinite property" inj (ic i)) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !inj, !cst_tac, !pre, !post, !power, !sign, !div)

VERNAC COMMAND EXTEND AddSetoidField
| [ "Add" "Field" ident(id) ":" constr(t) field_mods(l) ] -> 
  [ let (k,set,inj,cst_tac,pre,post,power,sign,div) = process_field_mods l in
    add_field_theory id (ic t) set k cst_tac inj (pre,post) power sign div]
END

let field_lookup (f:glob_tactic_expr) lH rl t gl =
  let env = pf_env gl in
  let sigma = project gl in
  let rl = make_args_list rl t in
  let e = find_field_structure env sigma rl None in
  let rl = carg (make_term_list e.field_carrier rl) in
  let lH = carg (make_hyp_list env lH) in
  let req = carg e.field_req in
  let cst_tac = Tacexp e.field_cst_tac in
  let pow_tac = Tacexp e.field_pow_tac in
  let field_ok = carg e.field_ok in
  let field_simpl_ok = carg e.field_simpl_ok in
  let field_simpl_eq_ok = carg e.field_simpl_eq_ok in
  let field_simpl_eq_in_ok = carg e.field_simpl_eq_in_ok in
  let cond_ok = carg e.field_cond in
  let pretac = Tacexp(TacFun([None],e.field_pre_tac)) in
  let posttac = Tacexp(TacFun([None],e.field_post_tac)) in
  Tacinterp.eval_tactic
    (TacLetIn
      (false,[(dummy_loc,id_of_string"f"),Tacexp f],
       ltac_lcall "f"
        [req;cst_tac;pow_tac;field_ok;field_simpl_ok;field_simpl_eq_ok;
         field_simpl_eq_in_ok;cond_ok;pretac;posttac;lH;rl])) gl

TACTIC EXTEND field_lookup
| [ "field_lookup" tactic0(f) "[" constr_list(lH) "]" ne_constr_list(lt) ] -> 
      [ let (t,l) = list_sep_last lt in field_lookup (fst f) lH l t ]
END
