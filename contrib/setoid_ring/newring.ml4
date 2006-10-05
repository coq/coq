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
  Tactics.reduct_option (protect_red map,DEFAULTcast) (Some(([],id),InHyp));;


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
(* Library linking *)

let contrib_name = "setoid_ring"


let ring_dir = ["Coq";contrib_name]
let ring_modules = 
  [ring_dir@["BinList"];ring_dir@["Ring_theory"];ring_dir@["Ring_polynom"];
   ring_dir@["Ring_tac"];ring_dir@["Field_tac"];ring_dir@["InitialRing"]]
let stdlib_modules =
  [["Coq";"Setoids";"Setoid"];
   ["Coq";"ZArith";"BinInt"];
   ["Coq";"ZArith";"Zbool"];
   ["Coq";"NArith";"BinNat"];
   ["Coq";"NArith";"BinPos"]]

let coq_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" stdlib_modules c)
let ring_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" ring_modules c)
let ringtac_constant m c =
  lazy (Coqlib.gen_constant_in_modules "Ring" [ring_dir@["InitialRing";m]] c)

let new_ring_path =
  make_dirpath (List.map id_of_string ["Ring_tac";contrib_name;"Coq"])
let ltac s =
  lazy(make_kn (MPfile new_ring_path) (make_dirpath []) (mk_label s))
let znew_ring_path =
  make_dirpath (List.map id_of_string ["InitialRing";contrib_name;"Coq"])
let zltac s =
  lazy(make_kn (MPfile znew_ring_path) (make_dirpath []) (mk_label s))
let carg c = TacDynamic(dummy_loc,Pretyping.constr_in c)

let mk_cst l s = lazy (Coqlib.gen_constant "newring" l s);;
let pol_cst s = mk_cst [contrib_name;"Ring_polynom"] s ;;

(* Ring theory *)

(* almost_ring defs *)
let coq_almost_ring_theory = ring_constant "almost_ring_theory"
let coq_ring_lemma1 = ring_constant "ring_correct"
let coq_ring_lemma2 = ring_constant "Pphi_dev_ok"
let ring_comp1 = ring_constant "ring_id_correct"
let ring_comp2 = ring_constant "ring_rw_id_correct"
let ring_abs1 = ringtac_constant "Zpol" "ring_gen_correct"
let ring_abs2 = ringtac_constant "Zpol" "ring_rw_gen_correct"
let sring_abs1 = ringtac_constant "Npol" "ring_gen_correct"
let sring_abs2 = ringtac_constant "Npol" "ring_rw_gen_correct"

(* setoid and morphism utilities *)
let coq_mk_Setoid = coq_constant "Build_Setoid_Theory"
let coq_eq_setoid = ring_constant "Eqsth"
let coq_eq_morph = ring_constant "Eq_ext"

(* ring -> almost_ring utilities *)
let coq_ring_theory = ring_constant "ring_theory"
let coq_ring_morph = ring_constant "ring_morph"
let coq_Rth_ARth = ring_constant "Rth_ARth"
let coq_mk_reqe = ring_constant "mk_reqe"

(* semi_ring -> almost_ring utilities *)
let coq_semi_ring_theory = ring_constant "semi_ring_theory"
let coq_SRth_ARth = ring_constant "SRth_ARth"
let coq_sring_morph = ring_constant "semi_morph"
let coq_SRmorph_Rmorph = ring_constant "SRmorph_Rmorph"
let coq_mk_seqe = ring_constant "mk_seqe"
let coq_SRsub = ring_constant "SRsub"
let coq_SRopp = ring_constant "SRopp"
let coq_SReqe_Reqe = ring_constant "SReqe_Reqe"

let ltac_setoid_ring = ltac"Ring"
let ltac_setoid_ring_rewrite = ltac"Ring_simplify"
let ltac_inv_morphZ = zltac"inv_gen_phiZ"
let ltac_inv_morphN = zltac"inv_gen_phiN"


let list_dir = ["Lists";"List"]
(* let list_dir =[contrib_name;"BinList"] *)
let coq_cons = mk_cst list_dir "cons"
let coq_nil = mk_cst list_dir "nil"

let lapp f args = mkApp(Lazy.force f,args)

let rec dest_rel t =
  match kind_of_term t with
      App(f,args) when Array.length args >= 2 ->
        let rel = mkApp(f,Array.sub args 0 (Array.length args - 2)) in
        if closed0 rel then
          (rel,args.(Array.length args - 2),args.(Array.length args - 1))
        else error "ring: cannot find relation (not closed)"
    | Prod(_,_,c) -> dest_rel c
    | _ -> error "ring: cannot find relation"

(* Equality: do not evaluate but make recursive call on both sides *)
let map_with_eq arg_map c =
  let (req,_,_) = dest_rel c in
  interp_map
    ((req,(function -1->Prot|_->Rec))::
    List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)
;;

let _ = add_map "ring"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
    pol_cst "Pphi_dev", (function -1|6|7|8|9|11->Eval|10->Rec|_->Prot);
    (* PEeval: evaluate morphism and polynomial, protect ring 
       operations and make recursive call on the var map *)
    pol_cst "PEeval", (function -1|7|9->Eval|8->Rec|_->Prot)]);;

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


let ltac_call tac args =
  TacArg(TacCall(dummy_loc, ArgArg(dummy_loc, Lazy.force tac),args))

(****************************************************************************)
(* Ring database *)

type ring_info =
    { ring_carrier : types;
      ring_req : constr;
      ring_cst_tac : glob_tactic_expr;
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


let find_ring_structure env sigma l cl oname =
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
    | None, [] ->
        let (req,_,_) = dest_rel cl in
        (try ring_for_relation req
        with Not_found ->
          errorlabstrm "ring"
            (str"cannot find a declared ring structure for equality"++
             spc()++str"\""++pr_constr req++str"\""))

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
  let thm1' = subst_mps subst th.ring_lemma1 in
  let thm2' = subst_mps subst th.ring_lemma2 in
  let tac'= subst_tactic subst th.ring_cst_tac in
  let pretac'= subst_tactic subst th.ring_pre_tac in
  let posttac'= subst_tactic subst th.ring_post_tac in
  if c' == th.ring_carrier &&
     eq' == th.ring_req &&
     thm1' == th.ring_lemma1 &&
     thm2' == th.ring_lemma2 &&
     tac' == th.ring_cst_tac &&
     pretac' == th.ring_pre_tac &&
     posttac' == th.ring_post_tac then th
  else
    { ring_carrier = c';
      ring_req = eq';
      ring_cst_tac = tac';
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


let setoid_of_relation r =
  lapp coq_mk_Setoid
    [|r.rel_a; r.rel_aeq;
      out_some r.rel_refl; out_some r.rel_sym; out_some r.rel_trans |]

let op_morph r add mul opp req m1 m2 m3 =
  lapp coq_mk_reqe [| r; add; mul; opp; req; m1; m2; m3 |]

let op_smorph r add mul req m1 m2 =
  lapp coq_mk_seqe [| r; add; mul; req; m1; m2 |]

let smorph2morph r add mul req sm =
  lapp coq_SReqe_Reqe [| r;add;mul;req;sm|]

let sr_sub r add = lapp coq_SRsub [|r;add|]
let sr_opp r = lapp coq_SRopp [|r|]

let dest_morphism env sigma kind th sth =
  let th_typ = Retyping.get_type_of env sigma th in
  match kind_of_term th_typ with
      App(f,[|_;_;_;_;_;_;_;_;c;czero;cone;cadd;cmul;csub;copp;ceqb;phi|])
        when f = Lazy.force coq_ring_morph ->
          (th,[|c;czero;cone;cadd;cmul;csub;copp;ceqb;phi|])
    | App(f,[|r;zero;one;add;mul;req;c;czero;cone;cadd;cmul;ceqb;phi|])
        when f = Lazy.force coq_sring_morph && kind=Some true->
        let th =
          lapp coq_SRmorph_Rmorph
            [|r;zero;one;add;mul;req;sth;c;czero;cone;cadd;cmul;ceqb;phi;th|]in
        (th,[|c;czero;cone;cadd;cmul;cadd;sr_opp c;ceqb;phi|])
    | _ -> error "bad ring_morph lemma"

let dest_eq_test env sigma th =
  let th_typ = Retyping.get_type_of env sigma th in
  match decompose_prod th_typ with
      (_,h)::_,_ ->
        (match snd(destApplication h) with
            [|_;lhs;_|] ->
              let (f,args) = destApplication lhs in
              if Array.length args < 2 then
                error "bad lemma for decidability of equality"
              else
                mkApp(f,Array.sub args 0 (Array.length args -2))
          | _ -> error "bad lemma for decidability of equality")
    | _ -> error "bad lemma for decidability of equality"

let default_ring_equality is_semi (r,add,mul,opp,req) =
  let is_setoid = function
      {rel_refl=Some _; rel_sym=Some _;rel_trans=Some _} -> true
    | _ -> false in
  match default_relation_for_carrier ~filter:is_setoid r with
      Leibniz _ ->
        let setoid = lapp coq_eq_setoid [|r|] in
        let op_morph = lapp coq_eq_morph [|r;add;mul;opp|] in
        (setoid,op_morph)
    | Relation rel ->
        let setoid = setoid_of_relation rel in
        let is_endomorphism = function
            { args=args } -> List.for_all
                (function (var,Relation rel) ->
                  var=None && eq_constr req rel
                  | _ -> false) args in
        let add_m =
          try default_morphism ~filter:is_endomorphism add
          with Not_found ->
            error "ring addition should be declared as a morphism" in
        let mul_m =
          try default_morphism ~filter:is_endomorphism mul
          with Not_found ->
            error "ring multiplication should be declared as a morphism" in
        let op_morph =
          if is_semi <> Some true then
            (let opp_m =
              try default_morphism ~filter:is_endomorphism opp
              with Not_found ->
                error "ring opposite should be declared as a morphism" in
             let op_morph =
               op_morph r add mul opp req add_m.lem mul_m.lem opp_m.lem in
             msgnl
               (str"Using setoid \""++pr_constr rel.rel_aeq++str"\""++spc()++  
               str"and morphisms \""++pr_constr add_m.morphism_theory++
               str"\","++spc()++ str"\""++pr_constr mul_m.morphism_theory++
               str"\""++spc()++str"and \""++pr_constr opp_m.morphism_theory++
               str"\"");
             op_morph)
          else
            (msgnl
              (str"Using setoid \""++pr_constr rel.rel_aeq++str"\"" ++ spc() ++  
               str"and morphisms \""++pr_constr add_m.morphism_theory++
               str"\""++spc()++str"and \""++
               pr_constr mul_m.morphism_theory++str"\"");
            op_smorph r add mul req add_m.lem mul_m.lem) in
        (setoid,op_morph)

let build_setoid_params is_semi r add mul opp req eqth =
  match eqth with
      Some th -> th
    | None -> default_ring_equality is_semi (r,add,mul,opp,req)

let dest_ring env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match kind_of_term th_typ with
      App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when f = Lazy.force coq_almost_ring_theory ->
          (None,r,zero,one,add,mul,sub,opp,req)
    | App(f,[|r;zero;one;add;mul;req|])
        when f = Lazy.force coq_semi_ring_theory ->
        (Some true,r,zero,one,add,mul,sr_sub r add,sr_opp r,req)
    | App(f,[|r;zero;one;add;mul;sub;opp;req|])
        when f = Lazy.force coq_ring_theory ->
        (Some false,r,zero,one,add,mul,sub,opp,req)
    | _ -> error "bad ring structure"


let build_almost_ring kind r zero one add mul sub opp req sth morph th =
  match kind with
      None -> th
    | Some true ->
        lapp coq_SRth_ARth [|r;zero;one;add;mul;req;sth;th|]
    | Some false ->
        lapp coq_Rth_ARth [|r;zero;one;add;mul;sub;opp;req;sth;morph;th|]


type coeff_spec =
    Computational of constr (* equality test *)
  | Abstract (* coeffs = Z *)
  | Morphism of constr (* general morphism *)

type cst_tac_spec =
    CstTac of raw_tactic_expr
  | Closed of reference list

(*
let ring_equiv_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" [ring_dir@["Ring_equiv"]] c)
let ring_def_eqb_ok = ring_equiv_constant "default_eqb_ok"
let ring_equiv2 = ring_equiv_constant "ring_equiv2"
let sring_equiv2 = ring_equiv_constant "sring_equiv2"
let ring_m_plus = ring_constant "Radd_ext"
let ring_m_mul = ring_constant "Rmul_ext"
let ring_m_opp = ring_constant "Ropp_ext"

let old_morph is_semi r add mul opp req morph =
    { Ring.plusm = lapp ring_m_plus [|r;add;mul;opp;req;morph|];
      Ring.multm  = lapp ring_m_mul [|r;add;mul;opp;req;morph|];
      Ring.oppm =
        if is_semi then None
        else Some (lapp ring_m_opp [|r;add;mul;opp;req;morph|])
    }

let add_old_theory env sigma is_semi is_setoid
      r zero one add mul sub opp req rth sth ops_morph morphth =
(try
  let opp_o = if is_semi then None else Some opp in
  let (is_abs, eqb_ok) =
    match morphth with
        Computational c -> (false, c)
      | _ -> (true, lapp ring_def_eqb_ok [|r|]) in
  let eqb = dest_eq_test env sigma eqb_ok in
  let rth =
    if is_setoid then failwith "not impl"
    else
      if is_semi then
        lapp sring_equiv2 [|r;zero;one;add;mul;rth;eqb;eqb_ok|]
      else
        lapp ring_equiv2 [|r;zero;one;add;mul;sub;opp;rth;eqb;eqb_ok|] in
  Ring.add_theory (not is_semi) is_abs is_setoid r
     (Some req) (Some sth)
     (if is_setoid then Some(old_morph is_semi r add mul opp req ops_morph)
      else None)
     add mul one zero opp_o eqb rth Quote.ConstrSet.empty
with _ ->
  prerr_endline "Warning: could not add old ring structure")
*)

let add_theory name rth eqth morphth cst_tac (pre,post) =
  let env = Global.env() in
  let sigma = Evd.empty in
  let (kind,r,zero,one,add,mul,sub,opp,req) = dest_ring env sigma rth in
  let (sth,morph) = build_setoid_params kind r add mul opp req eqth in
  let args0 = [|r;zero;one;add;mul;sub;opp;req;sth;morph|] in
  let args0' = [|r;zero;one;add;mul;req;sth;morph|] in
  let (lemma1,lemma2) =
    match morphth with
      | Computational c ->
          let reqb = dest_eq_test env sigma c in
          let rth = 
            build_almost_ring
              kind r zero one add mul sub opp req sth  morph rth in
          let args = Array.append args0 [|rth;reqb;c|] in
          (lapp ring_comp1 args, lapp ring_comp2 args)
      | Morphism m ->
          let (m,args1) = dest_morphism env sigma kind m sth in
          let rth = 
            build_almost_ring
              kind r zero one add mul sub opp req sth morph rth in
          let args = Array.concat [args0;[|rth|]; args1; [|m|]] in
          (lapp coq_ring_lemma1 args, lapp coq_ring_lemma2 args)
      | Abstract ->
          (try check_required_library (ring_dir@["Ring"])
          with UserError _ ->
            error "You must require \"Ring\" to declare an abstract ring");
          (match kind with
              None -> error "an almost_ring cannot be abstract"
            | Some true ->
                let args1 = Array.append args0' [|rth|] in
                (lapp sring_abs1 args1, lapp sring_abs2 args1)
            | Some false ->
                let args1 = Array.append args0 [|rth|] in
                (lapp ring_abs1 args1, lapp ring_abs2 args1)) in
  let lemma1 = decl_constant (string_of_id name^"_ring_lemma1") lemma1 in
  let lemma2 = decl_constant (string_of_id name^"_ring_lemma2") lemma2 in
  let cst_tac = match cst_tac with
      Some (CstTac t) -> Tacinterp.glob_tactic t
    | Some (Closed lc) -> closed_term_ast (List.map Nametab.global lc)
    | None ->
        (match kind with
            Some true ->
              let t = ArgArg(dummy_loc,Lazy.force ltac_inv_morphN) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul]))
          | Some false ->
              let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morphZ) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul;opp]))
          | _ -> error"a tactic must be specified for an almost_ring") in
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
          ring_cst_tac = cst_tac;
          ring_lemma1 = lemma1;
          ring_lemma2 = lemma2;
          ring_pre_tac = pretac;
          ring_post_tac = posttac }) in
  (* old ring theory *)
(*  let _ =
    match kind with
        Some is_semi ->
          add_old_theory env sigma is_semi (eqth <> None)
            r zero one add mul sub opp req rth sth morph morphth
      | _ -> () in
*)
  ()

type ring_mod =
    Ring_kind of coeff_spec
  | Const_tac of cst_tac_spec
  | Pre_tac of raw_tactic_expr
  | Post_tac of raw_tactic_expr
  | Setoid of Topconstr.constr_expr * Topconstr.constr_expr

VERNAC ARGUMENT EXTEND ring_mod
  | [ "decidable" constr(eq_test) ] -> [ Ring_kind(Computational (ic eq_test)) ]
  | [ "abstract" ] -> [ Ring_kind Abstract ]
  | [ "morphism" constr(morph) ] -> [ Ring_kind(Morphism (ic morph)) ]
  | [ "constants" "[" tactic(cst_tac) "]" ] -> [ Const_tac(CstTac cst_tac) ]
  | [ "closed" "[" ne_global_list(l) "]" ] -> [ Const_tac(Closed l) ]
  | [ "preprocess" "[" tactic(pre) "]" ] -> [ Pre_tac pre ]
  | [ "postprocess" "[" tactic(post) "]" ] -> [ Post_tac post ]
  | [ "setoid" constr(sth) constr(ext) ] -> [ Setoid(sth,ext) ]
END

let set_once s r v =
  if !r = None then r := Some v else error (s^" cannot be set twice")

let process_ring_mods l =
  let kind = ref None in
  let set = ref None in
  let cst_tac = ref None in
  let pre = ref None in
  let post = ref None in
  List.iter(function
      Ring_kind k -> set_once "ring kind" kind k
    | Const_tac t -> set_once "tactic recognizing constants" cst_tac t
    | Pre_tac t -> set_once "preprocess tactic" pre t
    | Post_tac t -> set_once "postprocess tactic" post t
    | Setoid(sth,ext) -> set_once "setoid" set (ic sth,ic ext)) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !cst_tac, !pre, !post)

VERNAC COMMAND EXTEND AddSetoidRing
  | [ "Add" "Ring" ident(id) ":" constr(t) ring_mods(l) ] ->
    [ let (k,set,cst,pre,post) = process_ring_mods l in
      add_theory id (ic t) set k cst (pre,post) ]
END

(*****************************************************************************)
(* The tactics consist then only in a lookup in the ring database and
   call the appropriate ltac. *)

let ring gl = 
  let env = pf_env gl in
  let sigma = project gl in
  let e = find_ring_structure env sigma [] (pf_concl gl) None in
  let main_tac =
    ltac_call ltac_setoid_ring
      (Tacexp e.ring_cst_tac:: List.map carg [e.ring_lemma1;e.ring_req]) in
  Tacinterp.eval_tactic (TacThen(e.ring_pre_tac,main_tac)) gl

let ring_rewrite rl gl =
  let env = pf_env gl in
  let sigma = project gl in
  let e = find_ring_structure env sigma rl (pf_concl gl) None in
  tclTHEN (Tacinterp.eval_tactic e.ring_pre_tac)
    (tclTHEN
        (fun gl ->
	    let rl = 
	      match rl with
		  [] -> let (_,t1,t2) = dest_rel (pf_concl gl) in [t1;t2]
		| _ -> rl in
	    let rl = List.fold_right
	      (fun x l -> lapp coq_cons [|e.ring_carrier;x;l|]) rl
	      (lapp coq_nil [|e.ring_carrier|]) in
	      Tacinterp.eval_tactic 
		(TacArg(
		    TacCall(dummy_loc,
			   (ArgArg(dummy_loc,
				  Lazy.force ltac_setoid_ring_rewrite)),
			   (Tacexp e.ring_cst_tac::
			       List.map carg 
			       [e.ring_lemma2; e.ring_req; rl])))) gl)
	(Tacinterp.eval_tactic e.ring_post_tac)) gl

TACTIC EXTEND setoid_ring
  [ "ring" ] -> [ ring ]
| [ "ring_simplify" constr_list(l) ] -> [ ring_rewrite l ]
END

(***********************************************************************)
let fld_cst s = mk_cst [contrib_name;"Field_theory"] s ;;

let field_modules = List.map
  (fun f -> ["Coq";contrib_name;f])
  ["Field_theory";"Field_tac"]

let new_field_path =
  make_dirpath (List.map id_of_string ["Field_tac";contrib_name;"Coq"])

let field_constant c =
  lazy (Coqlib.gen_constant_in_modules "Field" field_modules c)

let field_ltac s =
  lazy(make_kn (MPfile new_field_path) (make_dirpath []) (mk_label s))

let field_lemma = field_constant "Fnorm_correct2"
let field_simplify_eq_lemma = field_constant "Field_simplify_eq_correct"
let field_simplify_lemma = field_constant "Pphi_dev_div_ok"

let afield_theory = field_constant "almost_field_theory"
let field_theory = field_constant "field_theory"
let sfield_theory = field_constant "semi_field_theory"
let field_Rth = field_constant "AF_AR"

let field_tac = field_ltac "Make_field_tac"
let field_simplify_eq_tac = field_ltac "Make_field_simplify_eq_tac"
let field_simplify_tac = field_ltac "Make_field_simplify_tac"


let _ = add_map "field"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
    coq_nil, (function -1->Eval|_ -> Prot);
    (* display_linear: evaluate polynomials and coef operations, protect
       field operations and make recursive call on the var map *)
    fld_cst "display_linear",
      (function -1|7|8|9|10|12|13->Eval|11->Rec|_->Prot);
    (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
    pol_cst "Pphi_dev", (function -1|6|7|8|9|11->Eval|10->Rec|_->Prot);
    (* PEeval: evaluate morphism and polynomial, protect ring 
       operations and make recursive call on the var map *)
    fld_cst "FEeval", (function -1|9|11->Eval|10->Rec|_->Prot)]);;


let _ = add_map "field_cond"
  (map_with_eq
    [coq_cons,(function -1->Eval|2->Rec|_->Prot);
     coq_nil, (function -1->Eval|_ -> Prot);
    (* PCond: evaluate morphism and denum list, protect ring
       operations and make recursive call on the var map *)
     fld_cst "PCond", (function -1|8|10->Eval|9->Rec|_->Prot)]);;


let dest_field env sigma th_spec =
  let th_typ = Retyping.get_type_of env sigma th_spec in
  match kind_of_term th_typ with
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when f = Lazy.force afield_theory ->
        let rth = lapp field_Rth
          [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (None,r,zero,one,add,mul,sub,opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;sub;opp;div;inv;req|])
        when f = Lazy.force field_theory ->
        let rth =
          lapp (field_constant"F_R")
            [|r;zero;one;add;mul;sub;opp;div;inv;req;th_spec|] in
        (Some false,r,zero,one,add,mul,sub,opp,div,inv,req,rth)
    | App(f,[|r;zero;one;add;mul;div;inv;req|])
        when f = Lazy.force sfield_theory ->
        let rth = lapp (field_constant"SF_SR")
          [|r;zero;one;add;mul;div;inv;req;th_spec|] in
        (Some true,r,zero,one,add,mul,sr_sub r add,sr_opp r,div,inv,req,rth)
    | _ -> error "bad field structure"

let build_almost_field
     kind r zero one add mul sub opp div inv req sth morph th =
  match kind with
      None -> th
    | Some true ->
        lapp (field_constant "SF2AF")
          [|r;zero;one;add;mul;div;inv;req;sth;th|]
    | Some false ->
        lapp (field_constant "F2AF")
          [|r;zero;one;add;mul;sub;opp;div;inv;req;sth;morph;th|]

type field_info =
    { field_carrier : types;
      field_req : constr;
      field_cst_tac : glob_tactic_expr;
      field_ok : constr;
      field_simpl_eq_ok : constr;
      field_simpl_ok : constr;
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


let find_field_structure env sigma l cl oname =
  check_required_library (ring_dir@["Field_tac"]);
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
    | None, [] ->
        let (req,_,_) = dest_rel cl in
        (try field_for_relation req
        with Not_found ->
          errorlabstrm "field"
            (str"cannot find a declared field structure for equality"++
             spc()++str"\""++pr_constr req++str"\""))

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
  let _ = ty e.field_ok in
  let _ = ty e.field_simpl_eq_ok in
  let _ = ty e.field_simpl_ok in
  let _ = ty e.field_cond in
  field_from_carrier := Cmap.add e.field_carrier e !field_from_carrier;
  field_from_relation := Cmap.add e.field_req e !field_from_relation;
  field_from_name := Spmap.add sp e !field_from_name 


let subst_th (_,subst,th) = 
  let c' = subst_mps subst th.field_carrier in                   
  let eq' = subst_mps subst th.field_req in
  let thm1' = subst_mps subst th.field_ok in
  let thm2' = subst_mps subst th.field_simpl_eq_ok in
  let thm3' = subst_mps subst th.field_simpl_ok in
  let thm4' = subst_mps subst th.field_cond in
  let tac'= subst_tactic subst th.field_cst_tac in
  let pretac'= subst_tactic subst th.field_pre_tac in
  let posttac'= subst_tactic subst th.field_post_tac in
  if c' == th.field_carrier &&
     eq' == th.field_req &&
     thm1' == th.field_ok &&
     thm2' == th.field_simpl_eq_ok &&
     thm3' == th.field_simpl_ok &&
     thm4' == th.field_cond &&
     tac' == th.field_cst_tac &&
     pretac' == th.field_pre_tac &&
     posttac' == th.field_post_tac then th
  else
    { field_carrier = c';
      field_req = eq';
      field_cst_tac = tac';
      field_ok = thm1';
      field_simpl_eq_ok = thm2';
      field_simpl_ok = thm3';
      field_cond = thm4';
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

let default_field_equality r inv req =
  let is_setoid = function
      {rel_refl=Some _; rel_sym=Some _;rel_trans=Some _} -> true
    | _ -> false in
  match default_relation_for_carrier ~filter:is_setoid r with
      Leibniz _ ->
        mkApp((Coqlib.build_coq_eq_data()).congr,[|r;r;inv|])
    | Relation rel ->
        let is_endomorphism = function
            { args=args } -> List.for_all
                (function (var,Relation rel) ->
                  var=None && eq_constr req rel
                  | _ -> false) args in
        let inv_m =
          try default_morphism ~filter:is_endomorphism inv
          with Not_found ->
            error "field inverse should be declared as a morphism" in
        inv_m.lem


let n_morph r zero one add mul =
[|Lazy.force(coq_constant"N");
Lazy.force(coq_constant"N0");
lapp(coq_constant"Npos")[|Lazy.force(coq_constant"xH")|];
Lazy.force(coq_constant"Nplus");
Lazy.force(coq_constant"Nmult");
Lazy.force(coq_constant"Nminus");
Lazy.force(coq_constant"Nopp");
Lazy.force(ring_constant"Neq_bool");
lapp(ring_constant"gen_phiN")[|r;zero;one;add;mul|]
|]
let z_morph r zero one add mul opp =
[|Lazy.force(coq_constant"Z");
Lazy.force(coq_constant"Z0");
lapp(coq_constant"Zpos")[|Lazy.force(coq_constant"xH")|];
Lazy.force(coq_constant"Zplus");
Lazy.force(coq_constant"Zmult");
Lazy.force(coq_constant"Zminus");
Lazy.force(coq_constant"Zopp");
Lazy.force(coq_constant"Zeq_bool");
lapp(ring_constant"gen_phiZ")[|r;zero;one;add;mul;opp|]
|]

let add_field_theory name fth eqth morphth cst_tac inj (pre,post) =
  let env = Global.env() in
  let sigma = Evd.empty in
  let (kind,r,zero,one,add,mul,sub,opp,div,inv,req,rth) =
    dest_field env sigma fth in
  let (sth,morph) = build_setoid_params None r add mul opp req eqth in
  let eqth = Some(sth,morph) in
  let _ = add_theory name rth eqth morphth cst_tac (None,None) in
  let afth = build_almost_field
    kind r zero one add mul sub opp div inv req sth morph fth in
  let inv_m = default_field_equality r inv req in
  let args0 =
    [|r;zero;one;add;mul;sub;opp;div;inv;req;sth;morph;inv_m;afth|] in
  let args0' =
    [|r;zero;one;add;mul;sub;opp;div;inv;req;sth;morph;afth|] in
  let (m,args1) =
    match morphth with
        Computational c ->
          let reqb = dest_eq_test env sigma c in
          let idphi = ring_constant "IDphi" in
          let idmorph =  lapp (ring_constant "IDmorph")
            [|r;zero;one;add;mul;sub;opp;req;sth;reqb;c|] in
          (idmorph,[|r;zero;one;add;mul;sub;opp;reqb;lapp idphi [|r|]|])
      | Morphism m ->
          dest_morphism env sigma kind m sth
      | Abstract ->
          (match kind with
              None -> error "an almost_field cannot be abstract"
            | Some true ->
                (lapp(ring_constant"gen_phiN_morph")
                  [|r;zero;one;add;mul;req;sth;morph;rth|],
                 n_morph r zero one add mul)
            | Some false ->
                (lapp(ring_constant"gen_phiZ_morph")
                  [|r;zero;one;add;mul;sub;opp;req;sth;morph;rth|],
                 z_morph r zero one add mul opp)) in
  let args = Array.concat [args0;args1;[|m|]] in
  let args' = Array.concat [args0';args1;[|m|]] in
  let lemma1 = lapp field_lemma args in
  let lemma2 = lapp field_simplify_eq_lemma args in
  let lemma3 = lapp field_simplify_lemma args in
  let lemma1 = decl_constant (string_of_id name^"_field_lemma1") lemma1 in
  let lemma2 = decl_constant (string_of_id name^"_field_lemma2") lemma2 in
  let lemma3 = decl_constant (string_of_id name^"_field_lemma3") lemma3 in
  let cond_lemma =
    match inj with
      | Some thm ->
          lapp (field_constant"Pcond_simpl_complete")
            (Array.append args' [|thm|])
      | None -> lapp (field_constant"Pcond_simpl_gen") args' in
  let cond_lemma = decl_constant (string_of_id name^"_lemma4") cond_lemma in
  let cst_tac = match cst_tac with
      Some (CstTac t) -> Tacinterp.glob_tactic t
    | Some (Closed lc) -> closed_term_ast (List.map Nametab.global lc)
    | None ->
        (match kind with
            Some true ->
              let t = ArgArg(dummy_loc,Lazy.force ltac_inv_morphN) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul]))
          | Some false ->
              let t = ArgArg(dummy_loc, Lazy.force ltac_inv_morphZ) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul;opp]))
          | _ -> error"a tactic must be specified for an almost_ring") in
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
          field_ok = lemma1;
          field_simpl_eq_ok = lemma2;
          field_simpl_ok = lemma3;
          field_cond = cond_lemma;
          field_pre_tac = pretac;
          field_post_tac = posttac }) in  ()

type field_mod =
    Ring_mod of ring_mod
  | Inject of Topconstr.constr_expr

VERNAC ARGUMENT EXTEND field_mod
  | [ ring_mod(m) ] -> [ Ring_mod m ]
  | [ "infinite" constr(inj) ] -> [ Inject inj ]
END

let process_field_mods l =
  let kind = ref None in
  let set = ref None in
  let cst_tac = ref None in
  let pre = ref None in
  let post = ref None in
  let inj = ref None in
  List.iter(function
      Ring_mod(Ring_kind k) -> set_once "field kind" kind k
    | Ring_mod(Const_tac t) ->
        set_once "tactic recognizing constants" cst_tac t
    | Ring_mod(Pre_tac t) -> set_once "preprocess tactic" pre t
    | Ring_mod(Post_tac t) -> set_once "postprocess tactic" post t
    | Ring_mod(Setoid(sth,ext)) -> set_once "setoid" set (ic sth,ic ext)
    | Inject i -> set_once "infinite property" inj (ic i)) l;
  let k = match !kind with Some k -> k | None -> Abstract in
  (k, !set, !inj, !cst_tac, !pre, !post)

VERNAC COMMAND EXTEND AddSetoidField
| [ "Add" "Field" ident(id) ":" constr(t) field_mods(l) ] -> 
  [ let (k,set,inj,cst_tac,pre,post) = process_field_mods l in
    add_field_theory id (ic t) set k cst_tac inj (pre,post) ]
END

let field gl = 
  let env = pf_env gl in
  let sigma = project gl in
  let e = find_field_structure env sigma [] (pf_concl gl) None in
  let main_tac =
    ltac_call field_tac
      [carg e.field_ok;carg e.field_cond;
       carg e.field_req; Tacexp e.field_cst_tac] in
  Tacinterp.eval_tactic
    (TacThen(e.field_pre_tac,TacThen(main_tac,e.field_post_tac))) gl

let field_simplify_eq gl =
  let env = pf_env gl in
  let sigma = project gl in
  let e = find_field_structure env sigma [] (pf_concl gl) None in
  let main_tac =
    ltac_call field_simplify_eq_tac
      [carg e.field_simpl_eq_ok;carg e.field_cond;
       carg e.field_req; Tacexp e.field_cst_tac] in
  Tacinterp.eval_tactic
    (TacThen(e.field_pre_tac,TacThen(main_tac,e.field_post_tac))) gl

let field_simplify rl gl =
  let env = pf_env gl in
  let sigma = project gl in
  let e = find_field_structure env sigma rl (pf_concl gl) None in
  let rl =
    match rl with
        [] -> let (_,t1,t2) = dest_rel (pf_concl gl) in [t1;t2]
      | _ -> rl in
  let rl = List.fold_right
    (fun x l -> lapp coq_cons [|e.field_carrier;x;l|]) rl
    (lapp coq_nil [|e.field_carrier|]) in
  let main_tac =
    ltac_call field_simplify_tac
      [carg e.field_simpl_ok;carg e.field_cond;
       carg e.field_req; Tacexp e.field_cst_tac;
       carg rl] in
  Tacinterp.eval_tactic
    (TacThen(e.field_pre_tac,TacThen(main_tac,e.field_post_tac))) gl

TACTIC EXTEND setoid_field
  [ "field" ] -> [ field ]
END
TACTIC EXTEND setoid_field_simplify
  [ "field_simplify_eq" ] -> [ field_simplify_eq ]
| [ "field_simplify" constr_list(l) ] -> [ field_simplify l ]
END
