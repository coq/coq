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
open Ppconstrnew
open Mod_subst
open Tacinterp
open Libobject

(****************************************************************************)
(* Library linking *)

let contrib_name = "setoid_ring"


let ring_dir = ["Coq";contrib_name]
let setoids_dir = ["Coq";"Setoids"]
let ring_modules = 
  [ring_dir@["BinList"];ring_dir@["Ring_th"];ring_dir@["Pol"];
   ring_dir@["Ring_tac"];ring_dir@["ZRing_th"]]
let stdlib_modules = [setoids_dir@["Setoid"]]

let coq_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" stdlib_modules c)
let ring_constant c =
  lazy (Coqlib.gen_constant_in_modules "Ring" ring_modules c)
let ringtac_constant m c =
  lazy (Coqlib.gen_constant_in_modules "Ring" [ring_dir@["ZRing_th";m]] c)

let new_ring_path =
  make_dirpath (List.map id_of_string ["Ring_tac";contrib_name;"Coq"])
let ltac s =
  lazy(make_kn (MPfile new_ring_path) (make_dirpath []) (mk_label s))
let znew_ring_path =
  make_dirpath (List.map id_of_string ["ZRing_th";contrib_name;"Coq"])
let zltac s =
  lazy(make_kn (MPfile znew_ring_path) (make_dirpath []) (mk_label s))
let carg c = TacDynamic(dummy_loc,Pretyping.constr_in c)

let mk_cst l s = lazy (Coqlib.gen_constant "newring" l s);;
let pol_cst s = mk_cst [contrib_name;"Pol"] s ;;

let ic c =
  let env = Global.env() and sigma = Evd.empty in
  Constrintern.interp_constr sigma env c


(* Ring theory *)

(* almost_ring defs *)
let coq_almost_ring_theory = ring_constant "almost_ring_theory"
let coq_ring_lemma1 = ring_constant "ring_correct"
let coq_ring_lemma2 = ring_constant "Pphi_dev_ok'"
let ring_comp1 = ring_constant "ring_id_correct"
let ring_comp2 = ring_constant "ring_rw_id_correct'"
let ring_abs1 = ringtac_constant "Zpol" "ring_gen_correct"
let ring_abs2 = ringtac_constant "Zpol" "ring_rw_gen_correct'"
let sring_abs1 = ringtac_constant "Npol" "ring_gen_correct"
let sring_abs2 = ringtac_constant "Npol" "ring_rw_gen_correct'"

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

let ltac_setoid_ring = ltac"Make_ring_tac"
let ltac_setoid_ring_rewrite = ltac"Make_ring_rw_list"
let ltac_inv_morphZ = zltac"inv_gen_phiZ"
let ltac_inv_morphN = zltac"inv_gen_phiN"

let coq_cons = ring_constant "cons"
let coq_nil = ring_constant "nil"

let lapp f args = mkApp(Lazy.force f,args)

let dest_rel t =
  match kind_of_term t with
      App(f,args) when Array.length args >= 2 ->
        mkApp(f,Array.sub args 0 (Array.length args - 2))
    | _ -> failwith "cannot find relation"

(****************************************************************************)
(* controlled reduction *)

let mark_arg i c = mkEvar(i,[|c|]);;
let unmark_arg f c =
  match destEvar c with
    | (i,[|c|]) -> f i c
    | _ -> assert false;;

type protect_flag = Eval|Prot|Rec ;;

let tag_arg tag_rec map i c =
  match map i with
      Eval -> inject c
    | Prot -> mk_atom c
    | Rec -> if i = -1 then inject c else tag_rec c

let rec mk_clos_but f_map t =
  match f_map t with
    | Some map -> tag_arg (mk_clos_but f_map) map (-1) t
    | None ->
        (match kind_of_term t with
            App(f,args) -> mk_clos_app_but f_map f args 0
          | _ -> mk_atom t)

and mk_clos_app_but f_map f args n =
  if n >= Array.length args then mk_atom(mkApp(f, args))
  else
    let fargs, args' = array_chop n args in
    let f' = mkApp(f,fargs) in
    match f_map f' with
        Some map ->
          mk_clos_deep
            (fun _ -> unmark_arg (tag_arg (mk_clos_but f_map) map))
            (Esubst.ESID 0)
            (mkApp (mark_arg (-1) f', Array.mapi mark_arg args'))
      | None -> mk_clos_app_but f_map f args (n+1)
;;

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

let arg_map =
  [mk_cst [contrib_name;"BinList"] "cons",(function -1->Eval|2->Rec|_->Prot);
   mk_cst [contrib_name;"BinList"] "nil", (function -1->Eval|_ -> Prot);
   (* Pphi_dev: evaluate polynomial and coef operations, protect
       ring operations and make recursive call on the var map *)
   pol_cst "Pphi_dev", (function -1|6|7|8|9|11->Eval|10->Rec|_->Prot);
   (* PEeval: evaluate morphism and polynomial, protect ring 
      operations and make recursive call on the var map *)
   pol_cst "PEeval", (function -1|7|9->Eval|8->Rec|_->Prot)];;

(* Equality: do not evaluate but make recursive call on both sides *)
let is_ring_thm req =
  interp_map
    ((req,(function -1->Prot|_->Rec))::
    List.map (fun (c,map) -> (Lazy.force c,map)) arg_map)
;;

let protect_red env sigma c =
  let req = dest_rel c in
  kl (create_clos_infos betadeltaiota env)
    (mk_clos_but (is_ring_thm req) c);;

let protect_tac =
  Tactics.reduct_option protect_red None ;;

let protect_tac_in id =
  Tactics.reduct_option protect_red (Some(id,[],(InHyp, ref None)));;


TACTIC EXTEND protect_fv
  [ "protect_fv" "in" ident(id) ] -> 
    [ protect_tac_in id ]
| [ "protect_fv" ] -> 
    [ protect_tac ]
END;;

(****************************************************************************)
(* Ring database *)

let ty c = Typing.type_of (Global.env()) Evd.empty c


type ring_info =
    { ring_carrier : types;
      ring_req : constr;
      ring_cst_tac : glob_tactic_expr;
      ring_lemma1 : constr;
      ring_lemma2 : constr }

module Cmap = Map.Make(struct type t = constr let compare = compare end)

let from_carrier = ref Cmap.empty
let from_relation = ref Cmap.empty

let _ = 
  Summary.declare_summary "tactic-new-ring-table"
    { Summary.freeze_function = (fun () -> !from_carrier,!from_relation);
      Summary.unfreeze_function =
        (fun (ct,rt) -> from_carrier := ct; from_relation := rt);
      Summary.init_function =
        (fun () -> from_carrier := Cmap.empty; from_relation := Cmap.empty);
      Summary.survive_module = false;
      Summary.survive_section = false }

let add_entry _ e =
  let _ = ty e.ring_lemma1 in
  let _ = ty e.ring_lemma2 in
  from_carrier := Cmap.add e.ring_carrier e !from_carrier;
  from_relation := Cmap.add e.ring_req e !from_relation


let subst_th (_,subst,th) = 
  let c' = subst_mps subst th.ring_carrier in                   
  let eq' = subst_mps subst th.ring_req in
  let thm1' = subst_mps subst th.ring_lemma1 in
  let thm2' = subst_mps subst th.ring_lemma2 in
  let tac'= subst_tactic subst th.ring_cst_tac in
  if c' == th.ring_carrier &&
     eq' == th.ring_req &&
     thm1' == th.ring_lemma1 &&
     thm2' == th.ring_lemma2 &&
     tac' == th.ring_cst_tac then th
  else
    { ring_carrier = c';
      ring_req = eq';
      ring_cst_tac = tac';
      ring_lemma1 = thm1';
      ring_lemma2 = thm2' }


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


let ring_for_carrier r = Cmap.find r !from_carrier

let ring_for_relation rel = Cmap.find rel !from_relation

let setoid_of_relation r =
  lapp coq_mk_Setoid
    [|r.rel_a; r.rel_aeq;
      out_some r.rel_refl; out_some r.rel_sym; out_some r.rel_trans |]

let op_morph r add mul opp req m1 m2 m3 =
  lapp coq_mk_reqe [| r; add; mul; opp; req; m1; m2; m3 |]

let op_smorph r add mul req m1 m2 =
  lapp coq_SReqe_Reqe
    [| r;add;mul;req;lapp coq_mk_seqe [| r; add; mul; req; m1; m2 |]|]

let sr_sub r add = lapp coq_SRsub [|r;add|]
let sr_opp r = lapp coq_SRopp [|r|]

let dest_morphism kind th sth =
  let th_typ = Retyping.get_type_of (Global.env()) Evd.empty th in
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
    | _ -> failwith "bad ring_morph lemma"

let dest_eq_test th =
  let th_typ = Retyping.get_type_of (Global.env()) Evd.empty th in
  match decompose_prod th_typ with
      (_,h)::_,_ ->
        (match snd(destApplication h) with
            [|_;lhs;_|] -> fst(destApplication lhs)
          | _ -> failwith "bad lemma for decidability of equality")
    | _ -> failwith "bad lemma for decidability of equality"

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
            (let opp_m = default_morphism ~filter:is_endomorphism opp in
             let op_morph =
               op_morph r add mul opp req add_m.lem mul_m.lem opp_m.lem in
             msgnl
               (str"Using setoid \""++pr_term rel.rel_aeq++str"\""++spc()++  
               str"and morphisms \""++pr_term add_m.morphism_theory++
               str"\","++spc()++ str"\""++pr_term mul_m.morphism_theory++
               str"\""++spc()++str"and \""++pr_term opp_m.morphism_theory++
               str"\"");
             op_morph)
          else
            (msgnl
              (str"Using setoid \""++pr_term rel.rel_aeq++str"\"" ++ spc() ++  
               str"and morphisms \""++pr_term add_m.morphism_theory++
               str"\""++spc()++str"and \""++
               pr_term mul_m.morphism_theory++str"\"");
            op_smorph r add mul req add_m.lem mul_m.lem) in
        (setoid,op_morph)

let build_setoid_params is_semi r add mul opp req eqth =
  match eqth with
      Some th -> th
    | None -> default_ring_equality is_semi (r,add,mul,opp,req)

let dest_ring th_spec =
  let th_typ = Retyping.get_type_of (Global.env()) Evd.empty th_spec in
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
  | Closed of constr list


let add_theory name rth eqth morphth cst_tac =
  let (kind,r,zero,one,add,mul,sub,opp,req) = dest_ring rth in
  let (sth,morph) = build_setoid_params kind r add mul opp req eqth in
  let args0 = [|r;zero;one;add;mul;sub;opp;req;sth;morph|] in
  let (lemma1,lemma2) =
    match morphth with
      | Computational c ->
          let reqb = dest_eq_test c in
          let rth = 
            build_almost_ring
              kind r zero one add mul sub opp req sth  morph rth in
          let args = Array.append args0 [|rth;reqb;c|] in
          (lapp ring_comp1 args, lapp ring_comp2 args)
      | Morphism m ->
          let (m,args1) = dest_morphism kind m sth in
          let rth = 
            build_almost_ring
              kind r zero one add mul sub opp req sth morph rth in
          let args = Array.concat [args0;[|rth|]; args1; [|m|]] in
          (lapp coq_ring_lemma1 args, lapp coq_ring_lemma2 args)
      | Abstract ->
          let args1 = Array.append args0 [|rth|] in
          (match kind with
              None -> error "an almost_ring cannot be abstract"
            | Some true ->
                (lapp sring_abs1 args1, lapp sring_abs2 args1)
            | Some false ->
                (lapp ring_abs1 args1, lapp ring_abs2 args1)) in
  let cst_tac = match cst_tac with
      Some (CstTac t) -> Tacinterp.glob_tactic t
    | Some (Closed lc) -> failwith "TODO"
    | None ->
        (match kind with
            Some true ->
              let t = Genarg.ArgArg(dummy_loc,Lazy.force ltac_inv_morphN) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul]))
          | Some false ->
              let t = Genarg.ArgArg(dummy_loc, Lazy.force ltac_inv_morphZ) in
              TacArg(TacCall(dummy_loc,t,List.map carg [zero;one;add;mul;opp]))
          | _ -> error"a tactic must be specified for an almost_ring") in
  let _ =
    Lib.add_leaf name
      (theory_to_obj
        { ring_carrier = r;
          ring_req = req;
          ring_cst_tac = cst_tac;
          ring_lemma1 = lemma1;
          ring_lemma2 = lemma2 }) in
  ()

VERNAC ARGUMENT EXTEND ring_coefs
| [ "Computational" constr(c)] -> [ Computational (ic c) ]
| [ "Abstract" ] -> [ Abstract ]
| [ "Coefficients" constr(m)] -> [ Morphism (ic m) ]
| [ ] -> [ Abstract ]
END

VERNAC ARGUMENT EXTEND ring_cst_tac
| [ "Constant" tactic(c)] -> [ Some(CstTac c) ]
| [ "[" ne_constr_list(l) "]" ] -> [ Some(Closed (List.map ic l)) ]
| [ ] -> [ None ]
END

VERNAC COMMAND EXTEND AddSetoidRing
| [ "Add" "New" "Ring" ident(id) ":" constr(t) ring_coefs(c)
      "Setoid" constr(e) constr(m) ring_cst_tac(tac) ] ->
    [ add_theory id (ic t) (Some (ic e, ic m)) c tac ]
| [ "Add" "New" "Ring" ident(id) ":" constr(t) ring_coefs(c) 
      ring_cst_tac(tac) ] ->
    [ add_theory id (ic t) None c tac ]
END


(*****************************************************************************)
(* The tactics consist then only in a lookup in the ring database and
   call the appropriate ltac. *)

let ring gl = 
  let req = dest_rel (pf_concl gl) in
  let e =
    try ring_for_relation req
    with Not_found ->
      errorlabstrm "ring"
        (str"cannot find a declared ring structure for equality"++
         spc()++str"\""++pr_term req++str"\"") in
  let req = carg e.ring_req in
  let lemma1 = carg e.ring_lemma1 in
  let lemma2 = carg e.ring_lemma2 in
  let cst_tac = Tacexp e.ring_cst_tac in
  Tacinterp.eval_tactic
    (TacArg(TacCall(dummy_loc,
      Genarg.ArgArg(dummy_loc, Lazy.force ltac_setoid_ring),
      Tacexp e.ring_cst_tac::
      List.map carg [e.ring_lemma1;e.ring_lemma2;e.ring_req])))
    gl

let ring_rewrite rl =
  let ty = Retyping.get_type_of (Global.env()) Evd.empty (List.hd rl) in
  let e =
    try ring_for_carrier ty
    with Not_found ->
      errorlabstrm "ring"
        (str"cannot find a declared ring structure over"++
         spc()++str"\""++pr_term ty++str"\"") in
  let rl = List.fold_right (fun x l -> lapp coq_cons [|ty;x;l|]) rl
    (lapp coq_nil [|ty|]) in
  Tacinterp.eval_tactic
    (TacArg(TacCall(dummy_loc,
      Genarg.ArgArg(dummy_loc, Lazy.force ltac_setoid_ring_rewrite),
      Tacexp e.ring_cst_tac::List.map carg [e.ring_lemma2;e.ring_req;rl])))

let setoid_ring = function
  | [] -> ring
  | l -> ring_rewrite l

TACTIC EXTEND setoid_ring
  [ "setoid" "ring" constr_list(l) ] -> [ setoid_ring l ]
END

