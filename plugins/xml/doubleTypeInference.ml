(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

(*CSC: tutto da rifare!!! Basarsi su Retyping che e' meno costoso! *)
type types = {synthesized : Term.types ; expected : Term.types option};;

let prerr_endline _ = ();;

let cprop =
 let module N = Names in
  N.make_con
   (N.MPfile
     (Libnames.dirpath_of_string "CoRN.algebra.CLogic"))
   (N.make_dirpath [])
   (N.mk_label "CProp")
;;

let whd_betadeltaiotacprop env _evar_map ty =
 let module R = Rawterm in
 let module C = Closure in
 let module CR = C.RedFlags in
 (*** CProp is made Opaque ***)
 let flags = CR.red_sub C.betadeltaiota (CR.fCONST cprop) in
 C.whd_val (C.create_clos_infos flags env) (C.inject ty)
;;


(* Code similar to the code in the Typing module, but:   *)
(*  - the term is already assumed to be well typed       *)
(*  - some checks have been removed                      *)
(*  - both the synthesized and expected types of every   *)
(*    node are computed (Coscoy's double type inference) *)

let assumption_of_judgment env sigma j =
  Typeops.assumption_of_judgment env (Evarutil.j_nf_evar sigma j)
;;

let type_judgment env sigma j =
  Typeops.type_judgment env (Evarutil.j_nf_evar sigma j)
;;

let type_judgment_cprop env sigma j =
  match Term.kind_of_term(whd_betadeltaiotacprop env sigma j.Environ.uj_type) with
    | Term.Sort s -> Some {Environ.utj_val = j.Environ.uj_val; Environ.utj_type = s }
    | _ -> None  (* None means the CProp constant *)
;;

let double_type_of env sigma cstr expectedty subterms_to_types =
 (*CSC: the code is inefficient because judgments are created just to be   *)
 (*CSC: destroyed using Environ.j_type. Moreover I am pretty sure that the *)
 (*CSC: functions used do checks that we do not need                       *)
 let rec execute env sigma cstr expectedty =
  let module T = Term in
  let module E = Environ in
   (* the type part is the synthesized type *)
   let judgement =
    match T.kind_of_term cstr with
       T.Meta n ->
        Util.error
         "DoubleTypeInference.double_type_of: found a non-instanciated goal"

     | T.Evar ((n,l) as ev) ->
        let ty = Unshare.unshare (Evd.existential_type sigma ev) in
        let jty = execute env sigma ty None in
        let jty = assumption_of_judgment env sigma jty in
        let evar_context =
	  E.named_context_of_val (Evd.find sigma n).Evd.evar_hyps in
         let rec iter actual_args evar_context =
          match actual_args,evar_context with
             [],[] -> ()
           | he1::tl1,(n,_,ty)::tl2 ->
              (* for side-effects *)
              let _ = execute env sigma he1 (Some ty) in
              let tl2' =
               List.map
                (function (m,bo,ty) ->
                  (* Warning: the substitution should be performed also on bo *)
                  (* This is not done since bo is not used later yet          *)
                  (m,bo,Unshare.unshare (T.replace_vars [n,he1] ty))
                ) tl2
              in
               iter tl1 tl2'
           | _,_ -> assert false
         in
          (* for side effects only *)
          iter (List.rev (Array.to_list l)) (List.rev evar_context) ;
          E.make_judge cstr jty

     | T.Rel n ->
        Typeops.judge_of_relative env n

     | T.Var id ->
        Typeops.judge_of_variable env id

     | T.Const c ->
        E.make_judge cstr (Typeops.type_of_constant env c)

     | T.Ind ind ->
        E.make_judge cstr (Inductiveops.type_of_inductive env ind)

     | T.Construct cstruct ->
        E.make_judge cstr (Inductiveops.type_of_constructor env cstruct)

     | T.Case (ci,p,c,lf) ->
        let expectedtype =
         Reduction.whd_betadeltaiota env (Retyping.get_type_of env sigma c) in
        let cj = execute env sigma c (Some expectedtype) in
        let pj = execute env sigma p None in
        let (expectedtypes,_,_) =
         let indspec = Inductive.find_rectype env cj.Environ.uj_type in
          Inductive.type_case_branches env indspec pj cj.Environ.uj_val
        in
        let lfj =
         execute_array env sigma lf
          (Array.map (function x -> Some x) expectedtypes) in
        let (j,_) = Typeops.judge_of_case env ci pj cj lfj in
         j

     | T.Fix ((vn,i as vni),recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env sigma recdef in
        let fix = (vni,recdef') in
        E.make_judge (T.mkFix fix) tys.(i)

     | T.CoFix (i,recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env sigma recdef in
        let cofix = (i,recdef') in
        E.make_judge (T.mkCoFix cofix) tys.(i)

     | T.Sort (T.Prop c) ->
        Typeops.judge_of_prop_contents c

     | T.Sort (T.Type u) ->
(*CSC: In case of need, I refresh the universe. But exportation of the   *)
(*CSC: right universe level information is destroyed. It must be changed *)
(*CSC: again once Judicael will introduce his non-bugged algebraic       *)
(*CSC: universes.                                                        *)
(try
        Typeops.judge_of_type u
 with _ -> (* Successor of a non universe-variable universe anomaly *)
 (Pp.ppnl (Pp.str "Warning: universe refresh performed!!!") ; flush stdout ) ;
  Typeops.judge_of_type (Termops.new_univ ())
)

     | T.App (f,args) ->
        let expected_head =
         Reduction.whd_betadeltaiota env (Retyping.get_type_of env sigma f) in
        let j = execute env sigma f (Some expected_head) in
        let expected_args =
         let rec aux typ =
          function
             [] -> []
           | hj::restjl ->
              match T.kind_of_term (Reduction.whd_betadeltaiota env typ) with
                 T.Prod (_,c1,c2) ->
                  (Some (Reductionops.nf_beta sigma c1)) ::
                   (aux (T.subst1 hj c2) restjl)
               | _ -> assert false
         in
          Array.of_list (aux j.Environ.uj_type (Array.to_list args))
        in
        let jl = execute_array env sigma args expected_args in
        let (j,_) = Typeops.judge_of_apply env j jl in
         j

     | T.Lambda (name,c1,c2) ->
        let j = execute env sigma c1 None in
        let var = type_judgment env sigma j in
        let env1 = E.push_rel (name,None,var.E.utj_val) env in
        let expectedc2type =
         match expectedty with
            None -> None
          | Some ety ->
              match T.kind_of_term (Reduction.whd_betadeltaiota env ety) with
                 T.Prod (_,_,expected_target_type) ->
                  Some (Reductionops.nf_beta sigma expected_target_type)
               | _ -> assert false
        in
        let j' = execute env1 sigma c2 expectedc2type in
         Typeops.judge_of_abstraction env1 name var j'

     | T.Prod (name,c1,c2) ->
        let j = execute env sigma c1 None in
        let varj = type_judgment env sigma j in
        let env1 = E.push_rel (name,None,varj.E.utj_val) env in
        let j' = execute env1 sigma c2 None in
        (match type_judgment_cprop env1 sigma j' with
            Some varj' -> Typeops.judge_of_product env name varj varj'
          | None ->
             (* CProp found *)
             { Environ.uj_val = T.mkProd (name, j.Environ.uj_val, j'.Environ.uj_val);
               Environ.uj_type = T.mkConst cprop })

     | T.LetIn (name,c1,c2,c3) ->
(*CSC: What are the right expected types for the source and *)
(*CSC: target of a LetIn? None used.                        *)
        let j1 = execute env sigma c1 None in
        let j2 = execute env sigma c2 None in
        let j2 = type_judgment env sigma j2 in
        let env1 =
         E.push_rel (name,Some j1.E.uj_val,j2.E.utj_val) env
        in
         let j3 = execute env1 sigma c3 None in
          Typeops.judge_of_letin env name j1 j2 j3

     | T.Cast (c,k,t) ->
        let cj = execute env sigma c (Some (Reductionops.nf_beta sigma t)) in
        let tj = execute env sigma t None in
	let tj = type_judgment env sigma tj in
        let j, _ = Typeops.judge_of_cast env cj k tj in
	 j
    in
     let synthesized = E.j_type judgement in
     let synthesized' = Reductionops.nf_beta sigma synthesized in
      let types,res =
       match expectedty with
          None ->
           (* No expected type *)
           {synthesized = synthesized' ; expected = None}, synthesized
        | Some ty when Term.eq_constr synthesized' ty ->
           (* The expected type is synthactically equal to the    *)
           (* synthesized type. Let's forget it.                  *)
           (* Note: since eq_constr is up to casts, it is better  *)
           (* to keep the expected type, since it can bears casts *)
           (* that change the innersort to CProp                  *)
           {synthesized = ty ; expected = None}, ty
        | Some expectedty' ->
           {synthesized = synthesized' ; expected = Some expectedty'},
           expectedty'
      in
(*CSC: debugging stuff to be removed *)
if Acic.CicHash.mem subterms_to_types cstr then
 (Pp.ppnl (Pp.(++) (Pp.str "DUPLICATE INSERTION: ") (Printer.pr_lconstr cstr)) ; flush stdout ) ;
       Acic.CicHash.add subterms_to_types cstr types ;
       E.make_judge cstr res


 and execute_recdef env sigma (names,lar,vdef) =
   let length = Array.length lar in
   let larj =
    execute_array env sigma lar (Array.make length None) in
   let lara = Array.map (assumption_of_judgment env sigma) larj in
   let env1 = Environ.push_rec_types (names,lara,vdef) env in
   let expectedtypes =
    Array.map (function i -> Some (Term.lift length i)) lar
   in
   let vdefj = execute_array env1 sigma vdef expectedtypes in
   let vdefv = Array.map Environ.j_val vdefj in
   (names,lara,vdefv)

 and execute_array env sigma v expectedtypes =
   let jl =
    execute_list env sigma (Array.to_list v) (Array.to_list expectedtypes)
   in
    Array.of_list jl

 and execute_list env sigma =
  List.map2 (execute env sigma)

in
 ignore (execute env sigma cstr expectedty)
;;
