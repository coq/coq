(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*****************************************************************************)
(*                                                                           *)
(*                             PROJECT MoWGLI                                *)
(*                                                                           *)
(*                    A module to print Coq objects in XML                   *)
(*                                                                           *)
(*               Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                22/06/2002                                 *)
(*                                                                           *)
(*****************************************************************************)

(*CSC: tutto da rifare!!! Basarsi su Retyping che e' meno costoso! *)
type types = {synthesized : Term.types ; expected : Term.types option};;

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
        let ty = T.unshare (Instantiate.existential_type sigma ev) in
        let jty = execute env sigma ty None in
        let jty = assumption_of_judgment env sigma jty in
        let evar_context = (Evd.map sigma n).Evd.evar_hyps in
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
                  (m,bo,T.unshare (T.replace_vars [n,he1] ty))
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
        E.make_judge cstr (E.constant_type env c)
	  
     | T.Ind ind ->
        E.make_judge cstr (Inductive.type_of_inductive env ind)
	  
     | T.Construct cstruct -> 
        E.make_judge cstr (Inductive.type_of_constructor env cstruct)
	  
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
                  (Some (Reductionops.nf_beta c1)) ::
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
                  Some (Reductionops.nf_beta expected_target_type)
               | _ -> assert false
        in
        let j' = execute env1 sigma c2 expectedc2type in 
         Typeops.judge_of_abstraction env1 name var j'
	  
     | T.Prod (name,c1,c2) ->
        let j = execute env sigma c1 None in
        let varj = type_judgment env sigma j in
        let env1 = E.push_rel (name,None,varj.E.utj_val) env in
        let j' = execute env1 sigma c2 None in
        let varj' = type_judgment env1 sigma j' in
         Typeops.judge_of_product env name varj varj'

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
  
     | T.Cast (c,t) ->
        let cj = execute env sigma c (Some (Reductionops.nf_beta t)) in
        let tj = execute env sigma t None in
	let tj = type_judgment env sigma tj in
        let j, _ = Typeops.judge_of_cast env cj tj in
	 j
    in
     let synthesized = E.j_type judgement in
     let synthesized' = Reductionops.nf_beta synthesized in
      let types,res =
       match expectedty with
          None ->
           (* No expected type *)
           {synthesized = synthesized' ; expected = None}, synthesized
        (*CSC: in HELM we did not considered Casts to be irrelevant. *)
        (*CSC: does it really matter? (eq_constr is up to casts)     *)
        | Some ty when Term.eq_constr synthesized' ty ->
           (* The expected type is synthactically equal to *)
           (* the synthesized type. Let's forget it.       *)
           {synthesized = synthesized' ; expected = None}, synthesized
        | Some expectedty' ->
           {synthesized = synthesized' ; expected = Some expectedty'},
           expectedty'
      in
(*CSC: debugging stuff to be removed *)
if Acic.CicHash.mem subterms_to_types cstr then
 (Pp.ppnl (Pp.(++) (Pp.str "DUPLICATE INSERTION: ") (Printer.prterm cstr)) ; flush stdout ) ;
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
