(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

(* Note: we can not use the Set module here because we _need_ physical *)
(* equality and there exists no comparison function compatible with    *)
(* physical equality.                                                  *)

module S =
 struct
  let empty = []
  let mem = List.memq
  let add x l = x::l
 end
;;

(* evar reduction that preserves some terms *)
let nf_evar sigma ~preserve =
 let module T = Term in
  let rec aux t =
   if preserve t then t else
    match T.kind_of_term t with
     | T.Rel _ | T.Meta _ | T.Var _ | T.Sort _ | T.Const _ | T.Ind _
     | T.Construct _ -> t
     | T.Cast (c1,k,c2) -> T.mkCast (aux c1, k, aux c2)
     | T.Prod (na,c1,c2) -> T.mkProd (na, aux c1, aux c2)
     | T.Lambda (na,t,c) -> T.mkLambda (na, aux t, aux c)
     | T.LetIn (na,b,t,c) -> T.mkLetIn (na, aux b, aux t, aux c)
     | T.App (c,l) ->
        let c' = aux c in
        let l' = Array.map aux l in
         (match T.kind_of_term c' with
             T.App (c'',l'') -> T.mkApp (c'', Array.append l'' l')
           | T.Cast (he,_,_) ->
              (match T.kind_of_term he with
                  T.App (c'',l'') -> T.mkApp (c'', Array.append l'' l')
                | _ -> T.mkApp (c', l')
              )
           | _ -> T.mkApp (c', l'))
     | T.Evar (e,l) when Evd.mem sigma e & Evd.is_defined sigma e ->
	aux (Evd.existential_value sigma (e,l))
     | T.Evar (e,l) -> T.mkEvar (e, Array.map aux l)
     | T.Case (ci,p,c,bl) -> T.mkCase (ci, aux p, aux c, Array.map aux bl)
     | T.Fix (ln,(lna,tl,bl)) ->
         T.mkFix (ln,(lna,Array.map aux tl,Array.map aux bl))
     | T.CoFix(ln,(lna,tl,bl)) ->
         T.mkCoFix (ln,(lna,Array.map aux tl,Array.map aux bl))
     | T.NativeInt _ | T.NativeArr _ ->
	 Util.anomaly "proof2aproof.nf_evar: native not yet implemented"
   in
    aux
;;

(* Unshares a proof-tree.                                                  *)
(* Warning: statuses, goals, prim_rules and tactic_exprs are not unshared! *)
let rec unshare_proof_tree =
 let module PT = Proof_type in
  function {PT.open_subgoals = status ;
	    PT.goal = goal ;
	    PT.ref = ref} ->
   let unshared_ref =
    match ref with
       None -> None
     | Some (rule,pfs) ->
        let unshared_rule =
         match rule with
             PT.Nested (cmpd, pf) ->
               PT.Nested (cmpd, unshare_proof_tree pf)
	   | other -> other
	in
         Some (unshared_rule, List.map unshare_proof_tree pfs)
   in
    {PT.open_subgoals = status ;
     PT.goal = goal ;
     PT.ref = unshared_ref}
;;

module ProofTreeHash =
 Hashtbl.Make
  (struct
    type t = Proof_type.proof_tree
    let equal = (==)
    let hash = Hashtbl.hash
   end)
;;


let extract_open_proof sigma pf =
  (* Deactivated and candidate for removal. (Apr. 2010) *)
   ()

let extract_open_pftreestate pts =
  (* Deactivated and candidate for removal. (Apr. 2010) *)
   ()
