(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Vars
open Environ
open Context.Named.Declaration

(** Characterization of the head of a term *)

(* We only compute an approximation to ensure the computation is not
   arbitrary long (e.g. the head constant of [h] defined to be
   [g (fun x -> phi(x))] where [g] is [fun f => g O] does not launch
   the evaluation of [phi(0)] and the head of [h] is declared unknown). *)

type rigid_head_kind =
| RigidParameter of Constant.t (* a Const without body. Module substitution may instantiate it with something else. *)
| RigidOther (* a Var without body, inductive, product, sort, projection *)

type head_approximation =
| RigidHead of rigid_head_kind
| ConstructorHead
| FlexibleHead of int * int * int * bool (* [true] if a surrounding case *)
| NotImmediatelyComputableHead

(* FIXME: maybe change interface here *)
let rec compute_head env = function
  | EvalConstRef cst ->
    let body = Environ.constant_opt_value_in env (cst,Univ.Instance.empty) in
    (match body with
     | None -> RigidHead (RigidParameter cst)
     | Some c -> kind_of_head env c)
  | EvalVarRef id ->
    (match lookup_named id env with
     | LocalDef (_,c,_) when not (Decls.variable_opacity id) ->
       kind_of_head env c
     | _ -> RigidHead RigidOther)

and kind_of_head env t =
  let rec aux k l t b = match kind (Reduction.whd_betaiotazeta env t) with
  | Rel n when n > k -> NotImmediatelyComputableHead
  | Rel n -> FlexibleHead (k,k+1-n,List.length l,b)
  | Var id ->
      (try on_subterm k l b (compute_head env (EvalVarRef id))
       with Not_found ->
        (* a goal variable *)
        match lookup_named id env with
        | LocalDef (_,c,_) -> aux k l c b
        | LocalAssum _ -> NotImmediatelyComputableHead)
  | Const (cst,_) ->
      (try on_subterm k l b (compute_head env (EvalConstRef cst))
       with Not_found ->
         CErrors.anomaly
           Pp.(str "constant not found in kind_of_head: " ++
               Names.Constant.print cst ++
               str "."))
  | Construct _ | CoFix _ ->
      if b then NotImmediatelyComputableHead else ConstructorHead
  | Sort _ | Ind _ | Prod _ -> RigidHead RigidOther
  | Cast (c,_,_) -> aux k l c b
  | Lambda (_,_,c) ->
    begin match l with
    | [] ->
      let () = assert (not b) in
      aux (k + 1) [] c b
    | h :: l -> aux k l (subst1 h c) b
    end
  | LetIn _ -> assert false
  | Meta _ | Evar _ -> NotImmediatelyComputableHead
  | App (c,al) -> aux k (Array.to_list al @ l) c b
  | Proj (p,c) -> RigidHead RigidOther

  | Case (_,_,c,_) -> aux k [] c true
  | Int _ -> ConstructorHead
  | Fix ((i,j),_) ->
      let n = i.(j) in
      try aux k [] (List.nth l n) true
      with Failure _ -> FlexibleHead (k + n + 1, k + n + 1, 0, true)
  and on_subterm k l with_case = function
  | FlexibleHead (n,i,q,with_subcase) ->
      let m = List.length l in
      let k',rest,a =
        if n > m then
          (* eta-expansion *)
          let a =
            if i <= m then
              (* we pick the head in the existing arguments *)
              lift (n-m) (List.nth l (i-1))
            else
              (* we pick the head in the added arguments *)
              mkRel (n-i+1) in
          k+n-m,[],a
        else
          (* enough arguments to [cst] *)
          k,List.skipn n l,List.nth l (i-1) in
      let l' = List.make q (mkMeta 0) @ rest in
      aux k' l' a (with_subcase || with_case)
  | ConstructorHead when with_case -> NotImmediatelyComputableHead
  | x -> x
  in aux 0 [] t false

let is_rigid env t =
  match kind_of_head env t with
  | RigidHead _ | ConstructorHead -> true
  | _ -> false
