(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
open Mod_subst
open Environ
open Globnames
open Libobject
open Lib
open Context.Named.Declaration

(** Characterization of the head of a term *)

(* We only compute an approximation to ensure the computation is not
   arbitrary long (e.g. the head constant of [h] defined to be
   [g (fun x -> phi(x))] where [g] is [fun f => g O] does not launch
   the evaluation of [phi(0)] and the head of [h] is declared unknown). *)

type rigid_head_kind =
| RigidParameter of Constant.t (* a Const without body *)
| RigidVar of variable (* a Var without body *)
| RigidType (* an inductive, a product or a sort *)

type head_approximation =
| RigidHead of rigid_head_kind
| ConstructorHead
| FlexibleHead of int * int * int * bool (* [true] if a surrounding case *)
| NotImmediatelyComputableHead

(** Registration as global tables and rollback. *)

module Evalreford = struct
  type t = evaluable_global_reference
  let compare gr1 gr2 = match gr1, gr2 with
  | EvalVarRef id1, EvalVarRef id2 -> Id.compare id1 id2
  | EvalVarRef _, EvalConstRef _ -> -1
  | EvalConstRef c1, EvalConstRef c2 ->
    Constant.CanOrd.compare c1 c2
  | EvalConstRef _, EvalVarRef _ -> 1
end

module Evalrefmap =
  Map.Make (Evalreford)


let head_map = Summary.ref Evalrefmap.empty ~name:"Head_decl"

let variable_head id  = Evalrefmap.find (EvalVarRef id) !head_map
let constant_head cst = Evalrefmap.find (EvalConstRef cst) !head_map

let kind_of_head env t =
  let rec aux k l t b = match kind (Reduction.whd_betaiotazeta env t) with
  | Rel n when n > k -> NotImmediatelyComputableHead
  | Rel n -> FlexibleHead (k,k+1-n,List.length l,b)
  | Var id ->
      (try on_subterm k l b (variable_head id)
       with Not_found ->
        (* a goal variable *)
        match lookup_named id env with
        | LocalDef (_,c,_) -> aux k l c b
        | LocalAssum _ -> NotImmediatelyComputableHead)
  | Const (cst,_) ->
      (try on_subterm k l b (constant_head cst)
       with Not_found ->
         CErrors.anomaly
           Pp.(str "constant not found in kind_of_head: " ++
               Names.Constant.print cst ++
               str "."))
  | Construct _ | CoFix _ ->
      if b then NotImmediatelyComputableHead else ConstructorHead
  | Sort _ | Ind _ | Prod _ -> RigidHead RigidType
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
  | Proj (p,c) ->
      (try on_subterm k (c :: l) b (constant_head (Projection.constant p))
       with Not_found -> assert false)

  | Case (_,_,c,_) -> aux k [] c true
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

(* FIXME: maybe change interface here *)
let compute_head = function
| EvalConstRef cst ->
   let env = Global.env() in
   let cb = Environ.lookup_constant cst env in
   let is_Def = function Declarations.Def _ -> true | _ -> false in
   let body =
     if not (Recordops.is_primitive_projection cst) && is_Def cb.Declarations.const_body
     then Global.body_of_constant cst else None
   in
     (match body with
     | None -> RigidHead (RigidParameter cst)
     | Some (c, _) -> kind_of_head env c)
| EvalVarRef id ->
    (match Global.lookup_named id with
     | LocalDef (_,c,_) when not (Decls.variable_opacity id) ->
           kind_of_head (Global.env()) c
     | _ ->
           RigidHead (RigidVar id))

let is_rigid env t =
  match kind_of_head env t with
  | RigidHead _ | ConstructorHead -> true
  | _ -> false

(** Registration of heads as an object *)

let load_head _ (_,(ref,(k:head_approximation))) =
  head_map := Evalrefmap.add ref k !head_map

let cache_head o =
  load_head 1 o

let subst_head_approximation subst = function
  | RigidHead (RigidParameter cst) as k ->
      let cst,c = subst_con_kn subst cst in
      if isConst c && Constant.equal (fst (destConst c)) cst then
        (* A change of the prefix of the constant *)
        k
      else
        (* A substitution of the constant by a functor argument *)
        kind_of_head (Global.env()) c
  | x -> x

let subst_head (subst,(ref,k)) =
  (subst_evaluable_reference subst ref, subst_head_approximation subst k)

let discharge_head (_,(ref,k)) =
  match ref with
  | EvalConstRef cst -> Some (EvalConstRef (pop_con cst), k)
  | EvalVarRef id -> None

let rebuild_head (ref,k) =
  (ref, compute_head ref)

type head_obj = evaluable_global_reference * head_approximation

let inHead : head_obj -> obj =
  declare_object {(default_object "HEAD") with
    cache_function = cache_head;
    load_function = load_head;
    subst_function = subst_head;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_head;
    rebuild_function = rebuild_head }

let declare_head c =
  let hd = compute_head c in
  add_anonymous_leaf (inHead (c,hd))
