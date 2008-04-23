(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

open Pp
open Util
open Names
open Term
open Mod_subst
open Environ
open Libnames
open Nameops
open Libobject
open Lib

(** Characterization of the head of a term *)

(* We only compute an approximation to ensure the computation is not
   arbitrary long (e.g. the head constant of [h] defined to be 
   [g (fun x -> phi(x))] where [g] is [fun f => g O] does not launch 
   the evaluation of [phi(0)] and the head of [h] is declared unknown). *)

type rigid_head_kind =
| RigidParameter of constant (* a Const without body *)
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
  let compare = Pervasives.compare
end

module Evalrefmap = Map.Make(Evalreford)

let head_map = ref Evalrefmap.empty

let init () = head_map := Evalrefmap.empty

let freeze () = !head_map

let unfreeze hm = head_map := hm

let _ = 
  Summary.declare_summary "Head_decl"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = true;
      Summary.survive_section = false }

let variable_head id  = Evalrefmap.find (EvalVarRef id) !head_map
let constant_head cst = Evalrefmap.find (EvalConstRef cst) !head_map

let kind_of_head env t =
  let rec aux k l t b = match kind_of_term (Reduction.whd_betaiotazeta t) with
  | Rel n when n > k -> NotImmediatelyComputableHead
  | Rel n -> FlexibleHead (k,k+1-n,List.length l,b)
  | Var id -> 
      (try on_subterm k l b (variable_head id)
       with Not_found ->
        (* a goal variable *)
        match pi2 (lookup_named id env) with
        | Some c -> aux k l c b
        | None -> NotImmediatelyComputableHead)
  | Const cst -> on_subterm k l b (constant_head cst)
  | Construct _ | CoFix _ -> 
      if b then NotImmediatelyComputableHead else ConstructorHead
  | Sort _ | Ind _ | Prod _ -> RigidHead RigidType
  | Cast (c,_,_) -> aux k l c b
  | Lambda (_,_,c) when l = [] -> assert (not b); aux (k+1) [] c b
  | Lambda (_,_,c) -> aux (k+1) (List.tl l) (subst1 (List.hd l) c) b
  | LetIn _ -> assert false
  | Meta _ | Evar _ -> NotImmediatelyComputableHead
  | App (c,al) -> aux k (Array.to_list al @ l) c b
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
          k,list_skipn n l,List.nth l (i-1) in
      let l' = list_tabulate (fun _ -> mkMeta 0) q @ rest in
      aux k' l' a (with_subcase or with_case)
  | ConstructorHead when with_case -> NotImmediatelyComputableHead
  | x -> x
  in aux 0 [] t false

let compute_head = function
| EvalConstRef cst ->
    (match constant_opt_value (Global.env()) cst with
     | None -> RigidHead (RigidParameter cst)
     | Some c -> kind_of_head (Global.env()) c)
| EvalVarRef id ->
    (match pi2 (Global.lookup_named id) with
     | Some c when not (Decls.variable_opacity id) -> 
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
      let cst,c = subst_con subst cst in
      if c = mkConst cst then
        (* A change of the prefix of the constant *)
        k
      else
        (* A substitution of the constant by a functor argument *)
        kind_of_head (Global.env()) c
  | x -> x

let subst_head (_,subst,(ref,k)) =
  (subst_evaluable_reference subst ref, subst_head_approximation subst k)

let discharge_head (_,(ref,k)) =
  match ref with
  | EvalConstRef cst -> Some (EvalConstRef (pop_con cst), k)
  | EvalVarRef id -> None

let rebuild_head (info,(ref,k)) =
  (ref, compute_head ref)

let export_head o = Some o

let (inHead, _) =
  declare_object {(default_object "HEAD") with 
    cache_function = cache_head;
    load_function = load_head;
    subst_function = subst_head;
    classify_function = (fun (_,x) -> Substitute x);
    discharge_function = discharge_head;
    rebuild_function = rebuild_head;
    export_function = export_head }

let declare_head c =
  let hd = compute_head c in
  add_anonymous_leaf (inHead (c,hd))

(** Printing *)

let pr_head = function
| RigidHead (RigidParameter cst) -> str "rigid constant " ++ pr_con cst
| RigidHead (RigidType) -> str "rigid type"
| RigidHead (RigidVar id) -> str "rigid variable " ++ pr_id id
| ConstructorHead -> str "constructor"
| FlexibleHead (k,n,p,b) -> int n ++ str "th of " ++ int k ++ str " binders applied to " ++ int p ++ str " arguments" ++ (if b then str " (with case)" else mt())
| NotImmediatelyComputableHead -> str "unknown"


