(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Context
open Univ
open Environ
open EConstr
open Vars
open Context.Rel.Declaration

(** This module implements a call by name reduction used by the cbn tactic.

    It has an ability to "refold" constants by storing constants and
    their parameters in its stack.
*)

(** Machinery to custom the behavior of the reduction *)
module ReductionBehaviour = Reductionops.ReductionBehaviour

type cst_info = { volatile : bool; refold_after_iota : bool }

module CbnClos = struct
  open EConstr

  (* [force] is deliberately cached for non-identity substitutions: several
     refolding/progress checks compare the same delayed closure repeatedly. *)
  type t = { term : constr; subst : subs; mutable forced : constr option }
  and subs = t Esubst.subs

  type view = subs * (EConstr.t, EConstr.t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term

  let id_subst = Esubst.subs_id 0
  let inject term = { term; subst = id_subst; forced = None }
  let lift n c =
    if Int.equal n 0 then c else { term = c.term; subst = Esubst.subs_shft (n, c.subst); forced = None }

  (* important optim: expand rel eagerly
     (might also work to cache kind like we cache force?) *)
  let mk_clos subst term =
    if Esubst.is_subs_id subst then inject term else
      match Constr.kind (EConstr.Unsafe.to_constr term) with
      | Rel n -> begin match Esubst.expand_rel n subst with
          | Inl (k, v) -> lift k v
          | Inr (k, _) -> inject (mkRel k)
        end
      | _ ->
      { term; subst; forced = None }

  let mk_clos_vect subst v = Array.map (mk_clos subst) v
  let is_id_subst c = Esubst.is_subs_id c.subst

  (* Closure-level application used by internal continuations that need to keep
     constructor/constant spines without forcing all arguments. *)
  let mk_app f args =
    match args with
    | [] -> f
    | _ :: _ ->
      let nargs = List.length args in
      let term = mkApp (mkRel 1, Array.init nargs (fun i -> mkRel (i + 2))) in
      let subst = List.fold_right Esubst.subs_cons (f :: args) id_subst in
      mk_clos subst term

  let mk_array u elems def ty =
    let n = Array.length elems in
    let term = mkArray (u, Array.init n (fun i -> mkRel (i + 1)), mkRel (n + 1), mkRel (n + 2)) in
    let subst = List.fold_right Esubst.subs_cons (Array.to_list elems @ [def; ty]) id_subst in
    mk_clos subst term

  let rec force c =
    if Esubst.is_subs_id c.subst then c.term
    else match c.forced with
    | Some t -> t
    | None ->
      let t = force_constr c.subst c.term in
      c.forced <- Some t;
      t

  and force_constr subs c =
    EConstr.Vars.esubst (fun k v -> force (lift k v)) subs c

  let force_vect v = Array.map force v

  let force_under_context subs (nas,c) =
    nas, force_constr (Esubst.subs_liftn (Array.length nas) subs) c

  let force_invert subs = function
    | NoInvert -> NoInvert
    | CaseInvert { indices } -> CaseInvert { indices = Array.Fun1.map force_constr subs indices }

  let force_return subs (p, r) =
    (force_under_context subs p, r)

  let force_branches subs brs = Array.Fun1.map force_under_context subs brs

  let force_case subs (ci, u, pms, ret, iv, brs) =
    let pms = Array.Fun1.map force_constr subs pms in
    let ret = force_return subs ret in
    let iv = force_invert subs iv in
    let brs = force_branches subs brs in
    ci, u, pms, ret, iv, brs

  let mk_clos_fix subs (struc,(nas, ts, bs)) =
    struc, (nas, mk_clos_vect subs ts, mk_clos_vect (Esubst.subs_liftn (Array.length nas) subs) bs)

  let force_fix subs f =
    let ((ri, n), (names, types, bodies)) = mk_clos_fix subs f in
    ((ri, n), (names, force_vect types, force_vect bodies))

  let force_cofix subs (n, (names, types, bodies)) =
    let nb = Array.length bodies in
    (n, (names, force_vect (mk_clos_vect subs types), force_vect (mk_clos_vect (Esubst.subs_liftn nb subs) bodies)))

  let equal sigma a b =
    (a.term == b.term && a.subst == b.subst) ||
    (* TODO: add fast path that returns false on non-Rel terms whose head is not of the same shape.
       Alternatively, fuse the equality check and the substitution
       (but attempt at 9a772ab008 produced bad results, cf https://gitlab.inria.fr/coq/coq/-/jobs/7383036) *)
    let a = force a in
    let b = force b in
    EConstr.eq_constr sigma a b

  let rec kind sigma c : view =
    match EConstr.kind sigma c.term with
    | Rel n ->
      begin match Esubst.expand_rel n c.subst with
      | Inl (k, v) -> kind sigma (lift k v)
      | Inr (k, _) ->
        (* subst is ignored here *)
        Esubst.subs_id 0, Rel k
      end
    | k -> c.subst, k

  type array_view = {
    array_length : int;
    array_get : int -> t;
    array_default : t;
  }

  let array_view sigma c =
    match kind sigma c with
    | subs, Array (_,elems,def,ty) -> Some {
        array_length = Array.length elems;
        array_get = (fun i -> mk_clos subs elems.(i));
        array_default = mk_clos subs def;
      }
    | _ -> None

end
let mk_clos = CbnClos.mk_clos
let mk_clos_vect = CbnClos.mk_clos_vect

(** Machinery about stack of unfolded constants *)
module Cst_stack = struct
  open EConstr

(** constant * params * args

- constant applied to params = term in head applied to args
- there is at most one arguments with an empty list of args, it must be the first.
- in args, the int represents the indice of the first arg to consider *)
  type t = (constr * CbnClos.t list * (int * CbnClos.t array) list * cst_info) list

  let empty : t = []
  let all_volatile (l : t) = CList.for_all (fun (_,_,_,{volatile; _}) -> volatile) l

  let drop_useless (l : t) : t = match l with
    | _ :: ((_,_,[],_)::_ as q) -> q
    | l -> l

  let add_param (h : CbnClos.t) (cst_l : t) : t =
    let append2cst = function
      | (c,params,[],vol) -> (c, h::params, [], vol)
      | (c,params,((i,t)::q),vol) when i = pred (Array.length t) ->
        (c, params, q, vol)
      | (c,params,(i,t)::q, vol) ->
        (c, params, (succ i,t)::q, vol)
    in
      drop_useless (List.map append2cst cst_l)

  let add_args (cl : CbnClos.t array) (l : t) : t =
    List.map (fun (a,b,args,vol) -> (a,b,(0,cl)::args,vol)) l

  let add_cst ?(volatile=false) ?(refold_after_iota=false) (cst : constr) (l : t) : t = match l with
    | (_,_,[],_) :: q as l -> l
    | l -> (cst,[],[],{volatile; refold_after_iota})::l

  let best_cst (l : t) : (constr * CbnClos.t list) option = match l with
    | (cst,params,[],_)::_ -> Some(cst,params)
    | _ -> None

  let reference sigma (t : t) = match best_cst t with
    | Some (c, params) when isConst sigma c -> Some (fst (destConst sigma c), List.map CbnClos.force params)
    | _ -> None

  (** [best_replace d cst_l c] makes the best replacement for [d]
      by [cst_l] in [c] *)
  let best_replace sigma d (cst_l : t) c =
    let reconstruct_head = List.fold_left
      (fun t (i,args) ->
         let args = Array.map CbnClos.force (Array.sub args i (Array.length args - i)) in
         mkApp (t,args)) in
    List.fold_right
      (fun (cst,params,args,_) t -> Termops.replace_term sigma
        (reconstruct_head d args)
        (applist (cst, List.rev_map CbnClos.force params))
        t) cst_l c

  let pr env sigma pr_a (l : t) =
    let open Pp in
    let p_c c = Termops.Internal.print_constr_env env sigma c in
    prlist_with_sep pr_semicolon
      (fun (c,params,args,{volatile; refold_after_iota}) ->
        hov 1 (str"(" ++ p_c c ++ str ")" ++ spc () ++ pr_sequence pr_a params ++ spc () ++ str "(args:" ++
                 pr_sequence (fun (i,el) -> prvect_with_sep spc pr_a (Array.sub el i (Array.length el - i))) args ++
               str ")" ++
              (if volatile then str " (volatile)" else mt()) ++
              (if refold_after_iota then str " (refold-after-iota)" else mt()))) l
end




(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack =
struct
  open EConstr
  type app_node = int * CbnClos.t array * int
  (* first releavnt position, arguments, last relevant position *)
  (* TODO I think the substitution is constant for each array so put
     it outside the array to avoid allocating an array? *)

  (*
     Invariant that this module must ensure:
     - in app_node (i,_,j) i <= j
     - There is no array reallocation (outside of debug printing)
   *)

  let pr_app_node pr (i,a,j) =
    let open Pp in surround (
                     prvect_with_sep pr_comma pr (Array.sub a i (j - i + 1))
                     )


  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t * ERelevance.t

  type case_stk =
    case_info * EInstance.t * EConstr.t array * (EConstr.t,ERelevance.t) pcase_return * EConstr.t pcase_invert * (EConstr.t,ERelevance.t) pcase_branch array
  type member =
  | App of app_node
  | Case of CbnClos.subs * case_stk * Cst_stack.t
  | Proj of Projection.t * ERelevance.t * Cst_stack.t
  | Fix of CbnClos.subs * (EConstr.t, EConstr.t, ERelevance.t) pfixpoint * t * Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * t * CPrimitives.args_red * Cst_stack.t
  | Cst of { const : cst_member;
             curr : int;
             remains : int list;
             params : t;
             volatile : bool;
             refold_after_iota : bool;
             cst_l : Cst_stack.t;
           }

  and t = member list

  (* Debugging printer *)
  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case (subs,(_,_,_,_,_,br),cst) ->
       str "ZCase(" ++
       prvect_with_sep pr_bar (fun (nas, b) ->
           let b = mk_clos (Esubst.subs_liftn (Array.length nas) subs) b in
           pr_c b) br
       ++ str ")"
    | Proj (p,_,cst) ->
      str "ZProj(" ++ Projection.debug_print p ++ str ")"
    | Fix (subs,f,args,cst) ->
      let f = CbnClos.mk_clos_fix subs f in
       str "ZFix(" ++ Constr.debug_print_fix pr_c f
       ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Primitive (p,c,args,kargs,cst_l) ->
      str "ZPrimitive(" ++ str (CPrimitives.to_string p)
      ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Cst {const=mem;curr;remains;params;cst_l;refold_after_iota} ->
      str "ZCst(" ++ pr_cst_member pr_c mem ++ pr_comma () ++ int curr
      ++ pr_comma () ++
        prlist_with_sep pr_semicolon int remains ++
        pr_comma () ++ pr pr_c params ++
        (if refold_after_iota then str ", refold-after-iota" else mt()) ++ str ")"
  and pr pr_c l =
    let open Pp in
    prlist_with_sep pr_semicolon (fun x -> hov 1 (pr_member pr_c x)) l

  and pr_cst_member pr_c c =
    let open Pp in
      match c with
      | Cst_const (c, u) ->
        if UVars.Instance.is_empty u then Constant.debug_print c
        else str"(" ++ Constant.debug_print c ++ str ", " ++
          UVars.Instance.pr Sorts.raw_printer u ++ str")"
      | Cst_proj (p,r) ->
        str".(" ++ Projection.debug_print p ++ str")"

  let empty = []

  let append_app v s =
    let le = Array.length v in
    if Int.equal le 0 then s else App (0,v,pred le) :: s

  let decomp_node (i,l,j) sk =
    if i < j then (l.(i), App (succ i,l,j) :: sk)
    else (l.(i), sk)

  let decomp = function
    | App node::s -> Some (decomp_node node s)
    | _ -> None

  let decomp_node_last (i,l,j) sk =
    if i < j then (l.(j), App (i,l,pred j) :: sk)
    else (l.(j), sk)

  let equal env sigma sk1 sk2 =
    let equal_cst_member x y =
      match x, y with
      | Cst_const (c1,u1), Cst_const (c2, u2) ->
        QConstant.equal env c1 c2 && UVars.Instance.equal u1 u2
      | Cst_proj (p1,_), Cst_proj (p2,_) -> QProjection.Repr.equal env (Projection.repr p1) (Projection.repr p2)
      | _, _ -> false
    in
    let eq_case (ci1, u1, pms1, (p1,_), _, br1) (ci2, u2, pms2, (p2,_), _, br2) =
      let eq_under_ctx (nas1, c1) (nas2, c2) =
        Int.equal (Array.length nas1) (Array.length nas2) &&
        EConstr.eq_constr sigma c1 c2
      in
      Array.equal (EConstr.eq_constr sigma) pms1 pms2 &&
      eq_under_ctx p1 p2 &&
      Array.equal eq_under_ctx br1 br2
    in
    let rec equal_rec sk1 sk2 =
      match sk1,sk2 with
      | [],[] -> true
      | App a1 :: s1, App a2 :: s2 ->
        let t1,s1' = decomp_node_last a1 s1 in
        let t2,s2' = decomp_node_last a2 s2 in
        (CbnClos.equal sigma t1 t2) && (equal_rec s1' s2')
      | Case (subs1,c1,_) :: s1, Case (subs2,c2,_) :: s2 ->
        let c1 = CbnClos.force_case subs1 c1
        and c2 = CbnClos.force_case subs2 c2 in
        eq_case c1 c2 && equal_rec s1 s2
      | (Proj (p,_,_)::s1, Proj(p2,_,_)::s2) ->
        QProjection.Repr.equal env (Projection.repr p) (Projection.repr p2)
        && equal_rec s1 s2
      | Fix (subs1,f1,s1,_) :: s1', Fix (subs2,f2,s2,_) :: s2' ->
        let f1 = CbnClos.force_fix subs1 f1
        and f2 = CbnClos.force_fix subs2 f2 in
        EConstr.eq_constr sigma (mkFix f1) (mkFix f2)
          && equal_rec (List.rev s1) (List.rev s2)
          && equal_rec s1' s2'
      | Cst c1::s1', Cst c2::s2' ->
        equal_cst_member c1.const c2.const
          && equal_rec (List.rev c1.params) (List.rev c2.params)
          && equal_rec s1' s2'
      | ((App _|Case _|Proj _|Fix _|Cst _|Primitive _)::_|[]), _ -> false
    in equal_rec (List.rev sk1) (List.rev sk2)

  let append_app_list l s =
    let a = Array.of_list l in
    append_app a s

  let rec args_size = function
    | App (i,_,j)::s -> j + 1 - i + args_size s
    | (Case _|Fix _|Proj _|Cst _|Primitive _)::_ | [] -> 0

  let strip_app s =
    let rec aux out = function
      | ( App _ as e) :: s -> aux (e :: out) s
      | s -> List.rev out,s
    in aux [] s
  let strip_n_app n s =
    let rec aux n out = function
      | App (i,a,j) as e :: s ->
         let nb = j  - i + 1 in
         if n >= nb then
           aux (n - nb) (e::out) s
         else
           let p = i+n in
           Some (CList.rev
              (if Int.equal n 0 then out else App (i,a,p-1) :: out),
            a.(p),
            if j > p then App(succ p,a,j)::s else s)
      | s -> None
    in aux n [] s

  let split_n_app n s =
    let rec aux n out s =
      match s with
      | _ when n = 0 -> Some (CList.rev out, s)
      | App (i,a,j) as e :: s ->
         let nb = j  - i + 1 in
         if n >= nb then
           aux (n - nb) (e::out) s
         else
           let p = i+n in
           let out = CList.rev (App (i,a,p-1) :: out) in
           Some (out, if j >= p then App(p,a,j)::s else s)
      | s -> None
    in aux n [] s

  let will_expose_iota args =
    List.exists
      (function (Fix (_,_,_,l) | Case (_,_,l) |
                 Proj (_,_,l) | Cst {cst_l=l}) when Cst_stack.all_volatile l -> true | _ -> false)
      args

  let list_of_app_stack s =
    let rec aux = function
      | App (i,a,j) :: s ->
        let (args',s') = aux s in
        let a' = Array.sub a i (j - i + 1) in
        (Array.fold_right (fun x y -> x::y) a' args', s')
      | s -> ([],s) in
    let (out,s') = aux s in
    let init = match s' with [] -> true | _ -> false in
    Option.init init out

  let app_stack_for_all p s =
    let rec aux = function
      | App (i,a,j) :: s ->
        let rec loop k = k > j || (p a.(k) && loop (succ k)) in
        loop i && aux s
      | [] -> true
      | _ :: _ -> false
    in aux s

  let tail n0 s0 =
    let rec aux n s =
      if Int.equal n 0 then s else
        match s with
      | App (i,a,j) :: s ->
         let nb = j  - i + 1 in
         if n >= nb then
           aux (n - nb) s
         else
           let p = i+n in
           if j >= p then App(p,a,j)::s else s
        | _ -> raise (Invalid_argument "Reductionops.Stack.tail")
    in aux n0 s0

  let nth s p =
    match strip_n_app p s with
    | Some (_,el,_) -> el
    | None -> raise Not_found

  (** This function breaks the abstraction of Cst_stack ! *)
  let best_state_opt sigma sk l =
    let rec aux sk def = function
      |(_,_,_,{volatile=true; _}) -> def
      |(cst, params, [], _) -> Some (CbnClos.inject cst, append_app_list (List.rev params) sk)
      |(cst, params, (i,t)::q, vol) -> match decomp sk with
        | Some (el,sk') when CbnClos.equal sigma el t.(i) ->
          if i = pred (Array.length t)
          then aux sk' def (cst, params, q, vol)
          else aux sk' def (cst, params, (succ i,t)::q, vol)
        | _ -> def
    in List.fold_left (aux sk) None l

  let best_state sigma (_,sk as s) l =
    match best_state_opt sigma sk l with
    | Some s -> s
    | None -> s

  let constr_of_cst_member sigma f sk =
    match f with
    | Cst_const (c, u) -> CbnClos.inject (mkConstU (c, EInstance.make u)), sk
    | Cst_proj (p,r) ->
      match decomp sk with
      | Some (hd, sk) -> CbnClos.inject (mkProj (p, r, CbnClos.force hd)), sk
      | None -> assert false

  let zip ?(refold=false) sigma s =
  let open CbnClos in
  (* [best_state_opt] only inspects the residual stack.  Try it before
     materializing eliminated terms: on success the reconstructed case/fix/proj
     would be discarded immediately. *)

  let best_refold = best_state_opt sigma in
  let rec zip = function
    | f, [] -> force f
    | f, (App (i,a,j) :: s) ->
       let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
                then a
                else Array.sub a i (j - i + 1) in
       zip (inject (mkApp (force f, Array.map force a')), s)
    | f, (Case (subs,case,cst_l)::s) when refold ->
      begin match best_refold s cst_l with
      | Some state -> zip state
      | None ->
        let (ci,u,pms,rt,iv,br) = CbnClos.force_case subs case in
        let case = mkCase (ci, u, pms, rt, iv, CbnClos.force f, br) in
        zip (inject case, s)
      end
    | f, (Case (subs,case,_)::s) ->
      let (ci,u,pms,rt,iv,br) = force_case subs case in
      zip (inject (mkCase (ci, u, pms, rt, iv, force f, br)), s)
    | f, (Fix (subs,fix,st,cst_l)::s) when refold ->
      let sk = st @ append_app [|f|] s in
      begin match best_refold sk cst_l with
      | Some state -> zip state
      | None -> zip (inject (mkFix (force_fix subs fix)), sk)
      end
  | f, (Fix (subs,fix,st,_)::s) -> zip
    (inject (mkFix (force_fix subs fix)), st @ (append_app [|f|] s))
  | f, (Cst {const;params;cst_l}::s) when refold ->
    let sk = params @ append_app [|f|] s in
    begin match const with
    | Cst_const (c, u) ->
      begin match best_refold sk cst_l with
      | Some state -> zip state
      | None -> zip (inject (mkConstU (c, EInstance.make u)), sk)
      end
    | Cst_proj (p, r) ->
      match decomp sk with
      | Some (hd, sk) ->
        begin match best_refold sk cst_l with
        | Some state -> zip state
        | None -> zip (inject (mkProj (p, r, force hd)), sk)
        end
      | None -> assert false
    end
  | f, (Cst {const;params}::s) ->
    zip (constr_of_cst_member sigma const (params @ (append_app [|f|] s)))
  | f, (Proj (p,r,cst_l)::s) when refold ->
    begin match best_refold s cst_l with
    | Some state -> zip state
    | None -> zip (inject (mkProj (p,r,force f)),s)
    end
  | f, (Proj (p,r,_)::s) -> zip (inject (mkProj (p,r,force f)),s)
  | f, (Primitive (p,c,args,kargs,cst_l)::s) ->
      zip (inject (mkConstU c), args @ append_app [|f|] s)
  in
  zip s

  let get_next_primitive_args kargs stk =
    let rec nargs = function
      | [] -> 0
      | CPrimitives.Kwhnf :: _ -> 0
      | _ :: s -> 1 + nargs s
    in
    let n = nargs kargs in
    (List.skipn (n+1) kargs, strip_n_app n stk)

end

(** The type of (machine) states (= lambda-bar-calculus' cuts) *)

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

(*************************************)
(*** Reduction using bindingss ***)
(*************************************)

(* Beta Reduction tools *)

let clos_of_app_stack sigma x args =
  if CbnClos.is_id_subst x && Stack.app_stack_for_all CbnClos.is_id_subst args then
    CbnClos.inject (Stack.zip sigma (x,args))
  else match Stack.list_of_app_stack args with
  | Some args -> CbnClos.mk_app x args
  | None -> assert false

let reduce_array_primitive sigma u p args =
  let get i = Array.get args i in
  let get_int i = match CbnClos.kind sigma (get i) with
    | subs, Int i -> Some i
    | _ -> None
  in
  let get_array i = CbnClos.array_view sigma (get i) in
  let bounded_index len i =
    if Uint63.le Uint63.zero i && Uint63.lt i (Uint63.of_int len)
    then Some (snd (Uint63.to_int2 i))
    else None
  in
  let elems_of_array a = Array.init a.CbnClos.array_length a.CbnClos.array_get in
  let mk_array elems def ty = CbnClos.mk_array u elems def ty in
  try match p with
  | CPrimitives.Arraymake ->
    begin match get_int 1 with
    | Some len ->
      let a = Parray.make len (get 2) in
      let elems, def = Parray.to_array a in
      Some (mk_array elems def (get 0))
    | None -> None
    end
  | CPrimitives.Arrayget ->
    begin match get_array 1, get_int 2 with
    | Some a, Some i ->
      let elt = match bounded_index a.CbnClos.array_length i with
        | Some i -> a.CbnClos.array_get i
        | None -> a.CbnClos.array_default
      in
      Some elt
    | _, _ -> None
    end
  | CPrimitives.Arraydefault ->
    begin match get_array 1 with
    | Some a -> Some a.CbnClos.array_default
    | None -> None
    end
  | CPrimitives.Arrayset ->
    begin match get_array 1, get_int 2 with
    | Some a, Some i ->
      let elems = match bounded_index a.CbnClos.array_length i with
        | Some i -> Array.init a.CbnClos.array_length (fun j -> if Int.equal i j then get 3 else a.CbnClos.array_get j)
        | None -> elems_of_array a
      in
      Some (mk_array elems a.CbnClos.array_default (get 0))
    | _, _ -> None
    end
  | CPrimitives.Arraycopy ->
    begin match get_array 1 with
    | Some a -> Some (mk_array (elems_of_array a) a.CbnClos.array_default (get 0))
    | None -> None
    end
  | CPrimitives.Arraylength ->
    begin match get_array 1 with
    | Some a -> Some (CbnClos.inject (mkInt (Uint63.of_int a.CbnClos.array_length)))
    | None -> None
    end
  | _ -> None
  with Invalid_argument _ -> None

let apply_subst sigma cst_l t stack =
  let rec aux cst_l t stack =
    match (Stack.decomp stack, CbnClos.kind sigma t) with
    | Some (h,stacktl), (subs, Lambda (_,_,c)) ->
       let cst_l' = Cst_stack.add_param h cst_l in
       aux cst_l' (mk_clos (Esubst.subs_cons h subs) c) stacktl
    | _ ->
      (cst_l, (t, stack))
  in
  aux cst_l t stack

(* Iota reduction tools *)

(** @return c if there is a constant c whose body is bd
    @return bd else.

    It has only a meaning because internal representation of "Fixpoint f x
    := t" is Definition f := fix f x => t

    Even more fragile that we could hope because do Module M. Fixpoint
    f x := t. End M. Definition f := u. and say goodbye to any hope
    of refolding M.f this way ...
*)
let magically_constant_of_fixbody env sigma (reference, params) bd = function
  | Name.Anonymous -> bd
  | Name.Name id ->
    let open UnivProblem in
    let cst = Constant.change_label reference id in
    if not (Environ.mem_constant cst env) then bd
    else
      let (cst, u), ctx = UnivGen.fresh_constant_instance env cst in
      match constant_opt_value_in env (cst,u) with
      | None -> bd
      | Some t ->
        let csts = EConstr.eq_constr_universes env sigma (Reductionops.beta_applist sigma (EConstr.of_constr t, params)) bd in
        begin match csts with
          | Some csts ->
            let addqs l r (qs,us) = Sorts.QVar.Map.add l r qs, us in
            let addus l r (qs,us) = qs, Univ.Level.Map.add l r us in
            let subst = Set.fold (fun cst acc ->
                match cst with
                | QLeq _ | QElimTo _ -> assert false (* eq_constr_universes cannot produce QLeq nor QElimTo constraints *)
                | QEq (a, b) ->
                  let a = match a with
                    | QVar q -> q
                    | _ -> assert false
                  in
                  addqs a b acc
                  | ULub (u, v) | UWeak (u, v) -> addus u v acc
                  | UEq (u, v) | ULe (u, v) ->
                    (* XXX add something when qsort? *)
                    let get u = match u with
                    | Sorts.SProp | Sorts.Prop -> assert false
                    | Sorts.Set -> Level.set
                    | Sorts.Type u | Sorts.GSort (_, u)
                    | Sorts.VSort (_, u) -> Option.get (Universe.level u)
                    in
                    addus (get u) (get v) acc)
                csts UVars.empty_sort_subst
            in
            let inst = UVars.subst_sort_level_instance subst u in
            applist (mkConstU (cst, EInstance.make inst), params)
          | None -> bd
        end

let contract_cofix env sigma ?reference ?current_refold base_subs (bodynum,(names,types,bodies as cofix)) =
  let nbodies = Array.length bodies in
  let current_refold = Option.map
      (fun (cst, params) -> CbnClos.mk_app (CbnClos.inject cst) (List.rev params))
      current_refold in
  let make_Fi j =
    let ind = nbodies-j-1 in
    let bd = CbnClos.mk_clos base_subs (mkCoFix (ind,cofix)) in
    if Int.equal bodynum ind then Option.default bd current_refold
    else match reference with
      | None -> bd
      | Some r ->
        CbnClos.inject (magically_constant_of_fixbody env sigma r (CbnClos.force bd) names.(ind).binder_name) in
  let closure = List.init nbodies make_Fi in
  let subst = List.fold_right Esubst.subs_cons closure base_subs in
  CbnClos.mk_clos subst bodies.(bodynum)

(** Similar to the "fix" case below *)
let singleton_best_cst = function
  | [_] as cst_l -> Cst_stack.best_cst cst_l
  | [] | _ :: _ :: _ -> None

let reduce_and_refold_cofix recfun env sigma cst_l subs ((_,(_,_,bodies)) as cofix) sk =
  let current_refold = singleton_best_cst cst_l in
  let reference =
    if Array.length bodies > 1 then Cst_stack.reference sigma cst_l
    else None
  in
  let raw_answer =
    contract_cofix env sigma ?reference ?current_refold subs cofix in
  let (x, (t, sk')) = apply_subst sigma Cst_stack.empty raw_answer sk in
  let t = match cst_l, current_refold with
    | [], _ | _, Some _ -> t
    | _ :: _, None ->
      let d = mkCoFix (CbnClos.force_cofix subs cofix) in
      CbnClos.inject (Cst_stack.best_replace sigma d cst_l (CbnClos.force t))
  in
  recfun x (t, sk')

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix env sigma ?reference ?current_refold base_subs ((recindices,bodynum),(names,types,bodies as fixdata)) =
    let nbodies = Array.length recindices in
    let current_refold = Option.map
        (fun (cst, params) -> CbnClos.mk_app (CbnClos.inject cst) (List.rev params))
        current_refold in
    let make_Fi j =
      let ind = nbodies-j-1 in
      let bd = CbnClos.mk_clos base_subs (mkFix ((recindices,ind),fixdata)) in
      if Int.equal bodynum ind then Option.default bd current_refold
      else match reference with
        | None -> bd
        | Some r -> CbnClos.inject (magically_constant_of_fixbody env sigma r (CbnClos.force bd) names.(ind).binder_name) in
    let closure = List.init nbodies make_Fi in
    let subst = List.fold_right Esubst.subs_cons closure base_subs in
    CbnClos.mk_clos subst bodies.(bodynum)

(** First we substitute the Rel bodynum by the fixpoint and then we try to
    replace the fixpoint by the best constant from [cst_l]
    Other rels are directly substituted by constants "magically found from the
    context" in contract_fix *)
let reduce_and_refold_fix recfun env sigma cst_l subs (((_,_),(_,_,bodies)) as fix) sk =
  let current_refold = singleton_best_cst cst_l in
  let reference =
    if Array.length bodies > 1 then Cst_stack.reference sigma cst_l
    else None
  in
  let raw_answer =
    contract_fix env sigma ?reference ?current_refold subs fix in
  let (x, (t, sk')) = apply_subst sigma Cst_stack.empty raw_answer sk in
  let t = match cst_l, current_refold with
    | [], _ | _, Some _ -> t
    | _ :: _, None ->
      let d = mkFix (CbnClos.force_fix subs fix) in
      CbnClos.inject (Cst_stack.best_replace sigma d cst_l (CbnClos.force t))
  in
  recfun x (t, sk')

module CredNative = Reductionops.CredNative

(** Generic reduction function with environment

    Here is where unfolded constant are stored in order to be
    eventually refolded.

    It uses ReductionBehaviour, prefers
    refold constant instead of value and tries to infer constants
    fix and cofix came from.

    It substitutes fix and cofix by the constant they come from in
    contract_* in any case .
*)

let debug_RAKAM = Reductionops.debug_RAKAM

let equal_stacks env sigma (x, l) (y, l') =
  Stack.equal env sigma l l' && CbnClos.equal sigma x y

let cbn_subst_of_rel_context_instance_list sign args subst =
  let open Context.Rel.Declaration in
  let rec aux subst sign l = match sign, l with
    | LocalAssum _ :: sign', a::args' -> aux (Esubst.subs_cons a subst) sign' args'
    | LocalDef (_,c,_)::sign', args' ->
      let c = CbnClos.mk_clos subst c in
      aux (Esubst.subs_cons c subst) sign' args'
    | [], [] -> subst
    | _ -> CErrors.anomaly (Pp.str "Instance and signature do not match.")
  in aux subst (List.rev sign) args

let apply_branch env sigma (ind, i) args subs (ci, u, pms, iv, r, lf) =
  let args = Stack.tail ci.ci_npar args in
  let args = Option.get (Stack.list_of_app_stack args) in
  let br = lf.(i - 1) in
  let body = snd br in
  let subs =
    if Int.equal ci.ci_cstr_nargs.(i - 1) ci.ci_cstr_ndecls.(i - 1) then
      (* No let-bindings *)
      List.fold_left (fun subst arg -> Esubst.subs_cons arg subst) subs args
    else
      let pms = Array.Fun1.map CbnClos.force_constr subs pms in
      let ctx = expand_branch env sigma u pms (ind, i) (fst br, mkProp) in
      cbn_subst_of_rel_context_instance_list ctx args subs
  in
  CbnClos.mk_clos subs body


exception PatternFailure

let match_einstance sigma pu u psubst =
  match UVars.Instance.pattern_match pu (EInstance.kind sigma u) psubst with
  | Some psubst -> psubst
  | None -> raise PatternFailure

let match_sort ps s psubst =
  match Sorts.pattern_match ps s psubst with
  | Some psubst -> psubst
  | None -> raise PatternFailure

let rec match_arg_pattern whrec env sigma ctx psubst p t =
  let open Declarations in
  match p with
  | EHole i ->
      let t = CbnClos.force t in
      let t' = EConstr.it_mkLambda_or_LetIn t ctx in
      Partial_subst.add_term i t' psubst
  | EHoleIgnored -> psubst
  | ERigid (ph, es) ->
      let t, stk = whrec ctx (t, Stack.empty) in
      let psubst = match_rigid_arg_pattern whrec env sigma ctx psubst ph t in
      let psubst, stk = apply_rule whrec env sigma ctx psubst es stk in
      match stk with
      | [] -> psubst
      | _ :: _ -> raise PatternFailure

and match_rigid_arg_pattern whrec env sigma ctx psubst p t =
  let subs, kt = CbnClos.kind sigma t in
  match [@ocaml.warning "-4"] p, kt with
  | PHInd (ind, pu), Ind (ind', u) ->
    if QInd.equal env ind ind' then match_einstance sigma pu u psubst else raise PatternFailure
  | PHConstr (constr, pu), Construct (constr', u) ->
    if QConstruct.equal env constr constr' then match_einstance sigma pu u psubst else raise PatternFailure
  | PHRel i, Rel n when i = n -> psubst
  | PHSort ps, Sort s -> match_sort ps (ESorts.kind sigma s) psubst
  | PHSymbol (c, pu), Const (c', u) ->
    if QConstant.equal env c c' then match_einstance sigma pu u psubst else raise PatternFailure
  | PHInt i, Int i' ->
    if Uint63.equal i i' then psubst else raise PatternFailure
  | PHFloat f, Float f' ->
    if Float64.equal f f' then psubst else raise PatternFailure
  | PHString s, String s' ->
    if Pstring.equal s s' then psubst else raise PatternFailure
  | PHLambda (ptys, pbod), _ ->
    let t = CbnClos.force t in
    let ntys, _ = EConstr.decompose_lambda sigma t in
    let na = List.length ntys and np = Array.length ptys in
    if np > na then raise PatternFailure;
    let ntys, body = EConstr.decompose_lambda_n sigma np t in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let tys = Array.of_list @@ List.rev_map snd ntys in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.skipn (na - i) ctx' @ ctx) in
    let tys = Array.map CbnClos.inject tys in
    let psubst = Array.fold_left3 (fun psubst ctx -> match_arg_pattern whrec env sigma ctx psubst) psubst contexts_upto ptys tys in
    let psubst = match_arg_pattern whrec env sigma (ctx' @ ctx) psubst (ERigid pbod) (CbnClos.inject body) in
    psubst
  | PHProd (ptys, pbod), _ ->
    let t = CbnClos.force t in
    let ntys, _ = EConstr.decompose_prod sigma t in
    let na = List.length ntys and np = Array.length ptys in
    if np > na then raise PatternFailure;
    let ntys, body = EConstr.decompose_prod_n sigma np t in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let tys = Array.of_list @@ List.rev_map snd ntys in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.skipn (na - i) ctx' @ ctx) in
    let tys = Array.map CbnClos.inject tys in
    let psubst = Array.fold_left3 (fun psubst ctx -> match_arg_pattern whrec env sigma ctx psubst) psubst contexts_upto ptys tys in
    let psubst = match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pbod (CbnClos.inject body) in
    psubst
  | (PHInd _ | PHConstr _ | PHRel _ | PHInt _ | PHFloat _ | PHString _ | PHSort _ | PHSymbol _), _ -> raise PatternFailure

and extract_n_stack args n s =
  if n = 0 then List.rev args, s else
  match Stack.decomp s with
  | Some (arg, rest) -> extract_n_stack (arg :: args) (n-1) rest
  | None -> raise PatternFailure

and apply_rule whrec env sigma ctx psubst es stk =
  match [@ocaml.warning "-4"] es, stk with
  | [], _ -> psubst, stk
  | Declarations.PEApp pargs :: e, s ->
      let np = Array.length pargs in
      let pargs = Array.to_list pargs in
      let args, s = extract_n_stack [] np s in
      let psubst = List.fold_left2 (match_arg_pattern whrec env sigma ctx) psubst pargs args in
      apply_rule whrec env sigma ctx psubst e s
  | Declarations.PECase (pind, pret, pbrs) :: e, Stack.Case (subs,(ci, _, _, _, _, _ as case), cst_l) :: s ->
      if not @@ QInd.equal env pind ci.ci_ind then raise PatternFailure;
      let dummy = mkProp in
      let (ci, u, pms, p, iv, brs) = CbnClos.force_case subs case in
      let (_, _, _, ((ntys_ret, ret), _), _, _, brs) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, dummy, brs) in
      let psubst = match_arg_pattern whrec env sigma (ntys_ret @ ctx) psubst pret (CbnClos.inject ret) in
      let psubst = Array.fold_left2 (fun psubst pat (ctx', br) -> match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pat (CbnClos.inject br)) psubst pbrs brs in
      apply_rule whrec env sigma ctx psubst e s
  | Declarations.PEProj proj :: e, Stack.Proj (proj', r, cst_l') :: s ->
      if not @@ QProjection.Repr.equal env proj (Projection.repr proj') then raise PatternFailure;
      apply_rule whrec env sigma ctx psubst e s
  | _, _ -> raise PatternFailure


let rec apply_rules whrec env sigma u r stk =
  let open Declarations in
  match r with
  | [] -> raise PatternFailure
  | { lhs_pat = (pu, elims); nvars; rhs } :: rs ->
    try
      let psubst = Partial_subst.make nvars in
      let psubst = match_einstance sigma pu u psubst in
      let psubst, stk = apply_rule whrec env sigma [] psubst elims stk in
      let subst, qsubst, usubst = Partial_subst.to_arrays psubst in
      let usubst = UVars.Instance.of_array (qsubst, usubst) in
      let rhsu = subst_instance_constr (EConstr.EInstance.make usubst) (EConstr.of_constr rhs) in
      let rhs' = substl (Array.to_list subst) rhsu in
      (CbnClos.inject rhs', stk)
    with PatternFailure -> apply_rules whrec env sigma u rs stk

let rec is_case sigma x = match CbnClos.kind sigma x with
  | (subs, Lambda (_,_, x)) | (subs, LetIn (_,_,_, x)) ->
    is_case sigma (CbnClos.mk_clos (Esubst.subs_lift subs) x)
  | (subs, Cast (x, _,_)) -> is_case sigma (CbnClos.mk_clos subs x)
  | (subs, App (hd, _)) -> is_case sigma (CbnClos.mk_clos subs hd)
  | (_, Case _) -> true
  | _ -> false


let rec whd_state_gen ?csts flags env sigma =
  let open Context.Named.Declaration in
  let open ReductionBehaviour in
  let rec whrec cst_l (x, stack) =
    let () = debug_RAKAM (fun () ->
        let open Pp in
        let pr c = Termops.Internal.print_constr_env env sigma (CbnClos.force c) in
               (h (str "<<" ++ pr x ++
                   str "|" ++ cut () ++ Cst_stack.pr env sigma pr cst_l ++
                   str "|" ++ cut () ++ Stack.pr pr stack ++
                   str ">>")))
    in
    let reduce_primitive_value () =
      match Stack.strip_app stack with
      | (_, Stack.Primitive(p,(_,u as kn),rargs,kargs,cst_l')::s) ->
        let more_to_reduce = List.exists (fun k -> CPrimitives.Kwhnf = k) kargs in
        if more_to_reduce then
          let (kargs,o) = Stack.get_next_primitive_args kargs s in
          (* Should not fail because Primitive is put on the stack only if fully applied *)
          let (before,a,after) = Option.get o in
          Some (whrec Cst_stack.empty (a,Stack.Primitive(p,kn,rargs @ Stack.append_app [|x|] before,kargs,cst_l')::after))
        else
          let n = List.length kargs in
          let (args,s) = Stack.strip_app s in
          let (args,extra_args) =
            try List.chop n args
            with List.IndexOutOfRange -> (args,[]) (* FIXME probably useless *)
          in
          let s = extra_args @ s in
          let args = Option.get (Stack.list_of_app_stack (rargs @ Stack.append_app [|x|] args)) in
          let args = Array.of_list args in
          Some
            (match reduce_array_primitive sigma u p args with
             | Some t -> whrec cst_l' (t,s)
             | None ->
               let forced_args = Array.map CbnClos.force args in
               match CredNative.red_prim env sigma (env, sigma, flags) p u forced_args with
               | Some t -> whrec cst_l' (CbnClos.inject t,s)
               | None ->
                 let t = CbnClos.mk_app (CbnClos.inject (mkConstU kn))
                     (Array.to_list args) in
                 ((t, s), cst_l))
      | _ -> None
    in
    let fold () =
      let () = debug_RAKAM (fun () ->
          Pp.(str "<><><><><>")) in
      ((x, stack),cst_l)
    in
    let c0 = CbnClos.kind sigma x in
    match c0 with
    | _, Rel n when RedFlags.red_set flags RedFlags.fDELTA ->
      (match lookup_rel n env with
      | LocalDef (_,body,_) -> whrec Cst_stack.empty (CbnClos.lift n (CbnClos.inject body), stack)
      | _ -> fold ())
    | _, Var id when RedFlags.red_set flags (RedFlags.fVAR id) ->
      (match lookup_named id env with
      | LocalDef (_,body,_) ->
        whrec (Cst_stack.add_cst (mkVar id) cst_l) (CbnClos.inject body, stack)
      | _ -> fold ())
    | _, (Evar _ | Meta _) -> fold ()
    | _, Const (c,u as const) ->
      Reductionops.reduction_effect_hook env sigma c
         (lazy (Stack.zip sigma (x,fst (Stack.strip_app stack))));
      if RedFlags.red_set flags (RedFlags.fCONST c) then
       let u' = EInstance.kind sigma u in
       match
         try Ok (constant_value_in env sigma (c, u))
         with NotEvaluableConst e -> Error e
       with
       | Ok body ->
         begin
          (* Looks for ReductionBehaviour *)
            match ReductionBehaviour.get c with
            | None -> whrec (Cst_stack.add_cst (mkConstU const) cst_l) (CbnClos.inject body, stack)
            | Some behavior ->
              begin match behavior with
              | NeverUnfold -> fold ()
              | (UnfoldWhen { nargs = Some n } |
                 UnfoldWhenNoMatch { nargs = Some n } )
                when Stack.args_size stack < n ->
                fold ()
              | UnfoldWhenNoMatch { recargs; nargs } -> (* maybe unfolds *)
                  let app_sk,sk = Stack.strip_app stack in
                  let volatile = Option.has_some nargs in
                  let (tm',sk'),cst_l' =
                    match recargs with
                    | [] ->
                      let cst_l = Cst_stack.add_cst ~volatile ~refold_after_iota:true
                          (mkConstU const) cst_l in
                      whrec cst_l (CbnClos.inject body, app_sk)
                    | curr :: remains -> match Stack.strip_n_app curr app_sk with
                      | None -> (x,app_sk), cst_l
                      | Some (bef,arg,app_sk') ->
                        let cst_l = Stack.Cst
                            { const = Stack.Cst_const (fst const, u');
                              volatile;
                              refold_after_iota = true;
                              curr; remains; params=bef; cst_l;
                            }
                        in
                        whrec Cst_stack.empty (arg,cst_l :: app_sk')
                  in
                  (* If the selected recursive argument definitely changed,
                     the unfolded state cannot be equal to the original one;
                     avoid a full stack comparison, which may force unrelated
                     arguments only to discard the equality result. *)
                  let recarg_changed = match recargs with
                    | [] -> false
                    | curr :: _ ->
                      not (CbnClos.equal sigma x tm') ||
                      match Stack.strip_n_app curr app_sk, Stack.strip_n_app curr sk' with
                      | Some (_, arg, _), Some (_, arg', _) ->
                        not (CbnClos.equal sigma arg arg')
                      | _ -> false
                  in
                  if (not recarg_changed && equal_stacks env sigma (x, app_sk) (tm', sk'))
                  || Stack.will_expose_iota sk'
                  || is_case sigma tm'
                  then fold ()
                  else whrec cst_l' (tm', sk' @ sk)
              | UnfoldWhen { recargs; nargs } -> (* maybe unfolds *)
                begin match recargs with
                | [] -> (* if nargs has been specified *)
                  (* CAUTION : the constant is NEVER refolded (even when it hides a (co)fix) *)
                  whrec cst_l (CbnClos.inject body, stack)
                | curr :: remains -> match Stack.strip_n_app curr stack with
                  | None -> fold ()
                  | Some (bef,arg,s') ->
                    let cst_l = Stack.Cst
                        { const = Stack.Cst_const (fst const, u');
                          volatile = Option.has_some nargs;
                          refold_after_iota = false;
                          curr; remains; params=bef; cst_l;
                        }
                    in
                    whrec Cst_stack.empty (arg,cst_l::s')
                end
              end

          end
       | Error (IsPrimitive (_u,p)) ->
         begin
         let p_arity = CPrimitives.arity p in
         let n_args = Stack.args_size stack in
         (* Make sure we have enough arguments for the primitive. *)
         if p_arity > n_args then fold () else
         (* Find the first argument that must be reduced to weak-head normal form. *)
         let nb_no_eval, kargs =
           let rec nb_leading_no_eval_args n = function
             | (CPrimitives.Kparam | CPrimitives.Karg) :: kargs ->
               nb_leading_no_eval_args (n + 1) kargs
             | (CPrimitives.Kwhnf :: _ | []) as kargs -> n, kargs
           in
           nb_leading_no_eval_args 0 (CPrimitives.kind p)
         in
         match kargs with
         | _ :: kargs ->
           let before, arg, after =
             Option.get (Stack.strip_n_app nb_no_eval stack)
           in
           whrec Cst_stack.empty
             (arg, Stack.Primitive (p, const, before, kargs, cst_l) :: after)
         | [] ->
           (* No argument needs head reduction; try the primitive immediately. *)
           let args, stack = Option.get (Stack.split_n_app nb_no_eval stack) in
           let args = Array.of_list (Option.get (Stack.list_of_app_stack args)) in
           begin match reduce_array_primitive sigma (snd const) p args with
           | Some t -> whrec cst_l (t, stack)
           | None ->
             let forced_args = Array.map CbnClos.force args in
             match CredNative.red_prim env sigma (env, sigma, flags) p
                     (snd const) forced_args with
             | Some t -> whrec cst_l (CbnClos.inject t, stack)
             | None ->
               let t = CbnClos.mk_app (CbnClos.inject (mkConstU const))
                   (Array.to_list args) in
               ((t, stack), cst_l)
           end
         end
       | Error (HasRules (u', b, r)) ->
         begin try
           let red_fun ctx =
             let env = push_rel_context ctx env in
             whd_state_gen flags env sigma
           in
           let rhs_stack = apply_rules red_fun env sigma u r stack in
           whrec Cst_stack.empty rhs_stack
         with PatternFailure ->
           if not b then fold () else
             match Stack.strip_app stack with
             | args, (Stack.Fix (subs,f,s',cst_l)::s'') when RedFlags.red_set flags RedFlags.fFIX ->
               let x' = clos_of_app_stack sigma x args in
               let out_sk = s' @ (Stack.append_app [|x'|] s'') in
               reduce_and_refold_fix whrec env sigma cst_l subs f out_sk
             | _ -> fold ()
         end
       | Error _ -> fold ()
      else fold ()
    | subs, Proj (p, r, c) when RedFlags.red_projection flags p ->
      (let npars = Projection.npars p in
       let c = mk_clos subs c in
       match ReductionBehaviour.get (Environ.projection_repr_constant env (Projection.repr p)) with
       | None ->
         let stack' = (c, Stack.Proj (p, r, cst_l) :: stack) in
         let stack'', csts = whrec Cst_stack.empty stack' in
         if equal_stacks env sigma stack' stack'' then fold ()
         else stack'', csts
       | Some behavior ->
         begin match behavior with
         | NeverUnfold -> fold ()
         | (UnfoldWhen { nargs = Some n }
           | UnfoldWhenNoMatch { nargs = Some n })
           when Stack.args_size stack < n - (npars + 1) -> fold ()
         | UnfoldWhen { recargs }
         | UnfoldWhenNoMatch { recargs }-> (* maybe unfolds *)
           let recargs = List.map_filter (fun x ->
               let idx = x - npars in
               if idx < 0 then None else Some idx) recargs
           in
           let volatile = match behavior with
             | UnfoldWhen {nargs} -> Option.has_some nargs
             | UnfoldWhenNoMatch _ | NeverUnfold -> false
           in
           match recargs with
           | [] -> (* if nargs has been specified *)
             (* CAUTION : the constant is NEVER refold
                              (even when it hides a (co)fix) *)
             let stack' = (c, Stack.Proj (p, r, cst_l) :: stack) in
             whrec Cst_stack.empty(* cst_l *) stack'
           | curr :: remains ->
             match Stack.strip_n_app curr (Stack.append_app [|c|] stack) with
             | None -> fold ()
             | Some (bef,arg,s') ->
               let cst_l = Stack.Cst
                   { const=Stack.Cst_proj (p,r);
                     curr;
                     remains;
                     volatile;
                     refold_after_iota =
                       (match behavior with
                        | UnfoldWhenNoMatch _ -> true
                        | UnfoldWhen _ | NeverUnfold -> false);
                     params=bef;
                     cst_l;
                   }
               in
               whrec Cst_stack.empty (arg,cst_l::s')
         end)

    | subs, LetIn (_,b,_,c) when RedFlags.red_set flags RedFlags.fZETA ->
      whrec cst_l (mk_clos (Esubst.subs_cons (mk_clos subs b) subs) c, stack)
    | subs, Cast (c,_,_) -> whrec cst_l (mk_clos subs c, stack)
    | subs, App (f,cl)  ->
      let f = mk_clos subs f in
      let cl = mk_clos_vect subs cl in
      whrec
        (Cst_stack.add_args cl cst_l)
        (f, Stack.append_app cl stack)
    | subs, Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when RedFlags.red_set flags RedFlags.fBETA ->
        let (cst_l, p) = apply_subst sigma cst_l x stack in
        whrec cst_l p
      | _ -> fold ())

    | subs, Case (ci,u,pms,p,iv,d,lf) ->
      whrec Cst_stack.empty (mk_clos subs d, Stack.Case (subs,(ci,u,pms,p,iv,lf),cst_l) :: stack)

    | subs, Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> fold ()
      |Some (bef,arg,s') ->
        whrec Cst_stack.empty (arg, Stack.Fix(subs,f,bef,cst_l)::s'))

    | _, Construct (cstr ,u) ->
      let use_match = RedFlags.red_set flags RedFlags.fMATCH in
      let use_fix = RedFlags.red_set flags RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case(subs,case,case_cst_l)::s') when use_match ->
          let r = apply_branch env sigma cstr args subs case in
          whrec Cst_stack.empty (r, s')
        |args, (Stack.Proj (p,_,_)::s') when use_match ->
          whrec Cst_stack.empty (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (subs,f,s',cst_l)::s'') when use_fix ->
          let x' = clos_of_app_stack sigma x args in
          let out_sk = s' @ (Stack.append_app [|x'|] s'') in
          reduce_and_refold_fix whrec env sigma cst_l subs f out_sk
        |args, (Stack.Cst {const;curr;remains;volatile;refold_after_iota;params=s';cst_l} :: s'') ->
          let x' = clos_of_app_stack sigma x args in
          begin match remains with
          | [] ->
            (match const with
            | Stack.Cst_const const ->
              (match constant_opt_value_in env const with
              | None -> fold ()
              | Some body ->
                let const = (fst const, EInstance.make (snd const)) in
                let body = EConstr.of_constr body in
                let cst_l = Cst_stack.add_cst ~volatile ~refold_after_iota (mkConstU const) cst_l in
                whrec cst_l (CbnClos.inject body, s' @ (Stack.append_app [|x'|] s'')))
            | Stack.Cst_proj (p,r) ->
              let stack = s' @ (Stack.append_app [|x'|] s'') in
              match Stack.strip_n_app 0 stack with
              | None -> assert false
              | Some (_,arg,s'') ->
                whrec Cst_stack.empty (arg, Stack.Proj (p,r,cst_l) :: s''))
          | next :: remains' -> match Stack.strip_n_app (next-curr-1) s'' with
            | None -> fold ()
            | Some (bef,arg,s''') ->
              let cst_l = Stack.Cst
                  { const;
                    curr=next;
                    volatile;
                    refold_after_iota;
                    remains=remains';
                    params=s' @ (Stack.append_app [|x'|] bef);
                    cst_l;
                  }
              in
              whrec Cst_stack.empty (arg, cst_l :: s''')
          end
        |_, (Stack.App _)::_ -> assert false
        |_, _ -> fold ()
      else fold ()

    | subs, CoFix cofix ->
      if RedFlags.red_set flags RedFlags.fCOFIX then
        match Stack.strip_app stack with
        |args, ((Stack.Case _ |Stack.Proj _)::s') ->
          reduce_and_refold_cofix whrec env sigma cst_l subs cofix stack
        |_ -> fold ()
      else fold ()

    | subs, PUnblock (_ty, b) ->
      let b = mk_clos subs b in
      let ((b', bstack), _) = whrec Cst_stack.empty (b, Stack.empty) in
      begin match bstack, CbnClos.kind sigma b' with
      | [], (body_subs, PBlock (_, _, body)) ->
        whrec cst_l (mk_clos body_subs body, stack)
      | _ -> fold ()
      end

    | subs, PRun (_ty, _k, b, cont) ->
      let b = mk_clos subs b in
      let cont = mk_clos subs cont in
      let ((b', bstack), _) = whrec Cst_stack.empty (b, Stack.empty) in
      begin match bstack, CbnClos.kind sigma b' with
      | [], (body_subs, PBlock (_, _, body)) ->
        let body = mk_clos body_subs body in
        whrec cst_l (cont, Stack.append_app [|body|] stack)
      | _ -> fold ()
      end

    | _, (Int _ | Float _ | String _ | Array _ | PBlock _) ->
      begin match reduce_primitive_value () with
      | Some res -> res
      | None ->
      begin match Stack.strip_app stack with
      | args, (Stack.Cst {const;curr;remains;volatile;refold_after_iota;params=s';cst_l} :: s'') ->
        let x' = clos_of_app_stack sigma x args in
          begin match remains with
          | [] ->
            (match const with
            | Stack.Cst_const const ->
              (match constant_opt_value_in env const with
              | None -> fold ()
              | Some body ->
                let const = (fst const, EInstance.make (snd const)) in
                let body = EConstr.of_constr body in
                let cst_l = Cst_stack.add_cst ~volatile ~refold_after_iota (mkConstU const) cst_l in
                whrec cst_l (CbnClos.inject body, s' @ (Stack.append_app [|x'|] s'')))
            | Stack.Cst_proj (p,r) ->
              let stack = s' @ (Stack.append_app [|x'|] s'') in
              match Stack.strip_n_app 0 stack with
              | None -> assert false
              | Some (_,arg,s'') ->
                whrec Cst_stack.empty (arg, Stack.Proj (p,r,cst_l) :: s''))
          | next :: remains' -> match Stack.strip_n_app (next-curr-1) s'' with
            | None -> fold ()
            | Some (bef,arg,s''') ->
              let cst_l = Stack.Cst
                  { const;
                    curr=next;
                    volatile;
                    refold_after_iota;
                    remains=remains';
                    params=s' @ (Stack.append_app [|x'|] bef);
                    cst_l;
                  }
              in
              whrec Cst_stack.empty (arg, cst_l :: s''')
          end
       | _ -> fold ()
      end
      end

    | _, (Rel _ | Var _ | LetIn _ | Proj _) -> fold ()
    | _, (Sort _ | Ind _ | Prod _) -> fold ()
  in
  fun xs ->
  let (s,cst_l) = whrec (Option.default Cst_stack.empty csts) xs in
  Stack.best_state sigma s cst_l

let whd_cbn flags env sigma t =
  let state = whd_state_gen flags env sigma (CbnClos.inject t, Stack.empty) in
  Stack.zip ~refold:true sigma state

let norm_cbn flags env sigma t =
  let push_rel_check_zeta d env =
    let open RedFlags in
    let d = match d with
      | LocalDef (na,_,t) when not (red_set flags fZETA) -> LocalAssum (na,t)
      | d -> d in
    push_rel d env
  in
  (* Refold the weak-head state before descending recursively.  If we map over
     the delayed stack directly, application arguments are normalized before
     enclosing case/fix/constant frames can refold or discard them. *)
  let rec strongrec env t =
    Termops.map_constr_with_full_binders env sigma
      push_rel_check_zeta strongrec env (whd_cbn flags env sigma t)
  in
  strongrec env t
