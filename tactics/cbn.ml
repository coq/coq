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
open Termops
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

type volatile = { volatile : bool } [@@unboxed]

(** Machinery about stack of unfolded constants *)
module Cst_stack = struct
  open EConstr

(** constant * params * args

- constant applied to params = term in head applied to args
- there is at most one arguments with an empty list of args, it must be the first.
- in args, the int represents the indice of the first arg to consider *)
  type t = (constr * constr list * (int * constr array) list * volatile)  list

  let empty = []
  let all_volatile = CList.for_all (fun (_,_,_,{volatile}) -> volatile)

  let drop_useless = function
    | _ :: ((_,_,[],_)::_ as q) -> q
    | l -> l

  let add_param h cst_l =
    let append2cst = function
      | (c,params,[],vol) -> (c, h::params, [], vol)
      | (c,params,((i,t)::q),vol) when i = pred (Array.length t) ->
        (c, params, q, vol)
      | (c,params,(i,t)::q, vol) ->
        (c, params, (succ i,t)::q, vol)
    in
      drop_useless (List.map append2cst cst_l)

  let add_args cl =
    List.map (fun (a,b,args,vol) -> (a,b,(0,cl)::args,vol))

  let add_cst ?(volatile=false) cst = function
    | (_,_,[],_) :: q as l -> l
    | l -> (cst,[],[],{volatile})::l

  let best_cst = function
    | (cst,params,[],_)::_ -> Some(cst,params)
    | _ -> None

  let reference sigma t = match best_cst t with
    | Some (c, params) when isConst sigma c -> Some (fst (destConst sigma c), params)
    | _ -> None

  (** [best_replace d cst_l c] makes the best replacement for [d]
      by [cst_l] in [c] *)
  let best_replace sigma d cst_l c =
    let reconstruct_head = List.fold_left
      (fun t (i,args) -> mkApp (t,Array.sub args i (Array.length args - i))) in
    List.fold_right
      (fun (cst,params,args,_) t -> Termops.replace_term sigma
        (reconstruct_head d args)
        (applist (cst, List.rev params))
        t) cst_l c

  let pr env sigma l =
    let open Pp in
    let p_c c = Termops.Internal.print_constr_env env sigma c in
    prlist_with_sep pr_semicolon
      (fun (c,params,args,{volatile}) ->
        hov 1 (str"(" ++ p_c c ++ str ")" ++ spc () ++ pr_sequence p_c params ++ spc () ++ str "(args:" ++
                 pr_sequence (fun (i,el) -> prvect_with_sep spc p_c (Array.sub el i (Array.length el - i))) args ++
               str ")" ++
              (if volatile then str " (volatile)" else mt()))) l
end


(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack :
sig
  open EConstr
  type 'a app_node

  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t * ERelevance.t

  type 'a case_stk =
    case_info * EInstance.t * 'a array * ('a,ERelevance.t) pcase_return * 'a pcase_invert * ('a,ERelevance.t) pcase_branch array
  type 'a member =
  | App of 'a app_node
  | Case of 'a case_stk * Cst_stack.t
  | Proj of Projection.t * ERelevance.t * Cst_stack.t
  | Fix of ('a, 'a, ERelevance.t) pfixpoint * 'a t * Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * 'a t * CPrimitives.args_red * Cst_stack.t
  | Cst of { const : cst_member;
             curr : int;
             remains : int list;
             params : 'a t;
             volatile : bool;
             cst_l : Cst_stack.t;
           }

  and 'a t = 'a member list

  val pr : ('a -> Pp.t) -> 'a t -> Pp.t
  val empty : 'a t
  val append_app : 'a array -> 'a t -> 'a t
  val decomp : 'a t -> ('a * 'a t) option
  val equal : env -> ('a -> 'a -> bool) -> (('a, 'a, ERelevance.t) pfixpoint -> ('a, 'a, ERelevance.t) pfixpoint -> bool)
    -> ('a case_stk -> 'a case_stk -> bool) -> 'a t -> 'a t -> bool
  val strip_app : 'a t -> 'a t * 'a t
  val strip_n_app : int -> 'a t -> ('a t * 'a * 'a t) option
  val will_expose_iota : 'a t -> bool
  val list_of_app_stack : constr t -> constr list option
  val args_size : 'a t -> int
  val tail : int -> 'a t -> 'a t
  val nth : 'a t -> int -> 'a
  val best_state : Evd.evar_map -> constr * constr t -> Cst_stack.t -> constr * constr t
  val zip : ?refold:bool -> Evd.evar_map -> constr * constr t -> constr
  val check_native_args : CPrimitives.t -> 'a t -> bool
  val get_next_primitive_args : CPrimitives.args_red -> 'a t -> CPrimitives.args_red * ('a t * 'a * 'a t) option
end =
struct
  open EConstr
  type 'a app_node = int * 'a array * int
  (* first releavnt position, arguments, last relevant position *)

  (*
     Invariant that this module must ensure :
     (behare of direct access to app_node by the rest of Reductionops)
     - in app_node (i,_,j) i <= j
     - There is no array realocation (outside of debug printing)
   *)

  let pr_app_node pr (i,a,j) =
    let open Pp in surround (
                     prvect_with_sep pr_comma pr (Array.sub a i (j - i + 1))
                     )


  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t * ERelevance.t

  type 'a case_stk =
    case_info * EInstance.t * 'a array * ('a,ERelevance.t) pcase_return * 'a pcase_invert * ('a,ERelevance.t) pcase_branch array
  type 'a member =
  | App of 'a app_node
  | Case of 'a case_stk * Cst_stack.t
  | Proj of Projection.t * ERelevance.t * Cst_stack.t
  | Fix of ('a, 'a, ERelevance.t) pfixpoint * 'a t * Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * 'a t * CPrimitives.args_red * Cst_stack.t
  | Cst of { const : cst_member;
             curr : int;
             remains : int list;
             params : 'a t;
             volatile : bool;
             cst_l : Cst_stack.t;
           }

  and 'a t = 'a member list

  (* Debugging printer *)
  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case ((_,_,_,_,_,br),cst) ->
       str "ZCase(" ++
         prvect_with_sep (pr_bar) (fun (_, b) -> pr_c b) br
       ++ str ")"
    | Proj (p,_,cst) ->
      str "ZProj(" ++ Projection.debug_print p ++ str ")"
    | Fix (f,args,cst) ->
       str "ZFix(" ++ Constr.debug_print_fix pr_c f
       ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Primitive (p,c,args,kargs,cst_l) ->
      str "ZPrimitive(" ++ str (CPrimitives.to_string p)
      ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Cst {const=mem;curr;remains;params;cst_l} ->
      str "ZCst(" ++ pr_cst_member pr_c mem ++ pr_comma () ++ int curr
      ++ pr_comma () ++
        prlist_with_sep pr_semicolon int remains ++
        pr_comma () ++ pr pr_c params ++ str ")"
  and pr pr_c l =
    let open Pp in
    prlist_with_sep pr_semicolon (fun x -> hov 1 (pr_member pr_c x)) l

  and pr_cst_member pr_c c =
    let open Pp in
      match c with
      | Cst_const (c, u) ->
        if UVars.Instance.is_empty u then Constant.debug_print c
        else str"(" ++ Constant.debug_print c ++ str ", " ++
          UVars.Instance.pr Sorts.QVar.raw_pr Univ.Level.raw_pr u ++ str")"
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

  let equal env f f_fix f_case sk1 sk2 =
    let equal_cst_member x y =
      match x, y with
      | Cst_const (c1,u1), Cst_const (c2, u2) ->
        QConstant.equal env c1 c2 && UVars.Instance.equal u1 u2
      | Cst_proj (p1,_), Cst_proj (p2,_) -> QProjection.Repr.equal env (Projection.repr p1) (Projection.repr p2)
      | _, _ -> false
    in
    let rec equal_rec sk1 sk2 =
      match sk1,sk2 with
      | [],[] -> true
      | App a1 :: s1, App a2 :: s2 ->
        let t1,s1' = decomp_node_last a1 s1 in
        let t2,s2' = decomp_node_last a2 s2 in
        (f t1 t2) && (equal_rec s1' s2')
      | Case ((ci1,pms1,p1,t1,iv1,a1),_) :: s1, Case ((ci2,pms2,p2,iv2,t2,a2),_) :: s2 ->
        f_case (ci1,pms1,p1,t1,iv1,a1) (ci2,pms2,p2,iv2,t2,a2) && equal_rec s1 s2
      | (Proj (p,_,_)::s1, Proj(p2,_,_)::s2) ->
        QProjection.Repr.equal env (Projection.repr p) (Projection.repr p2)
        && equal_rec s1 s2
      | Fix (f1,s1,_) :: s1', Fix (f2,s2,_) :: s2' ->
        f_fix f1 f2
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

  let will_expose_iota args =
    List.exists
      (function (Fix (_,_,l) | Case (_,l) |
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
  let best_state sigma (_,sk as s) l =
    let rec aux sk def = function
      |(_,_,_,{volatile=true}) -> def
      |(cst, params, [], _) -> (cst, append_app_list (List.rev params) sk)
      |(cst, params, (i,t)::q, vol) -> match decomp sk with
        | Some (el,sk') when EConstr.eq_constr sigma el t.(i) ->
          if i = pred (Array.length t)
          then aux sk' def (cst, params, q, vol)
          else aux sk' def (cst, params, (succ i,t)::q, vol)
        | _ -> def
    in List.fold_left (aux sk) s l

  let constr_of_cst_member f sk =
    match f with
    | Cst_const (c, u) -> mkConstU (c, EInstance.make u), sk
    | Cst_proj (p,r) ->
      match decomp sk with
      | Some (hd, sk) -> mkProj (p, r, hd), sk
      | None -> assert false

  let zip ?(refold=false) sigma s =
  let rec zip = function
    | f, [] -> f
    | f, (App (i,a,j) :: s) ->
       let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
                then a
                else Array.sub a i (j - i + 1) in
       zip (mkApp (f, a'), s)
    | f, (Case ((ci,u,pms,rt,iv,br),cst_l)::s) when refold ->
      zip (best_state sigma (mkCase (ci,u,pms,rt,iv,f,br), s) cst_l)
    | f, (Case ((ci,u,pms,rt,iv,br),_)::s) -> zip (mkCase (ci,u,pms,rt,iv,f,br), s)
    | f, (Fix (fix,st,cst_l)::s) when refold ->
      zip (best_state sigma (mkFix fix, st @ (append_app [|f|] s)) cst_l)
  | f, (Fix (fix,st,_)::s) -> zip
    (mkFix fix, st @ (append_app [|f|] s))
  | f, (Cst {const;params;cst_l}::s) when refold ->
    zip (best_state sigma (constr_of_cst_member const (params @ (append_app [|f|] s))) cst_l)
  | f, (Cst {const;params}::s) ->
    zip (constr_of_cst_member const (params @ (append_app [|f|] s)))
  | f, (Proj (p,r,cst_l)::s) when refold ->
    zip (best_state sigma (mkProj (p,r,f),s) cst_l)
  | f, (Proj (p,r,_)::s) -> zip (mkProj (p,r,f),s)
  | f, (Primitive (p,c,args,kargs,cst_l)::s) ->
      zip (mkConstU c, args @ append_app [|f|] s)
  in
  zip s

  (* Check if there is enough arguments on [stk] w.r.t. arity of [op] *)
  let check_native_args op stk =
    let nargs = CPrimitives.arity op in
    let rargs = args_size stk in
    nargs <= rargs

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

let apply_subst env sigma cst_l t stack =
  let rec aux env cst_l t stack =
    match (Stack.decomp stack, EConstr.kind sigma t) with
    | Some (h,stacktl), Lambda (_,_,c) ->
       let cst_l' = Cst_stack.add_param h cst_l in
       aux (h::env) cst_l' c stacktl
    | _ -> (cst_l, (substl env t, stack))
  in
  aux env cst_l t stack

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
    let cst = Constant.change_label reference (Label.of_id id) in
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
                | QEq (a,b) | QLeq (a,b) ->
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
                    | Sorts.Type u | Sorts.QSort (_, u) -> Option.get (Universe.level u)
                    in
                    addus (get u) (get v) acc)
                csts UVars.empty_sort_subst
            in
            let inst = UVars.subst_sort_level_instance subst u in
            applist (mkConstU (cst, EInstance.make inst), params)
          | None -> bd
        end

let contract_cofix env sigma ?reference (bodynum,(names,types,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    if Int.equal bodynum ind then mkCoFix (ind,typedbodies)
    else
      let bd = mkCoFix (ind,typedbodies) in
      match reference with
      | None -> bd
      | Some r -> magically_constant_of_fixbody env sigma r bd names.(ind).binder_name in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(** Similar to the "fix" case below *)
let reduce_and_refold_cofix recfun env sigma cst_l cofix sk =
  let raw_answer =
    contract_cofix env sigma ?reference:(Cst_stack.reference sigma cst_l) cofix in
  let (x, (t, sk')) = apply_subst [] sigma Cst_stack.empty raw_answer sk in
  let t' = Cst_stack.best_replace sigma (mkCoFix cofix) cst_l t in
  recfun x (t', sk')

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix env sigma ?reference ((recindices,bodynum),(names,types,bodies as typedbodies)) =
    let nbodies = Array.length recindices in
    let make_Fi j =
      let ind = nbodies-j-1 in
      if Int.equal bodynum ind then mkFix ((recindices,ind),typedbodies)
      else
        let bd = mkFix ((recindices,ind),typedbodies) in
        match reference with
        | None -> bd
        | Some r -> magically_constant_of_fixbody env sigma r bd names.(ind).binder_name in
    let closure = List.init nbodies make_Fi in
    substl closure bodies.(bodynum)

(** First we substitute the Rel bodynum by the fixpoint and then we try to
    replace the fixpoint by the best constant from [cst_l]
    Other rels are directly substituted by constants "magically found from the
    context" in contract_fix *)
let reduce_and_refold_fix recfun env sigma cst_l fix sk =
  let raw_answer =
    contract_fix env sigma ?reference:(Cst_stack.reference sigma cst_l) fix in
  let (x, (t, sk')) = apply_subst [] sigma Cst_stack.empty raw_answer sk in
  let t' = Cst_stack.best_replace sigma (mkFix fix) cst_l t in
  recfun x (t', sk')

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
  let f_equal x y = eq_constr sigma x y in
  let eq_fix a b = f_equal (mkFix a) (mkFix b) in
  let eq_case (ci1, u1, pms1, (p1,_), _, br1) (ci2, u2, pms2, (p2,_), _, br2) =
    Array.equal f_equal pms1 pms2 &&
    f_equal (snd p1) (snd p2) &&
    Array.equal (fun (_, c1) (_, c2) -> f_equal c1 c2) br1 br2
  in
  Stack.equal env f_equal eq_fix eq_case l l' && f_equal x y

let apply_branch env sigma (ind, i) args (ci, u, pms, iv, r, lf) =
  let args = Stack.tail ci.ci_npar args in
  let args = Option.get (Stack.list_of_app_stack args) in
  let br = lf.(i - 1) in
  let subst =
    if Int.equal ci.ci_cstr_nargs.(i - 1) ci.ci_cstr_ndecls.(i - 1) then
      (* No let-bindings *)
      List.rev args
    else
      let ctx = expand_branch env sigma u pms (ind, i) br in
      subst_of_rel_context_instance_list ctx args
  in
  Vars.substl subst (snd br)


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
  let t' = EConstr.it_mkLambda_or_LetIn t ctx in
  match p with
  | EHole i -> Partial_subst.add_term i t' psubst
  | EHoleIgnored -> psubst
  | ERigid (ph, es) ->
      let (t, stk), _ = whrec Cst_stack.empty (t, Stack.empty) in
      let psubst = match_rigid_arg_pattern whrec env sigma ctx psubst ph t in
      let psubst, stk = apply_rule whrec env sigma ctx psubst es stk in
      match stk with
      | [] -> psubst
      | _ :: _ -> raise PatternFailure

and match_rigid_arg_pattern whrec env sigma ctx psubst p t =
  match [@ocaml.warning "-4"] p, EConstr.kind sigma t with
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
    let ntys, _ = EConstr.decompose_lambda sigma t in
    let na = List.length ntys and np = Array.length ptys in
    if np > na then raise PatternFailure;
    let ntys, body = EConstr.decompose_lambda_n sigma np t in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let tys = Array.of_list @@ List.rev_map snd ntys in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.skipn (na - i) ctx' @ ctx) in
    let psubst = Array.fold_left3 (fun psubst ctx -> match_arg_pattern whrec env sigma ctx psubst) psubst contexts_upto ptys tys in
    let psubst = match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pbod body in
    psubst
  | PHProd (ptys, pbod), _ ->
    let ntys, _ = EConstr.decompose_prod sigma t in
    let na = List.length ntys and np = Array.length ptys in
    if np > na then raise PatternFailure;
    let ntys, body = EConstr.decompose_prod_n sigma np t in
    let ctx' = List.map (fun (n, ty) -> Context.Rel.Declaration.LocalAssum (n, ty)) ntys in
    let tys = Array.of_list @@ List.rev_map snd ntys in
    let na = Array.length tys in
    let contexts_upto = Array.init na (fun i -> List.skipn (na - i) ctx' @ ctx) in
    let psubst = Array.fold_left3 (fun psubst ctx -> match_arg_pattern whrec env sigma ctx psubst) psubst contexts_upto ptys tys in
    let psubst = match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pbod body in
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
  | Declarations.PECase (pind, pu, pret, pbrs) :: e, Stack.Case ((ci, u, pms, p, iv, brs), cst_l) :: s ->
      if not @@ QInd.equal env pind ci.ci_ind then raise PatternFailure;
      let dummy = mkProp in
      let psubst = match_einstance sigma pu u psubst in
      let (_, _, _, ((ntys_ret, ret), _), _, _, brs) = EConstr.annotate_case env sigma (ci, u, pms, p, NoInvert, dummy, brs) in
      let psubst = match_arg_pattern whrec env sigma (ntys_ret @ ctx) psubst pret ret in
      let psubst = Array.fold_left2 (fun psubst pat (ctx', br) -> match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pat br) psubst pbrs brs in
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
      (rhs', stk)
    with PatternFailure -> apply_rules whrec env sigma u rs stk




let whd_state_gen ?csts flags env sigma =
  let open Context.Named.Declaration in
  let open ReductionBehaviour in
  let rec whrec cst_l (x, stack) =
    let () = debug_RAKAM (fun () ->
        let open Pp in
        let pr c = Termops.Internal.print_constr_env env sigma c in
               (h (str "<<" ++ pr x ++
                   str "|" ++ cut () ++ Cst_stack.pr env sigma cst_l ++
                   str "|" ++ cut () ++ Stack.pr pr stack ++
                   str ">>")))
    in
    let c0 = EConstr.kind sigma x in
    let fold () =
      let () = debug_RAKAM (fun () ->
          Pp.(str "<><><><><>")) in
      ((EConstr.of_kind c0, stack),cst_l)
    in
    match c0 with
    | Rel n when RedFlags.red_set flags RedFlags.fDELTA ->
      (match lookup_rel n env with
      | LocalDef (_,body,_) -> whrec Cst_stack.empty (lift n body, stack)
      | _ -> fold ())
    | Var id when RedFlags.red_set flags (RedFlags.fVAR id) ->
      (match lookup_named id env with
      | LocalDef (_,body,_) ->
        whrec (Cst_stack.add_cst (mkVar id) cst_l) (body, stack)
      | _ -> fold ())
    | Evar _ | Meta _ -> fold ()
    | Const (c,u as const) ->
      Reductionops.reduction_effect_hook env sigma c
         (lazy (EConstr.to_constr sigma (Stack.zip sigma (x,fst (Stack.strip_app stack)))));
      if RedFlags.red_set flags (RedFlags.fCONST c) then
       let u' = EInstance.kind sigma u in
       match constant_value_in env (c, u') with
       | body ->
         begin
          let body = EConstr.of_constr body in
          (* Looks for ReductionBehaviour *)
            match ReductionBehaviour.get c with
            | None -> whrec (Cst_stack.add_cst (mkConstU const) cst_l) (body, stack)
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
                      whrec (Cst_stack.add_cst ~volatile (mkConstU const) cst_l) (body, app_sk)
                    | curr :: remains -> match Stack.strip_n_app curr app_sk with
                      | None -> (x,app_sk), cst_l
                      | Some (bef,arg,app_sk') ->
                        let cst_l = Stack.Cst
                            { const = Stack.Cst_const (fst const, u');
                              volatile;
                              curr; remains; params=bef; cst_l;
                            }
                        in
                        whrec Cst_stack.empty (arg,cst_l :: app_sk')
                  in
                  let rec is_case x = match EConstr.kind sigma x with
                    | Lambda (_,_, x) | LetIn (_,_,_, x) | Cast (x, _,_) -> is_case x
                    | App (hd, _) -> is_case hd
                    | Case _ -> true
                    | _ -> false in
                  if equal_stacks env sigma (x, app_sk) (tm', sk')
                  || Stack.will_expose_iota sk'
                  || is_case tm'
                  then fold ()
                  else whrec cst_l' (tm', sk' @ sk)
              | UnfoldWhen { recargs; nargs } -> (* maybe unfolds *)
                begin match recargs with
                  | [] -> (* if nargs has been specified *)
                    (* CAUTION : the constant is NEVER refolded (even when it hides a (co)fix) *)
                    whrec cst_l (body, stack)
                  | curr :: remains -> match Stack.strip_n_app curr stack with
                    | None -> fold ()
                    | Some (bef,arg,s') ->
                      let cst_l = Stack.Cst
                          { const = Stack.Cst_const (fst const, u');
                            volatile = Option.has_some nargs;
                            curr; remains; params=bef; cst_l;
                          }
                      in
                      whrec Cst_stack.empty (arg,cst_l::s')
                end
              end
        end
       | exception NotEvaluableConst (IsPrimitive (u,p)) when Stack.check_native_args p stack ->
          let kargs = CPrimitives.kind p in
          let (kargs,o) = Stack.get_next_primitive_args kargs stack in
          (* Should not fail thanks to [check_native_args] *)
          let (before,a,after) = Option.get o in
          whrec Cst_stack.empty (a,Stack.Primitive(p,const,before,kargs,cst_l)::after)
       | exception NotEvaluableConst (HasRules (u', b, r)) ->
          begin try
            let rhs_stack = apply_rules whrec env sigma u r stack in
            whrec Cst_stack.empty rhs_stack
          with PatternFailure ->
            if not b then fold () else
            match Stack.strip_app stack with
            | args, (Stack.Fix (f,s',cst_l)::s'') when RedFlags.red_set flags RedFlags.fFIX ->
                let x' = Stack.zip sigma (x, args) in
                let out_sk = s' @ (Stack.append_app [|x'|] s'') in
                reduce_and_refold_fix whrec env sigma cst_l f out_sk
            | _ -> fold ()
          end
       | exception NotEvaluableConst _ -> fold ()
      else fold ()
    | Proj (p, r, c) when RedFlags.red_projection flags p ->
      (let npars = Projection.npars p in
       match ReductionBehaviour.get (Projection.constant p) with
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
                         params=bef;
                         cst_l;
                       }
                   in
                   whrec Cst_stack.empty (arg,cst_l::s')
           end)

    | LetIn (_,b,_,c) when RedFlags.red_set flags RedFlags.fZETA ->
      let (cst_l, p) = apply_subst [b] sigma cst_l c stack in
      whrec cst_l p
    | Cast (c,_,_) -> whrec cst_l (c, stack)
    | App (f,cl)  ->
      whrec
        (Cst_stack.add_args cl cst_l)
        (f, Stack.append_app cl stack)
    | Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when RedFlags.red_set flags RedFlags.fBETA ->
        let (cst_l, p) = apply_subst [] sigma cst_l x stack in
        whrec cst_l p
      | _ -> fold ())

    | Case (ci,u,pms,p,iv,d,lf) ->
      whrec Cst_stack.empty (d, Stack.Case ((ci,u,pms,p,iv,lf),cst_l) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> fold ()
      |Some (bef,arg,s') ->
        whrec Cst_stack.empty (arg, Stack.Fix(f,bef,cst_l)::s'))

    | Construct (cstr ,u) ->
      let use_match = RedFlags.red_set flags RedFlags.fMATCH in
      let use_fix = RedFlags.red_set flags RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case(case,_)::s') when use_match ->
          let r = apply_branch env sigma cstr args case in
          whrec Cst_stack.empty (r, s')
        |args, (Stack.Proj (p,_,_)::s') when use_match ->
          whrec Cst_stack.empty (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (f,s',cst_l)::s'') when use_fix ->
          let x' = Stack.zip sigma (x, args) in
          let out_sk = s' @ (Stack.append_app [|x'|] s'') in
          reduce_and_refold_fix whrec env sigma cst_l f out_sk
        |args, (Stack.Cst {const;curr;remains;volatile;params=s';cst_l} :: s'') ->
          let x' = Stack.zip sigma (x, args) in
          begin match remains with
          | [] ->
            (match const with
            | Stack.Cst_const const ->
              (match constant_opt_value_in env const with
              | None -> fold ()
              | Some body ->
                let const = (fst const, EInstance.make (snd const)) in
                let body = EConstr.of_constr body in
                let cst_l = Cst_stack.add_cst ~volatile (mkConstU const) cst_l in
                whrec cst_l (body, s' @ (Stack.append_app [|x'|] s'')))
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

    | CoFix cofix ->
      if RedFlags.red_set flags RedFlags.fCOFIX then
        match Stack.strip_app stack with
        |args, ((Stack.Case _ |Stack.Proj _)::s') ->
          reduce_and_refold_cofix whrec env sigma cst_l cofix stack
        |_ -> fold ()
      else fold ()

    | Int _ | Float _ | String _ | Array _ ->
      begin match Stack.strip_app stack with
       | (_, Stack.Primitive(p,(_,u as kn),rargs,kargs,cst_l')::s) ->
         let more_to_reduce = List.exists (fun k -> CPrimitives.Kwhnf = k) kargs in
         if more_to_reduce then
           let (kargs,o) = Stack.get_next_primitive_args kargs s in
           (* Should not fail because Primitive is put on the stack only if fully applied *)
           let (before,a,after) = Option.get o in
           whrec Cst_stack.empty (a,Stack.Primitive(p,kn,rargs @ Stack.append_app [|x|] before,kargs,cst_l')::after)
         else
           let n = List.length kargs in
           let (args,s) = Stack.strip_app s in
           let (args,extra_args) =
             try List.chop n args
             with List.IndexOutOfRange -> (args,[]) (* FIXME probably useless *)
           in
           let s = extra_args @ s in
           let args = Array.of_list (Option.get (Stack.list_of_app_stack (rargs @ Stack.append_app [|x|] args))) in
             begin match CredNative.red_prim env sigma p u args with
               | Some t -> whrec cst_l' (t,s)
               | None -> ((mkApp (mkConstU kn, args), s), cst_l)
             end
        |args, (Stack.Cst {const;curr;remains;volatile;params=s';cst_l} :: s'') ->
          let x' = Stack.zip sigma (x, args) in
          begin match remains with
          | [] ->
            (match const with
            | Stack.Cst_const const ->
              (match constant_opt_value_in env const with
              | None -> fold ()
              | Some body ->
                let const = (fst const, EInstance.make (snd const)) in
                let body = EConstr.of_constr body in
                let cst_l = Cst_stack.add_cst ~volatile (mkConstU const) cst_l in
                whrec cst_l (body, s' @ (Stack.append_app [|x'|] s'')))
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
                    remains=remains';
                    params=s' @ (Stack.append_app [|x'|] bef);
                    cst_l;
                  }
              in
              whrec Cst_stack.empty (arg, cst_l :: s''')
          end
       | _ -> fold ()
      end

    | Rel _ | Var _ | LetIn _ | Proj _ -> fold ()
    | Sort _ | Ind _ | Prod _ -> fold ()
  in
  fun xs ->
  let (s,cst_l as res) = whrec (Option.default Cst_stack.empty csts) xs in
  (Stack.best_state sigma s cst_l)

let whd_cbn flags env sigma t =
  let state = whd_state_gen flags env sigma (t, Stack.empty) in
  Stack.zip ~refold:true sigma state

let norm_cbn flags env sigma t =
  let push_rel_check_zeta d env =
    let open RedFlags in
    let d = match d with
      | LocalDef (na,c,t) when not (red_set flags fZETA) -> LocalAssum (na,t)
      | d -> d in
    push_rel d env in
  let rec strongrec env t =
    map_constr_with_full_binders env sigma
      push_rel_check_zeta strongrec env (whd_cbn flags env sigma t) in
  strongrec env t
