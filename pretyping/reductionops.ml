(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Constr
open Termops
open Univ
open Evd
open Environ
open EConstr
open Vars
open Context.Rel.Declaration

exception Elimconst

(** This module implements a call by name reduction used by (at
    least) evarconv unification and cbn tactic.

    It has an ability to "refold" constants by storing constants and
    their parameters in its stack.
*)

let () = Goptions.(declare_bool_option {
  optdepr = false;
  optname =
    "Generate weak constraints between Irrelevant universes";
  optkey = ["Cumulativity";"Weak";"Constraints"];
  optread = (fun () -> not !UState.drop_weak_constraints);
  optwrite = (fun a -> UState.drop_weak_constraints:=not a);
})


(** Support for reduction effects *)

open Mod_subst
open Libobject

type effect_name = string

(** create a persistent set to store effect functions *)

(* Table bindings a constant to an effect *)
let constant_effect_table = Summary.ref ~name:"reduction-side-effect" Cmap.empty

(* Table bindings function key to effective functions *)
let effect_table = Summary.ref ~name:"reduction-function-effect" String.Map.empty

(** a test to know whether a constant is actually the effect function *)
let reduction_effect_hook env sigma con c =
  try
    let funkey = Cmap.find con !constant_effect_table in
    let effect = String.Map.find funkey !effect_table in
    effect env sigma (Lazy.force c)
  with Not_found -> ()

let cache_reduction_effect (_,(con,funkey)) =
  constant_effect_table := Cmap.add con funkey !constant_effect_table

let subst_reduction_effect (subst,(con,funkey)) =
  (subst_constant subst con,funkey)

let inReductionEffect : Constant.t * string -> obj =
  declare_object @@ global_object_nodischarge "REDUCTION-EFFECT"
    ~cache:cache_reduction_effect
    ~subst:(Some subst_reduction_effect)

let declare_reduction_effect funkey f =
  if String.Map.mem funkey !effect_table then
    CErrors.anomaly Pp.(str "Cannot redeclare effect function " ++ qstring funkey ++ str ".");
  effect_table := String.Map.add funkey f !effect_table

(** A function to set the value of the print function *)
let set_reduction_effect x funkey =
  Lib.add_anonymous_leaf (inReductionEffect (x,funkey))


(** Machinery to custom the behavior of the reduction *)
module ReductionBehaviour = struct
  open Globnames
  open Names
  open Libobject

  type t = {
    b_nargs: int;
    b_recargs: int list;
    b_dont_expose_case: bool;
  }

  let table =
    Summary.ref (GlobRef.Map.empty : t GlobRef.Map.t) ~name:"reductionbehaviour"

  type flag = [ `ReductionDontExposeCase | `ReductionNeverUnfold ]
  type req =
    | ReqLocal
    | ReqGlobal of GlobRef.t * (int list * int * flag list)

  let load _ (_,(_,(r, b))) =
    table := GlobRef.Map.add r b !table

  let cache o = load 1 o

  let classify = function
    | ReqLocal, _ -> Dispose
    | ReqGlobal _, _ as o -> Substitute o

  let subst (subst, (_, (r,o as orig))) =
    ReqLocal,
    let r' = fst (subst_global subst r) in if r==r' then orig else (r',o)

  let discharge = function
    | _,(ReqGlobal (ConstRef c as gr, req), (_, b)) ->
      let b =
        if Lib.is_in_section gr then
          let vars = Lib.variable_section_segment_of_reference gr in
          let extra = List.length vars in
          let nargs' =
             if b.b_nargs = max_int then max_int
             else if b.b_nargs < 0 then b.b_nargs
             else b.b_nargs + extra in
          let recargs' = List.map ((+) extra) b.b_recargs in
          { b with b_nargs = nargs'; b_recargs = recargs' }
        else b
      in
      Some (ReqGlobal (gr, req), (ConstRef c, b))
    | _ -> None

  let rebuild = function
    | req, (ConstRef c, _ as x) -> req, x
    | _ -> assert false

  let inRedBehaviour = declare_object {
			(default_object "REDUCTIONBEHAVIOUR") with
			load_function = load;
			cache_function = cache;
			classify_function = classify;
			subst_function = subst;
			discharge_function = discharge;
			rebuild_function = rebuild;
		      }

  let set local r (recargs, nargs, flags as req) =
    let nargs = if List.mem `ReductionNeverUnfold flags then max_int else nargs in
    let behaviour = {
      b_nargs = nargs; b_recargs = recargs;
      b_dont_expose_case = List.mem `ReductionDontExposeCase flags } in
    let req = if local then ReqLocal else ReqGlobal (r, req) in
    Lib.add_anonymous_leaf (inRedBehaviour (req, (r, behaviour)))
  ;;

  let get r =
    try
      let b = GlobRef.Map.find r !table in
      let flags =
	if Int.equal b.b_nargs max_int then [`ReductionNeverUnfold]
	else if b.b_dont_expose_case then [`ReductionDontExposeCase] else [] in
      Some (b.b_recargs, (if Int.equal b.b_nargs max_int then -1 else b.b_nargs), flags)
    with Not_found -> None

  let print ref =
    let open Pp in
    let pr_global = Nametab.pr_global_env Id.Set.empty in
    match get ref with
    | None -> mt ()
    | Some (recargs, nargs, flags) ->
       let never = List.mem `ReductionNeverUnfold flags in
       let nomatch = List.mem `ReductionDontExposeCase flags in
       let pp_nomatch = spc() ++ if nomatch then
				   str "but avoid exposing match constructs" else str"" in
       let pp_recargs = spc() ++ str "when the " ++
			  pr_enum (fun x -> pr_nth (x+1)) recargs ++ str (String.plural (List.length recargs) " argument") ++
			  str (String.plural (if List.length recargs >= 2 then 1 else 2) " evaluate") ++
			  str " to a constructor" in
       let pp_nargs =
	 spc() ++ str "when applied to " ++ int nargs ++
	   str (String.plural nargs " argument") in
       hov 2 (str "The reduction tactics " ++
		 match recargs, nargs, never with
		 | _,_, true -> str "never unfold " ++ pr_global ref
		 | [], 0, _ -> str "always unfold " ++ pr_global ref
		 | _::_, n, _ when n < 0 ->
		    str "unfold " ++ pr_global ref ++ pp_recargs ++ pp_nomatch
		 | _::_, n, _ when n > List.fold_left max 0 recargs ->
		    str "unfold " ++ pr_global ref ++ pp_recargs ++
		      str " and" ++ pp_nargs ++ pp_nomatch
		 | _::_, _, _ ->
		    str "unfold " ++ pr_global ref ++ pp_recargs ++ pp_nomatch
		 | [], n, _ when n > 0 ->
		    str "unfold " ++ pr_global ref ++ pp_nargs ++ pp_nomatch
		 | _ -> str "unfold " ++ pr_global ref ++ pp_nomatch )
end

(** Machinery about stack of unfolded constants *)
module Cst_stack = struct
  open EConstr

(** constant * params * args

- constant applied to params = term in head applied to args
- there is at most one arguments with an empty list of args, it must be the first.
- in args, the int represents the indice of the first arg to consider *)
  type t = (constr * constr list * (int * constr array) list)  list

  let empty = []
  let is_empty = CList.is_empty

  let drop_useless = function
    | _ :: ((_,_,[])::_ as q) -> q
    | l -> l

  let add_param h cst_l =
    let append2cst = function
      | (c,params,[]) -> (c, h::params, [])
      | (c,params,((i,t)::q)) when i = pred (Array.length t) ->
	(c, params, q)
      | (c,params,(i,t)::q) ->
	(c, params, (succ i,t)::q)
    in
      drop_useless (List.map append2cst cst_l)

  let add_args cl =
    List.map (fun (a,b,args) -> (a,b,(0,cl)::args))

  let add_cst cst = function
    | (_,_,[]) :: q as l -> l
    | l -> (cst,[],[])::l

  let best_cst = function
    | (cst,params,[])::_ -> Some(cst,params)
    | _ -> None

  let reference sigma t = match best_cst t with
    | Some (c, _) when isConst sigma c -> Some (fst (destConst sigma c))
    | _ -> None

  (** [best_replace d cst_l c] makes the best replacement for [d]
      by [cst_l] in [c] *)
  let best_replace sigma d cst_l c =
    let reconstruct_head = List.fold_left
      (fun t (i,args) -> mkApp (t,Array.sub args i (Array.length args - i))) in
    List.fold_right
      (fun (cst,params,args) t -> Termops.replace_term sigma
	(reconstruct_head d args)
	(applist (cst, List.rev params))
	t) cst_l c

  let pr env sigma l =
    let open Pp in
    let p_c c = Termops.Internal.print_constr_env env sigma c in
    prlist_with_sep pr_semicolon
      (fun (c,params,args) ->
	hov 1 (str"(" ++ p_c c ++ str ")" ++ spc () ++ pr_sequence p_c params ++ spc () ++ str "(args:" ++
		 pr_sequence (fun (i,el) -> prvect_with_sep spc p_c (Array.sub el i (Array.length el - i))) args ++
		 str ")")) l
end


(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack :
sig
  open EConstr
  type 'a app_node
  val pr_app_node : ('a -> Pp.t) -> 'a app_node -> Pp.t

  type cst_member =
    | Cst_const of pconstant
    | Cst_proj of Projection.t

  type 'a member =
  | App of 'a app_node
  | Case of case_info * 'a * 'a array * Cst_stack.t
  | Proj of Projection.t * Cst_stack.t
  | Fix of ('a, 'a) pfixpoint * 'a t * Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * 'a t * CPrimitives.args_red * Cst_stack.t
  | Cst of cst_member * int * int list * 'a t * Cst_stack.t

  and 'a t = 'a member list

  exception IncompatibleFold2

  val pr : ('a -> Pp.t) -> 'a t -> Pp.t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val append_app : 'a array -> 'a t -> 'a t
  val decomp : 'a t -> ('a * 'a t) option
  val decomp_node_last : 'a app_node -> 'a t -> ('a * 'a t)
  val equal : ('a -> 'a -> bool) -> (('a, 'a) pfixpoint -> ('a, 'a) pfixpoint -> bool)
    -> 'a t -> 'a t -> bool
  val compare_shape : 'a t -> 'a t -> bool
  val map : ('a -> 'a) -> 'a t -> 'a t
  val fold2 : ('a -> constr -> constr -> 'a) -> 'a ->
    constr t -> constr t -> 'a
  val append_app_list : 'a list -> 'a t -> 'a t
  val strip_app : 'a t -> 'a t * 'a t
  val strip_n_app : int -> 'a t -> ('a t * 'a * 'a t) option
  val not_purely_applicative : 'a t -> bool
  val will_expose_iota : 'a t -> bool
  val list_of_app_stack : constr t -> constr list option
  val assign : 'a t -> int -> 'a -> 'a t
  val args_size : 'a t -> int
  val tail : int -> 'a t -> 'a t
  val nth : 'a t -> int -> 'a
  val best_state : evar_map -> constr * constr t -> Cst_stack.t -> constr * constr t
  val zip : ?refold:bool -> evar_map -> constr * constr t -> constr
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
    | Cst_proj of Projection.t

  type 'a member =
  | App of 'a app_node
  | Case of case_info * 'a * 'a array * Cst_stack.t
  | Proj of Projection.t * Cst_stack.t
  | Fix of ('a, 'a) pfixpoint * 'a t * Cst_stack.t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * 'a t * CPrimitives.args_red * Cst_stack.t
  | Cst of cst_member * int * int list * 'a t * Cst_stack.t

  and 'a t = 'a member list

  (* Debugging printer *)
  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case (_,_,br,cst) ->
       str "ZCase(" ++
	 prvect_with_sep (pr_bar) pr_c br
       ++ str ")"
    | Proj (p,cst) ->
      str "ZProj(" ++ Constant.debug_print (Projection.constant p) ++ str ")"
    | Fix (f,args,cst) ->
       str "ZFix(" ++ Constr.debug_print_fix pr_c f
       ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Primitive (p,c,args,kargs,cst_l) ->
      str "ZPrimitive(" ++ str (CPrimitives.to_string p)
      ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Cst (mem,curr,remains,params,cst_l) ->
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
        if Univ.Instance.is_empty u then Constant.debug_print c
        else str"(" ++ Constant.debug_print c ++ str ", " ++
	  Univ.Instance.pr Univ.Level.pr u ++ str")"
      | Cst_proj p ->
        str".(" ++ Constant.debug_print (Projection.constant p) ++ str")"

  let empty = []
  let is_empty = CList.is_empty

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

  let equal f f_fix sk1 sk2 =
    let equal_cst_member x y =
      match x, y with
      | Cst_const (c1,u1), Cst_const (c2, u2) ->
        Constant.equal c1 c2 && Univ.Instance.equal u1 u2
      | Cst_proj p1, Cst_proj p2 -> Projection.repr_equal p1 p2
      | _, _ -> false
    in
    let rec equal_rec sk1 sk2 =
      match sk1,sk2 with
      | [],[] -> true
      | App a1 :: s1, App a2 :: s2 ->
        let t1,s1' = decomp_node_last a1 s1 in
        let t2,s2' = decomp_node_last a2 s2 in
        (f t1 t2) && (equal_rec s1' s2')
      | Case (_,t1,a1,_) :: s1, Case (_,t2,a2,_) :: s2 ->
        f t1 t2 && CArray.equal (fun x y -> f x y) a1 a2 && equal_rec s1 s2
      | (Proj (p,_)::s1, Proj(p2,_)::s2) ->
        Projection.Repr.equal (Projection.repr p) (Projection.repr p2)
        && equal_rec s1 s2
      | Fix (f1,s1,_) :: s1', Fix (f2,s2,_) :: s2' ->
        f_fix f1 f2
          && equal_rec (List.rev s1) (List.rev s2)
          && equal_rec s1' s2'
      | Cst (c1,curr1,remains1,params1,_)::s1', Cst (c2,curr2,remains2,params2,_)::s2' ->
        equal_cst_member c1 c2
          && equal_rec (List.rev params1) (List.rev params2)
          && equal_rec s1' s2'
      | ((App _|Case _|Proj _|Fix _|Cst _|Primitive _)::_|[]), _ -> false
    in equal_rec (List.rev sk1) (List.rev sk2)

  let compare_shape stk1 stk2 =
    let rec compare_rec bal stk1 stk2 =
      match (stk1,stk2) with
	([],[]) -> Int.equal bal 0
      | (App (i,_,j)::s1, _) -> compare_rec (bal + j + 1 - i) s1 stk2
      | (_, App (i,_,j)::s2) -> compare_rec (bal - j - 1 + i) stk1 s2
      | (Case(c1,_,_,_)::s1, Case(c2,_,_,_)::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
      | (Proj (p,_)::s1, Proj(p2,_)::s2) ->
	Int.equal bal 0 && compare_rec 0 s1 s2
      | (Fix(_,a1,_)::s1, Fix(_,a2,_)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
      | (Primitive(_,_,a1,_,_)::s1, Primitive(_,_,a2,_,_)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
      | (Cst (_,_,_,p1,_)::s1, Cst (_,_,_,p2,_)::s2) ->
        Int.equal bal 0 && compare_rec 0 p1 p2 && compare_rec 0 s1 s2
      | ((Case _|Proj _|Fix _|Cst _|Primitive _) :: _ | []) ,_ -> false in
    compare_rec 0 stk1 stk2

  exception IncompatibleFold2
  let fold2 f o sk1 sk2 =
    let rec aux o sk1 sk2 =
      match sk1,sk2 with
      | [], [] -> o
      | App n1 :: q1, App n2 :: q2 ->
        let t1,l1 = decomp_node_last n1 q1 in
        let t2,l2 = decomp_node_last n2 q2 in
        aux (f o t1 t2) l1 l2
      | Case (_,t1,a1,_) :: q1, Case (_,t2,a2,_) :: q2 ->
        aux (Array.fold_left2 f (f o t1 t2) a1 a2) q1 q2
      | Proj (p1,_) :: q1, Proj (p2,_) :: q2 ->
        aux o q1 q2
      | Fix ((_,(_,a1,b1)),s1,_) :: q1, Fix ((_,(_,a2,b2)),s2,_) :: q2 ->
        let o' = aux (Array.fold_left2 f (Array.fold_left2 f o b1 b2) a1 a2) (List.rev s1) (List.rev s2) in
        aux o' q1 q2
      | Cst (cst1,_,_,params1,_) :: q1, Cst (cst2,_,_,params2,_) :: q2 ->
        let o' = aux o (List.rev params1) (List.rev params2) in
        aux o' q1 q2
      | (((App _|Case _|Proj _|Fix _|Cst _|Primitive _) :: _|[]), _) ->
              raise IncompatibleFold2
    in aux o (List.rev sk1) (List.rev sk2)

  let rec map f x = List.map (function
                               | (Proj (_,_)) as e -> e
			       | App (i,a,j) ->
				  let le = j - i + 1 in
				  App (0,Array.map f (Array.sub a i le), le-1)
			       | Case (info,ty,br,alt) -> Case (info, f ty, Array.map f br, alt)
			       | Fix ((r,(na,ty,bo)),arg,alt) ->
				  Fix ((r,(na,Array.map f ty, Array.map f bo)),map f arg,alt)
			       | Cst (cst,curr,remains,params,alt) ->
				 Cst (cst,curr,remains,map f params,alt)
                               | Primitive (p,c,args,kargs,cst_l) ->
                                 Primitive(p,c, map f args, kargs, cst_l)
    ) x

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

  let not_purely_applicative args =
    List.exists (function (Fix _ | Case _ | Proj _ | Cst _) -> true
                          | App _ | Primitive _ -> false) args
  let will_expose_iota args =
    List.exists
      (function (Fix (_,_,l) | Case (_,_,_,l) |
                 Proj (_,l) | Cst (_,_,_,_,l)) when Cst_stack.is_empty l -> true | _ -> false)
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

  let assign s p c =
    match strip_n_app p s with
    | Some (pre,_,sk) -> pre @ (App (0,[|c|],0)::sk)
    | None -> assert false

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
      |(cst, params, []) -> (cst, append_app_list (List.rev params) sk)
      |(cst, params, (i,t)::q) -> match decomp sk with
	| Some (el,sk') when EConstr.eq_constr sigma el t.(i) ->
	  if i = pred (Array.length t)
	  then aux sk' def (cst, params, q)
	  else aux sk' def (cst, params, (succ i,t)::q)
	| _ -> def
    in List.fold_left (aux sk) s l

  let constr_of_cst_member f sk =
    match f with
    | Cst_const (c, u) -> mkConstU (c, EInstance.make u), sk
    | Cst_proj p -> 
      match decomp sk with
      | Some (hd, sk) -> mkProj (p, hd), sk
      | None -> assert false

  let zip ?(refold=false) sigma s =
  let rec zip = function
    | f, [] -> f
    | f, (App (i,a,j) :: s) ->
       let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
		then a
		else Array.sub a i (j - i + 1) in
       zip (mkApp (f, a'), s)
    | f, (Case (ci,rt,br,cst_l)::s) when refold ->
      zip (best_state sigma (mkCase (ci,rt,f,br), s) cst_l)
    | f, (Case (ci,rt,br,_)::s) -> zip (mkCase (ci,rt,f,br), s)
    | f, (Fix (fix,st,cst_l)::s) when refold ->
      zip (best_state sigma (mkFix fix, st @ (append_app [|f|] s)) cst_l)
  | f, (Fix (fix,st,_)::s) -> zip
    (mkFix fix, st @ (append_app [|f|] s))
  | f, (Cst (cst,_,_,params,cst_l)::s) when refold ->
    zip (best_state sigma (constr_of_cst_member cst (params @ (append_app [|f|] s))) cst_l)
  | f, (Cst (cst,_,_,params,_)::s) ->
    zip (constr_of_cst_member cst (params @ (append_app [|f|] s)))
  | f, (Proj (p,cst_l)::s) when refold ->
    zip (best_state sigma (mkProj (p,f),s) cst_l)
  | f, (Proj (p,_)::s) -> zip (mkProj (p,f),s)
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
type state = constr * constr Stack.t

type contextual_reduction_function = env -> evar_map -> constr -> constr
type reduction_function = contextual_reduction_function
type local_reduction_function = evar_map -> constr -> constr
type e_reduction_function = env -> evar_map -> constr -> evar_map * constr

type contextual_stack_reduction_function =
    env -> evar_map -> constr -> constr * constr list
type stack_reduction_function = contextual_stack_reduction_function
type local_stack_reduction_function =
    evar_map -> constr -> constr * constr list

type contextual_state_reduction_function =
    env -> evar_map -> state -> state
type state_reduction_function = contextual_state_reduction_function
type local_state_reduction_function = evar_map -> state -> state

let pr_state env sigma (tm,sk) =
  let open Pp in
  let pr c = Termops.Internal.print_constr_env env sigma c in
  h 0 (pr tm ++ str "|" ++ cut () ++ Stack.pr pr sk)

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let safe_evar_value = Evarutil.safe_evar_value

let safe_meta_value sigma ev =
  try Some (Evd.meta_value sigma ev)
  with Not_found -> None

let strong_with_flags whdfun flags env sigma t =
  let push_rel_check_zeta d env =
    let open CClosure.RedFlags in
    let d = match d with
      | LocalDef (na,c,t) when not (red_set flags fZETA) -> LocalAssum (na,t)
      | d -> d in
    push_rel d env in
  let rec strongrec env t =
    map_constr_with_full_binders sigma
      push_rel_check_zeta strongrec env (whdfun flags env sigma t) in
  strongrec env t

let strong whdfun env sigma t =
  let rec strongrec env t =
    map_constr_with_full_binders sigma push_rel strongrec env (whdfun env sigma t) in
  strongrec env t

let local_strong whdfun sigma =
  let rec strongrec t = EConstr.map sigma strongrec (whdfun sigma t) in
  strongrec

let rec strong_prodspine redfun sigma c =
  let x = redfun sigma c in
  match EConstr.kind sigma x with
    | Prod (na,a,b) -> mkProd (na,a,strong_prodspine redfun sigma b)
    | _ -> x

(*************************************)
(*** Reduction using bindingss ***)
(*************************************)

let eta = CClosure.RedFlags.mkflags [CClosure.RedFlags.fETA]

(* Beta Reduction tools *)

let apply_subst recfun env sigma refold cst_l t stack =
  let rec aux env cst_l t stack =
    match (Stack.decomp stack, EConstr.kind sigma t) with
    | Some (h,stacktl), Lambda (_,_,c) ->
       let cst_l' = if refold then Cst_stack.add_param h cst_l else cst_l in
       aux (h::env) cst_l' c stacktl
    | _ -> recfun sigma cst_l (substl env t, stack)
  in aux env cst_l t stack

let stacklam recfun env sigma t stack =
  apply_subst (fun _ _ s -> recfun s) env sigma false Cst_stack.empty t stack

let beta_applist sigma (c,l) =
  let zip s = Stack.zip sigma s in
  stacklam zip [] sigma c (Stack.append_app_list l Stack.empty)

(* Iota reduction tools *)

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)

let reducible_mind_case sigma c = match EConstr.kind sigma c with
  | Construct _ | CoFix _ -> true
  | _  -> false

(** @return c if there is a constant c whose body is bd
    @return bd else.

    It has only a meaning because internal representation of "Fixpoint f x
    := t" is Definition f := fix f x => t

    Even more fragile that we could hope because do Module M. Fixpoint
    f x := t. End M. Definition f := u. and say goodbye to any hope
    of refolding M.f this way ...
*)
let magicaly_constant_of_fixbody env sigma reference bd = function
  | Name.Anonymous -> bd
  | Name.Name id ->
    let open UnivProblem in
    try
      let (cst_mod,_) = Constant.repr2 reference in
      let cst = Constant.make2 cst_mod (Label.of_id id) in
      let (cst, u), ctx = UnivGen.fresh_constant_instance env cst in
      match constant_opt_value_in env (cst,u) with
      | None -> bd
      | Some t ->
        let csts = EConstr.eq_constr_universes env sigma (EConstr.of_constr t) bd in
        begin match csts with
        | Some csts ->
          let subst = Set.fold (fun cst acc ->
              let l, r = match cst with
                | ULub (u, v) | UWeak (u, v) -> u, v
                | UEq (u, v) | ULe (u, v) ->
                  let get u = Option.get (Universe.level u) in
                  get u, get v
              in
            Univ.LMap.add l r acc)
            csts Univ.LMap.empty
          in
          let inst = Instance.subst_fn (fun u -> Univ.LMap.find u subst) u in
          mkConstU (cst, EInstance.make inst)
        | None -> bd
        end
    with
    | Not_found -> bd

let contract_cofix ?env sigma ?reference (bodynum,(names,types,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    if Int.equal bodynum ind then mkCoFix (ind,typedbodies)
    else
      let bd = mkCoFix (ind,typedbodies) in
      match env with
      | None -> bd
      | Some e ->
        match reference with
        | None -> bd
        | Some r -> magicaly_constant_of_fixbody e sigma r bd names.(ind) in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(** Similar to the "fix" case below *)
let reduce_and_refold_cofix recfun env sigma refold cst_l cofix sk =
  let raw_answer =
    let env = if refold then Some env else None in
    contract_cofix ?env sigma ?reference:(Cst_stack.reference sigma cst_l) cofix in
  apply_subst
    (fun sigma x (t,sk') ->
      let t' =
        if refold then Cst_stack.best_replace sigma (mkCoFix cofix) cst_l t else t in
      recfun x (t',sk'))
    [] sigma refold Cst_stack.empty raw_answer sk

let reduce_mind_case sigma mia =
  match EConstr.kind sigma mia.mconstr with
    | Construct ((ind_sp,i),u) ->
(*	let ncargs = (fst mia.mci).(i-1) in*)
	let real_cargs = List.skipn mia.mci.ci_npar mia.mcargs in
        applist (mia.mlf.(i-1),real_cargs)
    | CoFix cofix ->
	let cofix_def = contract_cofix sigma cofix in
	mkCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix ?env sigma ?reference ((recindices,bodynum),(names,types,bodies as typedbodies)) =
    let nbodies = Array.length recindices in
    let make_Fi j =
      let ind = nbodies-j-1 in
      if Int.equal bodynum ind then mkFix ((recindices,ind),typedbodies)
      else
	let bd = mkFix ((recindices,ind),typedbodies) in
	match env with
	| None -> bd
	| Some e ->
          match reference with
          | None -> bd
          | Some r -> magicaly_constant_of_fixbody e sigma r bd names.(ind) in
    let closure = List.init nbodies make_Fi in
    substl closure bodies.(bodynum)

(** First we substitute the Rel bodynum by the fixpoint and then we try to
    replace the fixpoint by the best constant from [cst_l]
    Other rels are directly substituted by constants "magically found from the
    context" in contract_fix *)
let reduce_and_refold_fix recfun env sigma refold cst_l fix sk =
  let raw_answer =
    let env = if refold then Some env else None in
    contract_fix ?env sigma ?reference:(Cst_stack.reference sigma cst_l) fix in
  apply_subst
    (fun sigma x (t,sk') ->
      let t' =
        if refold then
          Cst_stack.best_replace sigma (mkFix fix) cst_l t
        else t
      in recfun x (t',sk'))
    [] sigma refold Cst_stack.empty raw_answer sk

let fix_recarg ((recindices,bodynum),_) stack =
  assert (0 <= bodynum && bodynum < Array.length recindices);
  let recargnum = Array.get recindices bodynum in
  try
    Some (recargnum, Stack.nth stack recargnum)
  with Not_found ->
    None

open Primred

module CNativeEntries =
struct

  type elem = EConstr.t
  type args = EConstr.t array
  type evd = evar_map

  let get = Array.get

  let get_int evd e =
    match EConstr.kind evd e with
    | Int i -> i
    | _ -> raise Primred.NativeDestKO

  let mkInt env i =
    mkInt i

  let mkBool env b =
    let (ct,cf) = get_bool_constructors env in
    mkConstruct (if b then ct else cf)

    let mkCarry env b e =
      let int_ty = mkConst @@ get_int_type env in
      let (c0,c1) = get_carry_constructors env in
      mkApp (mkConstruct (if b then c1 else c0),[|int_ty;e|])

    let mkIntPair env e1 e2 =
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp(mkConstruct c, [|int_ty;int_ty;e1;e2|])

  let mkLt env =
    let (_eq, lt, _gt) = get_cmp_constructors env in
    mkConstruct lt

  let mkEq env =
    let (eq, _lt, _gt) = get_cmp_constructors env in
    mkConstruct eq

  let mkGt env =
    let (_eq, _lt, gt) = get_cmp_constructors env in
    mkConstruct gt

end

module CredNative = RedNative(CNativeEntries)



(** Generic reduction function with environment

    Here is where unfolded constant are stored in order to be
    eventualy refolded.

    If tactic_mode is true, it uses ReductionBehaviour, prefers
    refold constant instead of value and tries to infer constants
    fix and cofix came from.

    It substitutes fix and cofix by the constant they come from in
    contract_* in any case .
*)

let debug_RAKAM = ref (false)
let () = Goptions.(declare_bool_option {
  optdepr = false;
  optname =
    "Print states of the Reductionops abstract machine";
  optkey = ["Debug";"RAKAM"];
  optread = (fun () -> !debug_RAKAM);
  optwrite = (fun a -> debug_RAKAM:=a);
})

let equal_stacks sigma (x, l) (y, l') =
  let f_equal x y = eq_constr sigma x y in
  let eq_fix a b = f_equal (mkFix a) (mkFix b) in
  Stack.equal f_equal eq_fix l l' && f_equal x y

let rec whd_state_gen ?csts ~refold ~tactic_mode flags env sigma =
  let open Context.Named.Declaration in
  let rec whrec cst_l (x, stack) =
    let () = if !debug_RAKAM then
	let open Pp in
        let pr c = Termops.Internal.print_constr_env env sigma c in
	Feedback.msg_notice
             (h 0 (str "<<" ++ pr x ++
                   str "|" ++ cut () ++ Cst_stack.pr env sigma cst_l ++
		   str "|" ++ cut () ++ Stack.pr pr stack ++
		   str ">>"))
    in
    let c0 = EConstr.kind sigma x in
    let fold () =
      let () = if !debug_RAKAM then
	  let open Pp in Feedback.msg_notice (str "<><><><><>") in
      ((EConstr.of_kind c0, stack),cst_l)
    in
    match c0 with
    | Rel n when CClosure.RedFlags.red_set flags CClosure.RedFlags.fDELTA ->
      (match lookup_rel n env with
      | LocalDef (_,body,_) -> whrec Cst_stack.empty (lift n body, stack)
      | _ -> fold ())
    | Var id when CClosure.RedFlags.red_set flags (CClosure.RedFlags.fVAR id) ->
      (match lookup_named id env with
      | LocalDef (_,body,_) ->
	whrec (if refold then Cst_stack.add_cst (mkVar id) cst_l else cst_l) (body, stack)
      | _ -> fold ())
    | Evar ev -> fold ()
    | Meta ev ->
      (match safe_meta_value sigma ev with
      | Some body -> whrec cst_l (body, stack)
      | None -> fold ())
    | Const (c,u as const) ->
      reduction_effect_hook env sigma c
         (lazy (EConstr.to_constr sigma (Stack.zip sigma (x,stack))));
      if CClosure.RedFlags.red_set flags (CClosure.RedFlags.fCONST c) then
       let u' = EInstance.kind sigma u in
       match constant_value_in env (c, u') with
       | body ->
         begin
          let body = EConstr.of_constr body in
          if not tactic_mode
          then whrec (if refold then Cst_stack.add_cst (mkConstU const) cst_l else cst_l)
              (body, stack)
          else (* Looks for ReductionBehaviour *)
            match ReductionBehaviour.get (Globnames.ConstRef c) with
            | None -> whrec (Cst_stack.add_cst (mkConstU const) cst_l) (body, stack)
            | Some (recargs, nargs, flags) ->
              if (List.mem `ReductionNeverUnfold flags
                  || (nargs > 0 && Stack.args_size stack < nargs))
              then fold ()
              else (* maybe unfolds *)
              if List.mem `ReductionDontExposeCase flags then
                let app_sk,sk = Stack.strip_app stack in
                let (tm',sk'),cst_l' =
                  whrec (Cst_stack.add_cst (mkConstU const) cst_l) (body, app_sk)
                in
                let rec is_case x = match EConstr.kind sigma x with
                  | Lambda (_,_, x) | LetIn (_,_,_, x) | Cast (x, _,_) -> is_case x
                  | App (hd, _) -> is_case hd
                  | Case _ -> true
                  | _ -> false in
                if equal_stacks sigma (x, app_sk) (tm', sk')
                || Stack.will_expose_iota sk'
                || is_case tm'
                then fold ()
                else whrec cst_l' (tm', sk' @ sk)
              else match recargs with
                |[] -> (* if nargs has been specified *)
                  (* CAUTION : the constant is NEVER refold
                                          (even when it hides a (co)fix) *)
                  whrec cst_l (body, stack)
                |curr::remains -> match Stack.strip_n_app curr stack with
                              | None -> fold ()
                              | Some (bef,arg,s') ->
                                whrec Cst_stack.empty
                                        (arg,Stack.Cst(Stack.Cst_const (fst const, u'),curr,remains,bef,cst_l)::s')
         end
       | exception NotEvaluableConst (IsPrimitive p) when Stack.check_native_args p stack ->
          let kargs = CPrimitives.kind p in
          let (kargs,o) = Stack.get_next_primitive_args kargs stack in
          (* Should not fail thanks to [check_native_args] *)
          let (before,a,after) = Option.get o in
          whrec Cst_stack.empty (a,Stack.Primitive(p,const,before,kargs,cst_l)::after)
       | exception NotEvaluableConst _ -> fold ()
      else fold ()
    | Proj (p, c) when CClosure.RedFlags.red_projection flags p ->
      (let npars = Projection.npars p in
         if not tactic_mode then
           let stack' = (c, Stack.Proj (p, Cst_stack.empty (*cst_l*)) :: stack) in
	     whrec Cst_stack.empty stack'
         else match ReductionBehaviour.get (Globnames.ConstRef (Projection.constant p)) with
	 | None ->
           let stack' = (c, Stack.Proj (p, cst_l) :: stack) in
	   let stack'', csts = whrec Cst_stack.empty stack' in
	     if equal_stacks sigma stack' stack'' then fold ()
	     else stack'', csts
	 | Some (recargs, nargs, flags) ->
	   if (List.mem `ReductionNeverUnfold flags
	       || (nargs > 0 && Stack.args_size stack < (nargs - (npars + 1))))
	   then fold ()
	   else
	     let recargs = List.map_filter (fun x -> 
	       let idx = x - npars in 
		 if idx < 0 then None else Some idx) recargs
	     in
	       match recargs with
	       |[] -> (* if nargs has been specified *)
		(* CAUTION : the constant is NEVER refold
                   (even when it hides a (co)fix) *)
                 let stack' = (c, Stack.Proj (p, cst_l) :: stack) in
		   whrec Cst_stack.empty(* cst_l *) stack'
	       | curr::remains -> 
		 if curr == 0 then (* Try to reduce the record argument *)
		   whrec Cst_stack.empty 
		     (c, Stack.Cst(Stack.Cst_proj p,curr,remains,Stack.empty,cst_l)::stack)
		 else
		   match Stack.strip_n_app curr stack with
		   | None -> fold ()
		   | Some (bef,arg,s') ->
		     whrec Cst_stack.empty 
		       (arg,Stack.Cst(Stack.Cst_proj p,curr,remains,
				      Stack.append_app [|c|] bef,cst_l)::s'))

    | LetIn (_,b,_,c) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fZETA ->
      apply_subst (fun _ -> whrec) [b] sigma refold cst_l c stack
    | Cast (c,_,_) -> whrec cst_l (c, stack)
    | App (f,cl)  ->
      whrec
	(if refold then Cst_stack.add_args cl cst_l else cst_l)
	(f, Stack.append_app cl stack)
    | Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when CClosure.RedFlags.red_set flags CClosure.RedFlags.fBETA ->
	apply_subst (fun _ -> whrec) [] sigma refold cst_l x stack
      | None when CClosure.RedFlags.red_set flags CClosure.RedFlags.fETA ->
	let env' = push_rel (LocalAssum (na, t)) env in
	let whrec' = whd_state_gen ~refold ~tactic_mode flags env' sigma in
        (match EConstr.kind sigma (Stack.zip ~refold sigma (fst (whrec' (c, Stack.empty)))) with
        | App (f,cl) ->
	  let napp = Array.length cl in
	  if napp > 0 then
	    let (x', l'),_ = whrec' (Array.last cl, Stack.empty) in
            match EConstr.kind sigma x', l' with
            | Rel 1, [] ->
	      let lc = Array.sub cl 0 (napp-1) in
	      let u = if Int.equal napp 1 then f else mkApp (f,lc) in
	      if noccurn sigma 1 u then (pop u,Stack.empty),Cst_stack.empty else fold ()
            | _ -> fold ()
	  else fold ()
	| _ -> fold ())
      | _ -> fold ())

    | Case (ci,p,d,lf) ->
      whrec Cst_stack.empty (d, Stack.Case (ci,p,lf,cst_l) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> fold ()
      |Some (bef,arg,s') ->
	whrec Cst_stack.empty (arg, Stack.Fix(f,bef,cst_l)::s'))

    | Construct ((ind,c),u) ->
      let use_match = CClosure.RedFlags.red_set flags CClosure.RedFlags.fMATCH in
      let use_fix = CClosure.RedFlags.red_set flags CClosure.RedFlags.fFIX in
      if use_match || use_fix then
	match Stack.strip_app stack with
	|args, (Stack.Case(ci, _, lf,_)::s') when use_match ->
	  whrec Cst_stack.empty (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
        |args, (Stack.Proj (p,_)::s') when use_match ->
          whrec Cst_stack.empty (Stack.nth args (Projection.npars p + Projection.arg p), s')
	|args, (Stack.Fix (f,s',cst_l)::s'') when use_fix ->
	  let x' = Stack.zip sigma (x, args) in
	  let out_sk = s' @ (Stack.append_app [|x'|] s'') in
	  reduce_and_refold_fix whrec env sigma refold cst_l f out_sk
	|args, (Stack.Cst (const,curr,remains,s',cst_l) :: s'') ->
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
		whrec (if refold then Cst_stack.add_cst (mkConstU const) cst_l else cst_l)
		  (body, s' @ (Stack.append_app [|x'|] s'')))
	    | Stack.Cst_proj p ->
              let stack = s' @ (Stack.append_app [|x'|] s'') in
		match Stack.strip_n_app 0 stack with
		| None -> assert false
		| Some (_,arg,s'') ->
                  whrec Cst_stack.empty (arg, Stack.Proj (p,cst_l) :: s''))
	  | next :: remains' -> match Stack.strip_n_app (next-curr-1) s'' with
	    | None -> fold ()
	    | Some (bef,arg,s''') ->
	      whrec Cst_stack.empty
		(arg,
		 Stack.Cst (const,next,remains',s' @ (Stack.append_app [|x'|] bef),cst_l) :: s''')
	  end
        |_, (Stack.App _)::_ -> assert false
	|_, _ -> fold ()
      else fold ()

    | CoFix cofix ->
      if CClosure.RedFlags.red_set flags CClosure.RedFlags.fCOFIX then
	match Stack.strip_app stack with
	|args, ((Stack.Case _ |Stack.Proj _)::s') ->
	  reduce_and_refold_cofix whrec env sigma refold cst_l cofix stack
	|_ -> fold ()
      else fold ()

    | Int i ->
      begin match Stack.strip_app stack with
       | (_, Stack.Primitive(p,kn,rargs,kargs,cst_l')::s) ->
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
           let args = Array.of_list (Option.get (Stack.list_of_app_stack (rargs @ Stack.append_app [|x|] args))) in
             begin match CredNative.red_prim env sigma p args with
               | Some t -> whrec cst_l' (t,s)
               | None -> ((mkApp (mkConstU kn, args), s), cst_l)
             end
       | _ -> fold ()
      end

    | Rel _ | Var _ | LetIn _ | Proj _ -> fold ()
    | Sort _ | Ind _ | Prod _ -> fold ()
  in
  fun xs ->
  let (s,cst_l as res) = whrec (Option.default Cst_stack.empty csts) xs in
  if tactic_mode then (Stack.best_state sigma s cst_l,Cst_stack.empty) else res

(** reduction machine without global env and refold machinery *)
let local_whd_state_gen flags sigma =
  let rec whrec (x, stack) =
    let c0 = EConstr.kind sigma x in
    let s = (EConstr.of_kind c0, stack) in
    match c0 with
    | LetIn (_,b,_,c) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fZETA ->
      stacklam whrec [b] sigma c stack
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  -> whrec (f, Stack.append_app cl stack)
    | Lambda (_,_,c) ->
      (match Stack.decomp stack with
      | Some (a,m) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fBETA ->
	stacklam whrec [a] sigma c m
      | None when CClosure.RedFlags.red_set flags CClosure.RedFlags.fETA ->
        (match EConstr.kind sigma (Stack.zip sigma (whrec (c, Stack.empty))) with
        | App (f,cl) ->
	  let napp = Array.length cl in
	  if napp > 0 then
	    let x', l' = whrec (Array.last cl, Stack.empty) in
            match EConstr.kind sigma x', l' with
            | Rel 1, [] ->
	      let lc = Array.sub cl 0 (napp-1) in
	      let u = if Int.equal napp 1 then f else mkApp (f,lc) in
	      if noccurn sigma 1 u then (pop u,Stack.empty) else s
            | _ -> s
	  else s
	| _ -> s)
      | _ -> s)

    | Proj (p,c) when CClosure.RedFlags.red_projection flags p ->
      (whrec (c, Stack.Proj (p, Cst_stack.empty) :: stack))

    | Case (ci,p,d,lf) ->
      whrec (d, Stack.Case (ci,p,lf,Cst_stack.empty) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> s
      |Some (bef,arg,s') -> whrec (arg, Stack.Fix(f,bef,Cst_stack.empty)::s'))

    | Evar ev -> s
    | Meta ev ->
      (match safe_meta_value sigma ev with
        Some c -> whrec (c,stack)
      | None -> s)

    | Construct ((ind,c),u) ->
      let use_match = CClosure.RedFlags.red_set flags CClosure.RedFlags.fMATCH in
      let use_fix = CClosure.RedFlags.red_set flags CClosure.RedFlags.fFIX in
      if use_match || use_fix then
	match Stack.strip_app stack with
	|args, (Stack.Case(ci, _, lf,_)::s') when use_match ->
	  whrec (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
        |args, (Stack.Proj (p,_) :: s') when use_match ->
          whrec (Stack.nth args (Projection.npars p + Projection.arg p), s')
	|args, (Stack.Fix (f,s',cst)::s'') when use_fix ->
	  let x' = Stack.zip sigma (x,args) in
	  whrec (contract_fix sigma f, s' @ (Stack.append_app [|x'|] s''))
        |_, (Stack.App _|Stack.Cst _)::_ -> assert false
	|_, _ -> s
      else s

    | CoFix cofix ->
      if CClosure.RedFlags.red_set flags CClosure.RedFlags.fCOFIX then
	match Stack.strip_app stack with
	|args, ((Stack.Case _ | Stack.Proj _)::s') ->
	  whrec (contract_cofix sigma cofix, stack)
	|_ -> s
      else s

    | Rel _ | Var _ | Sort _ | Prod _ | LetIn _ | Const _  | Ind _ | Proj _
      | Int _ -> s

  in
  whrec

let raw_whd_state_gen flags env =
  let f sigma s = fst (whd_state_gen ~refold:false
                         ~tactic_mode:false
                         flags env sigma s) in
  f

let stack_red_of_state_red f =
  let f sigma x = EConstr.decompose_app sigma (Stack.zip sigma (f sigma (x, Stack.empty))) in
  f

(* Drops the Cst_stack *)
let iterate_whd_gen refold flags env sigma s =
  let rec aux t =
  let (hd,sk),_ = whd_state_gen ~refold ~tactic_mode:false flags env sigma (t,Stack.empty) in
  let whd_sk = Stack.map aux sk in
  Stack.zip sigma ~refold (hd,whd_sk)
  in aux s

let red_of_state_red f sigma x =
  Stack.zip sigma (f sigma (x,Stack.empty))

(* 0. No Reduction Functions *)

let whd_nored_state = local_whd_state_gen CClosure.nored
let whd_nored_stack = stack_red_of_state_red whd_nored_state
let whd_nored = red_of_state_red whd_nored_state

(* 1. Beta Reduction Functions *)

let whd_beta_state = local_whd_state_gen CClosure.beta
let whd_beta_stack = stack_red_of_state_red whd_beta_state
let whd_beta = red_of_state_red whd_beta_state

let whd_betalet_state = local_whd_state_gen CClosure.betazeta
let whd_betalet_stack = stack_red_of_state_red whd_betalet_state
let whd_betalet = red_of_state_red whd_betalet_state

(* 2. Delta Reduction Functions *)

let whd_delta_state e = raw_whd_state_gen CClosure.delta e
let whd_delta_stack env = stack_red_of_state_red (whd_delta_state env)
let whd_delta env = red_of_state_red  (whd_delta_state env)

let whd_betadeltazeta_state e = raw_whd_state_gen CClosure.betadeltazeta e
let whd_betadeltazeta_stack env =
  stack_red_of_state_red (whd_betadeltazeta_state env)
let whd_betadeltazeta env =
  red_of_state_red (whd_betadeltazeta_state env)


(* 3. Iota reduction Functions *)

let whd_betaiota_state = local_whd_state_gen CClosure.betaiota
let whd_betaiota_stack = stack_red_of_state_red whd_betaiota_state
let whd_betaiota = red_of_state_red whd_betaiota_state

let whd_betaiotazeta_state = local_whd_state_gen CClosure.betaiotazeta
let whd_betaiotazeta_stack = stack_red_of_state_red whd_betaiotazeta_state
let whd_betaiotazeta = red_of_state_red whd_betaiotazeta_state

let whd_all_state env = raw_whd_state_gen CClosure.all env
let whd_all_stack env =
  stack_red_of_state_red (whd_all_state env)
let whd_all env =
  red_of_state_red (whd_all_state env)

let whd_allnolet_state env = raw_whd_state_gen CClosure.allnolet env
let whd_allnolet_stack env =
  stack_red_of_state_red (whd_allnolet_state env)
let whd_allnolet env =
  red_of_state_red (whd_allnolet_state env)

(* 4. Ad-hoc eta reduction, does not subsitute evars *)

let shrink_eta c = Stack.zip Evd.empty (local_whd_state_gen eta Evd.empty (c,Stack.empty))

(* 5. Zeta Reduction Functions *)

let whd_zeta_state = local_whd_state_gen CClosure.zeta
let whd_zeta_stack = stack_red_of_state_red whd_zeta_state
let whd_zeta = red_of_state_red whd_zeta_state

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

(* Replacing defined evars for error messages *)
let whd_evar = Evarutil.whd_evar
let nf_evar = Evarutil.nf_evar

(* lazy reduction functions. The infos must be created for each term *)
(* Note by HH [oct 08] : why would it be the job of clos_norm_flags to add
   a [nf_evar] here *)
let clos_norm_flags flgs env sigma t =
  try
    let evars ev = safe_evar_value sigma ev in
    EConstr.of_constr (CClosure.norm_val
      (CClosure.create_clos_infos ~evars flgs env)
      (CClosure.create_tab ())
      (CClosure.inject (EConstr.Unsafe.to_constr t)))
  with e when is_anomaly e -> user_err Pp.(str "Tried to normalize ill-typed term")

let clos_whd_flags flgs env sigma t =
  try
    let evars ev = safe_evar_value sigma ev in
    EConstr.of_constr (CClosure.whd_val
      (CClosure.create_clos_infos ~evars flgs env)
      (CClosure.create_tab ())
      (CClosure.inject (EConstr.Unsafe.to_constr t)))
  with e when is_anomaly e -> user_err Pp.(str "Tried to normalize ill-typed term")

let nf_beta = clos_norm_flags CClosure.beta
let nf_betaiota = clos_norm_flags CClosure.betaiota
let nf_betaiotazeta = clos_norm_flags CClosure.betaiotazeta
let nf_zeta = clos_norm_flags CClosure.zeta
let nf_all env sigma =
  clos_norm_flags CClosure.all env sigma


(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)
(*
let fkey = CProfile.declare_profile "fhnf";;
let fhnf info v = CProfile.profile2 fkey fhnf info v;;

let fakey = CProfile.declare_profile "fhnf_apply";;
let fhnf_apply info k h a = CProfile.profile4 fakey fhnf_apply info k h a;;
*)

let is_transparent e k =
  match Conv_oracle.get_strategy (Environ.oracle e) k with
  | Conv_oracle.Opaque -> false
  | _ -> true

(* Conversion utility functions *)

type conversion_test = Constraint.t -> Constraint.t

let pb_is_equal pb = pb == Reduction.CONV

let pb_equal = function
  | Reduction.CUMUL -> Reduction.CONV
  | Reduction.CONV -> Reduction.CONV

let report_anomaly e =
  let msg = Pp.(str "Conversion test raised an anomaly:" ++
                spc () ++ CErrors.print e) in
  let e = UserError (None,msg) in
  let e = CErrors.push e in
  iraise e

let f_conv ?l2r ?reds env ?evars x y =
  let inj = EConstr.Unsafe.to_constr in
  Reduction.conv ?l2r ?reds env ?evars (inj x) (inj y)

let f_conv_leq ?l2r ?reds env ?evars x y =
  let inj = EConstr.Unsafe.to_constr in
  Reduction.conv_leq ?l2r ?reds env ?evars (inj x) (inj y)

let test_trans_conversion (f: constr Reduction.extended_conversion_function) reds env sigma x y =
  try
    let evars ev = safe_evar_value sigma ev in
    let _ = f ~reds env ~evars:(evars, Evd.universes sigma) x y in
    true
  with Reduction.NotConvertible -> false
    | e when is_anomaly e -> report_anomaly e

let is_conv ?(reds=TransparentState.full) env sigma = test_trans_conversion f_conv reds env sigma
let is_conv_leq ?(reds=TransparentState.full) env sigma = test_trans_conversion f_conv_leq reds env sigma
let is_fconv ?(reds=TransparentState.full) = function
  | Reduction.CONV -> is_conv ~reds
  | Reduction.CUMUL -> is_conv_leq ~reds

let check_conv ?(pb=Reduction.CUMUL) ?(ts=TransparentState.full) env sigma x y =
  let f = match pb with
    | Reduction.CONV -> f_conv
    | Reduction.CUMUL -> f_conv_leq
  in
    try f ~reds:ts env ~evars:(safe_evar_value sigma, Evd.universes sigma) x y; true
    with Reduction.NotConvertible -> false
    | Univ.UniverseInconsistency _ -> false
    | e when is_anomaly e -> report_anomaly e

let sigma_compare_sorts env pb s0 s1 sigma =
  match pb with
  | Reduction.CONV -> Evd.set_eq_sort env sigma s0 s1
  | Reduction.CUMUL -> Evd.set_leq_sort env sigma s0 s1

let sigma_compare_instances ~flex i0 i1 sigma =
  try Evd.set_eq_instances ~flex sigma i0 i1
  with Evd.UniversesDiffer
     | Univ.UniverseInconsistency _ ->
	raise Reduction.NotConvertible

let sigma_check_inductive_instances cv_pb variance u1 u2 sigma =
  match Evarutil.compare_cumulative_instances cv_pb variance u1 u2 sigma with
  | Inl sigma -> sigma
  | Inr _ ->
    raise Reduction.NotConvertible

let sigma_univ_state = 
  let open Reduction in
  { compare_sorts = sigma_compare_sorts;
    compare_instances = sigma_compare_instances;
    compare_cumul_instances = sigma_check_inductive_instances; }

let infer_conv_gen conv_fun ?(catch_incon=true) ?(pb=Reduction.CUMUL)
    ?(ts=TransparentState.full) env sigma x y =
  (* FIXME *)
  try
      let ans = match pb with
      | Reduction.CUMUL ->
          EConstr.leq_constr_universes env sigma x y
      | Reduction.CONV ->
          EConstr.eq_constr_universes env sigma x y
      in
      let ans = match ans with
      | None -> None
      | Some cstr ->
        try Some (Evd.add_universe_constraints sigma cstr)
        with Univ.UniverseInconsistency _ | Evd.UniversesDiffer -> None
      in
      match ans with
      | Some sigma -> ans
      | None ->
        let x = EConstr.Unsafe.to_constr x in
        let y = EConstr.Unsafe.to_constr y in
	let sigma' = 
	  conv_fun pb ~l2r:false sigma ts
	    env (sigma, sigma_univ_state) x y in
        Some sigma'
  with
  | Reduction.NotConvertible -> None
  | Univ.UniverseInconsistency _ when catch_incon -> None
  | e when is_anomaly e -> report_anomaly e

let infer_conv = infer_conv_gen (fun pb ~l2r sigma ->
      Reduction.generic_conv pb ~l2r (safe_evar_value sigma))

(* This reference avoids always having to link C code with the kernel *)
let vm_infer_conv = ref (infer_conv ~catch_incon:true ~ts:TransparentState.full)
let set_vm_infer_conv f = vm_infer_conv := f
let vm_infer_conv ?(pb=Reduction.CUMUL) env t1 t2 =
  !vm_infer_conv ~pb env t1 t2

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let whd_meta sigma c = match EConstr.kind sigma c with
  | Meta p -> (try meta_value sigma p with Not_found -> c)
  | _ -> c

let default_plain_instance_ident = Id.of_string "H"

(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance sigma s c =
  let rec irec n u = match EConstr.kind sigma u with
    | Meta p -> (try lift n (Metamap.find p s) with Not_found -> u)
    | App (f,l) when isCast sigma f ->
        let (f,_,t) = destCast sigma f in
        let l' = Array.Fun1.Smart.map irec n l in
        (match EConstr.kind sigma f with
        | Meta p ->
	    (* Don't flatten application nodes: this is used to extract a
               proof-term from a proof-tree and we want to keep the structure
               of the proof-tree *)
	    (try let g = Metamap.find p s in
	    match EConstr.kind sigma g with
            | App _ ->
                let l' = Array.Fun1.Smart.map lift 1 l' in
                mkLetIn (Name default_plain_instance_ident,g,t,mkApp(mkRel 1, l'))
            | _ -> mkApp (g,l')
	    with Not_found -> mkApp (f,l'))
        | _ -> mkApp (irec n f,l'))
    | Cast (m,_,_) when isMeta sigma m ->
	(try lift n (Metamap.find (destMeta sigma m) s) with Not_found -> u)
    | _ ->
	map_with_binders sigma succ irec n u
  in
  if Metamap.is_empty s then c
  else irec 0 c

(* [instance] is used for [res_pf]; the call to [local_strong whd_betaiota]
   has (unfortunately) different subtle side effects:

   - ** Order of subgoals **
     If the lemma is a case analysis with parameters, it will move the
     parameters as first subgoals (e.g. "case H" applied on
     "H:D->A/\B|-C" will present the subgoal |-D first while w/o
     betaiota the subgoal |-D would have come last).

   - ** Betaiota-contraction in statement **
     If the lemma has a parameter which is a function and this
     function is applied in the lemma, then the _strong_ betaiota will
     contract the application of the function to its argument (e.g.
     "apply (H (fun x => x))" in "H:forall f, f 0 = 0 |- 0=0" will
     result in applying the lemma 0=0 in which "(fun x => x) 0" has
     been contracted). A goal to rewrite may then fail or succeed
     differently.

   - ** Naming of hypotheses **
     If a lemma is a function of the form "fun H:(forall a:A, P a)
     => .. F H .." where the expected type of H is "forall b:A, P b",
     then, without reduction, the application of the lemma will
     generate a subgoal "forall a:A, P a" (and intro will use name
     "a"), while with reduction, it will generate a subgoal "forall
     b:A, P b" (and intro will use name "b").

   - ** First-order pattern-matching **
     If a lemma has the type "(fun x => p) t" then rewriting t may fail
     if the type of the lemma is first beta-reduced (this typically happens
     when rewriting a single variable and the type of the lemma is obtained
     by meta_instance (with empty map) which itself calls instance with this
     empty map).
 *)

let instance sigma s c =
  (* if s = [] then c else *)
  local_strong whd_betaiota sigma (plain_instance sigma s c)

(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env sigma t n =
  match EConstr.kind sigma (whd_all env sigma t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly ~label:"hnf_prod_app" (Pp.str "Need a product.")

let hnf_prod_appvect env sigma t nl =
  Array.fold_left (fun acc t -> hnf_prod_app env sigma acc t) t nl

let hnf_prod_applist env sigma t nl =
  List.fold_left (fun acc t -> hnf_prod_app env sigma acc t) t nl

let hnf_lam_app env sigma t n =
  match EConstr.kind sigma (whd_all env sigma t) with
    | Lambda (_,_,b) -> subst1 n b
    | _ -> anomaly ~label:"hnf_lam_app" (Pp.str "Need an abstraction.")

let hnf_lam_appvect env sigma t nl =
  Array.fold_left (fun acc t -> hnf_lam_app env sigma acc t) t nl

let hnf_lam_applist env sigma t nl =
  List.fold_left (fun acc t -> hnf_lam_app env sigma acc t) t nl

let splay_prod env sigma =
  let rec decrec env m c =
    let t = whd_all env sigma c in
    match EConstr.kind sigma t with
      | Prod (n,a,c0) ->
         decrec (push_rel (LocalAssum (n,a)) env) ((n,a)::m) c0
      | _ -> m,t
  in
  decrec env []

let splay_lam env sigma =
  let rec decrec env m c =
    let t = whd_all env sigma c in
    match EConstr.kind sigma t with
      | Lambda (n,a,c0) ->
         decrec (push_rel (LocalAssum (n,a)) env) ((n,a)::m) c0
      | _ -> m,t
  in
  decrec env []

let splay_prod_assum env sigma =
  let rec prodec_rec env l c =
    let t = whd_allnolet env sigma c in
    match EConstr.kind sigma t with
    | Prod (x,t,c)  ->
	prodec_rec (push_rel (LocalAssum (x,t)) env)
	  (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) ->
	prodec_rec (push_rel (LocalDef (x,b,t)) env)
	  (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> prodec_rec env l c
    | _               -> 
      let t' = whd_all env sigma t in
	if EConstr.eq_constr sigma t t' then l,t
	else prodec_rec env l t'
  in
  prodec_rec env Context.Rel.empty

let splay_arity env sigma c =
  let l, c = splay_prod env sigma c in
  match EConstr.kind sigma c with
    | Sort s -> l,s
    | _ -> invalid_arg "splay_arity"

let sort_of_arity env sigma c = snd (splay_arity env sigma c)

let splay_prod_n env sigma n =
  let rec decrec env m ln c = if Int.equal m 0 then (ln,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Prod (n,a,c0) ->
	  decrec (push_rel (LocalAssum (n,a)) env)
	    (m-1) (Context.Rel.add (LocalAssum (n,a)) ln) c0
      | _                      -> invalid_arg "splay_prod_n"
  in
  decrec env n Context.Rel.empty

let splay_lam_n env sigma n =
  let rec decrec env m ln c = if Int.equal m 0 then (ln,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Lambda (n,a,c0) ->
	  decrec (push_rel (LocalAssum (n,a)) env)
	    (m-1) (Context.Rel.add (LocalAssum (n,a)) ln) c0
      | _                      -> invalid_arg "splay_lam_n"
  in
  decrec env n Context.Rel.empty

let is_sort env sigma t =
  match EConstr.kind sigma (whd_all env sigma t) with
  | Sort s -> true
  | _ -> false

(* reduction to head-normal-form allowing delta/zeta only in argument
   of case/fix (heuristic used by evar_conv) *)

let whd_betaiota_deltazeta_for_iota_state ts env sigma csts s =
  let refold = false in
  let tactic_mode = false in
  let rec whrec csts s =
    let (t, stack as s),csts' = whd_state_gen ~csts ~refold ~tactic_mode CClosure.betaiota env sigma s in
    match Stack.strip_app stack with
      |args, (Stack.Case _ :: _ as stack') ->
	let (t_o,stack_o),csts_o = whd_state_gen ~csts:csts' ~refold ~tactic_mode
	  (CClosure.RedFlags.red_add_transparent CClosure.all ts) env sigma (t,args) in
	if reducible_mind_case sigma t_o then whrec csts_o (t_o, stack_o@stack') else s,csts'
      |args, (Stack.Fix _ :: _ as stack') ->
	let (t_o,stack_o),csts_o = whd_state_gen ~csts:csts' ~refold ~tactic_mode
	  (CClosure.RedFlags.red_add_transparent CClosure.all ts) env sigma (t,args) in
	if isConstruct sigma t_o then whrec csts_o (t_o, stack_o@stack') else s,csts'
      |args, (Stack.Proj (p,_) :: stack'') ->
	let (t_o,stack_o),csts_o = whd_state_gen ~csts:csts' ~refold ~tactic_mode
	  (CClosure.RedFlags.red_add_transparent CClosure.all ts) env sigma (t,args) in
	if isConstruct sigma t_o then
          whrec Cst_stack.empty (Stack.nth stack_o (Projection.npars p + Projection.arg p), stack'')
	else s,csts'
      |_, ((Stack.App _|Stack.Cst _|Stack.Primitive _) :: _|[]) -> s,csts'
  in whrec csts s

let find_conclusion env sigma =
  let rec decrec env c =
    let t = whd_all env sigma c in
    match EConstr.kind sigma t with
      | Prod (x,t,c0) -> decrec (push_rel (LocalAssum (x,t)) env) c0
      | Lambda (x,t,c0) -> decrec (push_rel (LocalAssum (x,t)) env) c0
      | t -> t
  in
  decrec env

let is_arity env sigma c =
  match find_conclusion env sigma c with
    | Sort _ -> true
    | _ -> false

(*************************************)
(* Metas *)

let meta_value evd mv =
  let rec valrec mv =
    match meta_opt_fvalue evd mv with
    | Some (b,_) ->
      let metas = Metamap.bind valrec b.freemetas in
      instance evd metas b.rebus
    | None -> mkMeta mv
  in
  valrec mv

let meta_instance sigma b =
  let fm = b.freemetas in
  if Metaset.is_empty fm then b.rebus
  else
    let c_sigma = Metamap.bind (fun mv -> meta_value sigma mv) fm in
    instance sigma c_sigma b.rebus

let nf_meta sigma c =
  let cl = mk_freelisted c in
  meta_instance sigma { cl with rebus = cl.rebus }

(* Instantiate metas that create beta/iota redexes *)

let meta_reducible_instance evd b =
  let fm = b.freemetas in
  let fold mv accu =
    let fvalue = try meta_opt_fvalue evd mv with Not_found -> None in
    match fvalue with
    | None -> accu
    | Some (g, (_, s)) -> Metamap.add mv (g.rebus, s) accu
  in
  let metas = Metaset.fold fold fm Metamap.empty in
  let rec irec u =
    let u = whd_betaiota Evd.empty u (* FIXME *) in
    match EConstr.kind evd u with
    | Case (ci,p,c,bl) when EConstr.isMeta evd (strip_outer_cast evd c) ->
	let m = destMeta evd (strip_outer_cast evd c) in
	(match
	  try
	    let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
	    if isConstruct evd g || not is_coerce then Some g else None
	  with Not_found -> None
	  with
	    | Some g -> irec (mkCase (ci,p,g,bl))
	    | None -> mkCase (ci,irec p,c,Array.map irec bl))
    | App (f,l) when EConstr.isMeta evd (strip_outer_cast evd f) ->
	let m = destMeta evd (strip_outer_cast evd f) in
	(match
	  try
	    let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
	    if isLambda evd g || not is_coerce then Some g else None
	  with Not_found -> None
	 with
	   | Some g -> irec (mkApp (g,l))
	   | None -> mkApp (f,Array.map irec l))
    | Meta m ->
	(try let g, s = Metamap.find m metas in
          let is_coerce = match s with CoerceToType -> true | _ -> false in
          if not is_coerce then irec g else u
	 with Not_found -> u)
    | Proj (p,c) when isMeta evd c || isCast evd c && isMeta evd (pi1 (destCast evd c)) (* What if two nested casts? *) ->
      let m = try destMeta evd c with _ -> destMeta evd (pi1 (destCast evd c)) (* idem *) in
	  (match
	  try
	    let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
	    if isConstruct evd g || not is_coerce then Some g else None
	  with Not_found -> None
	  with
	    | Some g -> irec (mkProj (p,g))
	    | None -> mkProj (p,c))
    | _ -> EConstr.map evd irec u
  in
  if Metaset.is_empty fm then (* nf_betaiota? *) b.rebus
  else irec b.rebus

let betazetaevar_applist sigma n c l =
  let rec stacklam n env t stack =
    if Int.equal n 0 then applist (substl env t, stack) else
    match EConstr.kind sigma t, stack with
    | Lambda(_,_,c), arg::stacktl -> stacklam (n-1) (arg::env) c stacktl
    | LetIn(_,b,_,c), _ -> stacklam (n-1) (substl env b::env) c stack
    | Evar _, _ -> applist (substl env t, stack)
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  stacklam n [] c l
