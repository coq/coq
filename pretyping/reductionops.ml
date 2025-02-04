(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
    least) evarconv unification. *)

(** Support for reduction effects *)

open Mod_subst
open Libobject

type effect_name = string

(** create a persistent set to store effect functions *)

(* Table bindings a constant to an effect *)
let constant_effect_table = Summary.ref ~name:"reduction-side-effect" Cmap.empty

(* Table bindings function key to effective functions *)
let effect_table = ref String.Map.empty

(** a test to know whether a constant is actually the effect function *)
let reduction_effect_hook env sigma con c =
  try
    let funkey = Cmap.find con !constant_effect_table in
    let effect_function = String.Map.find funkey !effect_table in
    effect_function env sigma (Lazy.force c)
  with Not_found -> ()

let cache_reduction_effect (con,funkey) =
  constant_effect_table := Cmap.add con funkey !constant_effect_table

let subst_reduction_effect (subst,(con,funkey)) =
  (subst_constant subst con,funkey)

let inReductionEffect : Libobject.locality * (Constant.t * string) -> obj =
  declare_object @@ object_with_locality "REDUCTION-EFFECT"
    ~cache:cache_reduction_effect
    ~subst:(Some subst_reduction_effect)
    ~discharge:(fun x -> x)

let declare_reduction_effect funkey f =
  if String.Map.mem funkey !effect_table then
    CErrors.anomaly Pp.(str "Cannot redeclare effect function " ++ qstring funkey ++ str ".");
  effect_table := String.Map.add funkey f !effect_table

(** A function to set the value of the print function *)
let set_reduction_effect local x funkey =
  Lib.add_leaf (inReductionEffect (local,(x,funkey)))


(** Machinery to custom the behavior of the reduction *)
module ReductionBehaviour = struct
  open Names
  open Libobject

  type t = NeverUnfold | UnfoldWhen of when_flags | UnfoldWhenNoMatch of when_flags
  and when_flags = { recargs : int list ; nargs : int option }

  let more_args_when k { recargs; nargs } =
    { nargs = Option.map ((+) k) nargs;
      recargs = List.map ((+) k) recargs;
    }

  let more_args k = function
    | NeverUnfold -> NeverUnfold
    | UnfoldWhen x -> UnfoldWhen (more_args_when k x)
    | UnfoldWhenNoMatch x -> UnfoldWhenNoMatch (more_args_when k x)

  type table = Cpred.t * t Cmap.t

(* We need to have a fast way to know the set of all constants that
  have the NeverUnfold flag.  Therefore, the table has a distinct subpart
  that is this set. *)
  let table =
    Summary.ref ((Cpred.empty, Cmap.empty)) ~name:"reductionbehaviour"

  let load _ (_,(r, b)) =
    table := (match b with
                | None -> Cpred.remove r (fst !table), Cmap.remove r (snd !table)
                | Some NeverUnfold -> Cpred.add r (fst !table), Cmap.remove r (snd !table)
                | Some b -> Cpred.remove r (fst !table), Cmap.add r b (snd !table))

  let cache o = load 1 o

  let classify (local,_) = if local then Dispose else Substitute

  let subst (subst, (local, (r,o) as orig)) =
    let r' = subst_constant subst r in if r==r' then orig
    else (local,(r',o))

  let discharge = function
    | false, (gr, b) ->
      let b =
        let gr = GlobRef.ConstRef gr in
        if Lib.is_in_section gr then
          let vars = Lib.section_instance gr in
          let extra = Array.length vars in
          Option.map (more_args extra) b
        else b
      in
      Some (false, (gr, b))
    | true, _ -> None

  let inRedBehaviour = declare_object {
      (default_object "REDUCTIONBEHAVIOUR") with
      load_function = load;
      cache_function = cache;
      classify_function = classify;
      subst_function = subst;
      discharge_function = discharge;
    }

  let set ~local r b =
    Lib.add_leaf (inRedBehaviour (local, (r, b)))

  let get_from_db table r =
    if Cpred.mem r (fst table) then
      Some NeverUnfold
    else
      Cmap.find_opt r (snd table)

  let print_from_db table ref =
    let open Pp in
    let pr_global c = Nametab.pr_global_env Id.Set.empty (ConstRef c) in
    match get_from_db table ref with
    | None -> mt ()
    | Some b ->
       let pp_nomatch = spc () ++ str "but avoid exposing match constructs" in
       let pp_recargs recargs = spc() ++ str "when the " ++
                          pr_enum (fun x -> pr_nth (x+1)) recargs ++ str (String.plural (List.length recargs) " argument") ++
                          str (String.plural (if List.length recargs >= 2 then 1 else 2) " evaluate") ++
                          str " to a constructor" in
       let pp_nargs nargs =
         spc() ++ str "when applied to " ++ int nargs ++
         str (String.plural nargs " argument") in
       let pp_when = function
         | { recargs = []; nargs = Some 0 } ->
           str "always unfold " ++ pr_global ref
         | { recargs = []; nargs = Some n } ->
           str "unfold " ++ pr_global ref ++ pp_nargs n
         | { recargs = []; nargs = None } ->
           str "unfold " ++ pr_global ref
         | { recargs; nargs = Some n } when n > List.fold_left max 0 recargs ->
           str "unfold " ++ pr_global ref ++ pp_recargs recargs ++
           str " and" ++ pp_nargs n
         | { recargs; nargs = _ } ->
           str "unfold " ++ pr_global ref ++ pp_recargs recargs
       in
       let pp_behavior = function
         | NeverUnfold -> str "never unfold " ++ pr_global ref
         | UnfoldWhen x -> pp_when x
         | UnfoldWhenNoMatch x -> pp_when x ++ pp_nomatch
       in
       hov 2 (str "The reduction tactics " ++ pp_behavior b)

  module Db = struct
    type t = table
    let get () = !table
    let empty = (Cpred.empty, Cmap.empty)
    let print = print_from_db
    let all_never_unfold table = fst table
  end

  let get r = get_from_db (Db.get ()) r

  let print c = print_from_db (Db.get ()) c

end

(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack :
sig
  open EConstr
  type app_node
  val pr_app_node : (EConstr.t -> Pp.t) -> app_node -> Pp.t

  type case_stk = case_info * EInstance.t * EConstr.t array * EConstr.case_return * EConstr.t pcase_invert * EConstr.case_branch array

  val mkCaseStk : case_info * EInstance.t * EConstr.t array * EConstr.case_return * EConstr.t pcase_invert * EConstr.case_branch array -> case_stk

  type member =
  | App of app_node
  | Case of case_stk
  | Proj of Projection.t * ERelevance.t
  | Fix of fixpoint * t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * t * CPrimitives.args_red

  and t = member list

  exception IncompatibleFold2

  val pr : (EConstr.t -> Pp.t) -> t -> Pp.t
  val empty : t
  val is_empty : t -> bool
  val append_app : EConstr.t array -> t -> t
  val decomp : t -> (EConstr.t * t) option
  val decomp_rev : t -> (EConstr.t * t) option
  val compare_shape : t -> t -> bool
  val fold2 : ('a -> constr -> constr -> 'a) -> 'a -> t -> t -> 'a
  val append_app_list : EConstr.t list -> t -> t
  val strip_app : t -> t * t
  val strip_n_app : int -> t -> (t * EConstr.t * t) option
  val not_purely_applicative : t -> bool
  val list_of_app_stack : t -> constr list option
  val args_size : t -> int
  val tail : int -> t -> t
  val nth : t -> int -> EConstr.t
  val zip : evar_map -> constr * t -> constr
  val check_native_args : CPrimitives.t -> t -> bool
  val get_next_primitive_args : CPrimitives.args_red -> t -> CPrimitives.args_red * (t * EConstr.t * t) option
  val expand_case : env -> evar_map -> case_stk -> case_info * EInstance.t * constr array * ((rel_context * constr) * ERelevance.t) * (rel_context * constr) array
end =
struct
  open EConstr
  type app_node = int * EConstr.t array * int
  (* first relevant position, arguments, last relevant position *)

  (*
     Invariant that this module must ensure:
     (beware of direct access to app_node by the rest of Reductionops)
     - in app_node (i,_,j) i <= j
     - There is no array reallocation (outside of debug printing)
   *)

  let pr_app_node pr (i,a,j) =
    let open Pp in surround (
                     prvect_with_sep pr_comma pr (Array.sub a i (j - i + 1))
                     )


  type case_stk =
    case_info * EInstance.t * EConstr.t array * EConstr.case_return * EConstr.t pcase_invert * EConstr.case_branch array

  let mkCaseStk x = x

  type member =
  | App of app_node
  | Case of case_stk
  | Proj of Projection.t * ERelevance.t
  | Fix of fixpoint * t
  | Primitive of CPrimitives.t * (Constant.t * EInstance.t) * t * CPrimitives.args_red

  and t = member list

  (* Debugging printer *)
  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case (_,_,_,_,_,br) ->
       str "ZCase(" ++
         prvect_with_sep (pr_bar) (fun (_, c) -> pr_c c) br
       ++ str ")"
    | Proj (p,_)  ->
      str "ZProj(" ++ Projection.debug_print p ++ str ")"
    | Fix (f,args) ->
       str "ZFix(" ++ Constr.debug_print_fix pr_c f
       ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Primitive (p,c,args,kargs) ->
      str "ZPrimitive(" ++ str (CPrimitives.to_string p)
      ++ pr_comma () ++ pr pr_c args ++ str ")"
  and pr pr_c l =
    let open Pp in
    prlist_with_sep pr_semicolon (fun x -> hov 1 (pr_member pr_c x)) l

  let empty = []
  let is_empty = CList.is_empty

  let append_app v s =
    let le = Array.length v in
    if Int.equal le 0 then s else App (0,v,pred le) :: s

  let decomp_rev = function
    | App (i,l,j) :: sk ->
      if i < j then Some (l.(j), App (i,l,pred j) :: sk)
      else Some (l.(j), sk)
    | _ -> None

  let decomp_node_last (i,l,j) sk =
    if i < j then (l.(j), App (i,l,pred j) :: sk)
    else (l.(j), sk)

  let compare_shape stk1 stk2 =
    let rec compare_rec bal stk1 stk2 =
      match (stk1,stk2) with
        ([],[]) -> Int.equal bal 0
      | (App (i,_,j)::s1, _) -> compare_rec (bal + j + 1 - i) s1 stk2
      | (_, App (i,_,j)::s2) -> compare_rec (bal - j - 1 + i) stk1 s2
      | (Case _ :: s1, Case _::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
      | (Proj (p,_)::s1, Proj(p2,_)::s2) ->
        Int.equal bal 0 && compare_rec 0 s1 s2
      | (Fix(_,a1)::s1, Fix(_,a2)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
      | (Primitive(_,_,a1,_)::s1, Primitive(_,_,a2,_)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
      | ((Case _ | Proj _ | Fix _ | Primitive _) :: _ | []) ,_ -> false in
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
      | Case ((_,_,pms1,((_, t1),_),_,a1)) :: q1, Case ((_,_,pms2, ((_, t2),_),_,a2)) :: q2 ->
        let f' o (_, t1) (_, t2) = f o t1 t2 in
        aux (Array.fold_left2 f' (f (Array.fold_left2 f o pms1 pms2) t1 t2) a1 a2) q1 q2
      | Proj (p1,_) :: q1, Proj (p2,_) :: q2 ->
        aux o q1 q2
      | Fix ((_,(_,a1,b1)),s1) :: q1, Fix ((_,(_,a2,b2)),s2) :: q2 ->
        let o' = aux (Array.fold_left2 f (Array.fold_left2 f o b1 b2) a1 a2) (List.rev s1) (List.rev s2) in
        aux o' q1 q2
      | (((App _|Case _|Proj _|Fix _|Primitive _) :: _|[]), _) ->
              raise IncompatibleFold2
    in aux o (List.rev sk1) (List.rev sk2)

  let append_app_list l s =
    let a = Array.of_list l in
    append_app a s

  let rec args_size = function
    | App (i,_,j) :: s -> j + 1 - i + args_size s
    | (Case _ | Fix _ | Proj _ | Primitive _) :: _ | [] -> 0

  let strip_app s =
    let rec aux out = function
      | ( App _ as e) :: s -> aux (e :: out) s
      | s -> List.rev out,s
    in aux [] s

  let strip_n_app n s =
    let rec aux n out = function
      | App (i,a,j) as e :: s ->
         let nb = j - i + 1 in
         if n >= nb then
           aux (n - nb) (e :: out) s
         else
           let p = i + n in
           Some (CList.rev
              (if Int.equal n 0 then out else App (i,a,p-1) :: out),
            a.(p),
            if j > p then App (succ p,a,j) :: s else s)
      | s -> None
    in aux n [] s

  let decomp s =
    match strip_n_app 0 s with
    | Some (_,a,s) -> Some (a,s)
    | None -> None

  let not_purely_applicative args =
    List.exists (function (Fix _ | Case _ | Proj _ ) -> true
                          | App _ | Primitive _ -> false) args

  let list_of_app_stack s =
    let rec aux = function
      | App (i,a,j) :: s ->
        let (args',s') = aux s in
        let a' = Array.sub a i (j - i + 1) in
        (Array.fold_right (fun x y -> x::y) a' args', s')
      | s -> ([],s) in
    let (out,s') = aux s in
    match s' with [] -> Some out | _ -> None

  let tail n0 s0 =
    let rec aux n s =
      if Int.equal n 0 then s else
        match s with
      | App (i,a,j) :: s ->
         let nb = j - i + 1 in
         if n >= nb then
           aux (n - nb) s
         else
           let p = i+n in
           if j >= p then App (p,a,j) :: s else s
        | _ -> raise (Invalid_argument "Reductionops.Stack.tail")
    in aux n0 s0

  let nth s p =
    match strip_n_app p s with
    | Some (_,el,_) -> el
    | None -> raise Not_found

  let zip sigma s =
  let rec zip = function
    | f, [] -> f
    | f, (App (i,a,j) :: s) ->
       let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
                then a
                else Array.sub a i (j - i + 1) in
       zip (mkApp (f, a'), s)
    | f, (Case (ci,u,pms,rt,iv,br)::s) -> zip (mkCase (ci,u,pms,rt,iv,f,br), s)
  | f, (Fix (fix,st)::s) -> zip
    (mkFix fix, st @ (append_app [|f|] s))
  | f, (Proj (p,r)::s) -> zip (mkProj (p,r,f),s)
  | f, (Primitive (p,c,args,kargs)::s) ->
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
      | (CPrimitives.Kwhnf | CPrimitives.Karg) :: _ -> 0
      | CPrimitives.Kparam :: s -> 1 + nargs s
    in
    let n = nargs kargs in
    (List.skipn (n+1) kargs, strip_n_app n stk)

  let expand_case env sigma ((ci, u, pms, t, iv, br) : case_stk) =
    let dummy = mkProp in
    let (ci, u, pms, t, _, _, br) = EConstr.annotate_case env sigma (ci, u, pms, t, iv, dummy, br) in
    (ci, u, pms, t, br)

end

(** The type of (machine) states (= lambda-bar-calculus' cuts) *)
type state = constr * Stack.t

type reduction_function = env -> evar_map -> constr -> constr
type e_reduction_function = env -> evar_map -> constr -> evar_map * constr

type stack_reduction_function =
    env -> evar_map -> constr -> constr * constr list

type state_reduction_function =
    env -> evar_map -> state -> state

let pr_state env sigma (tm,sk) =
  let open Pp in
  let pr c = Termops.Internal.print_constr_env env sigma c in
  h (pr tm ++ str "|" ++ cut () ++ Stack.pr pr sk)

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

type meta_handler = { meta_value : metavariable -> EConstr.t option }

let safe_meta_value metas ev = match metas with
| None -> None
| Some f -> f.meta_value ev

(*************************************)
(*** Reduction using bindingss ***)
(*************************************)

(* Beta Reduction tools *)

let apply_subst env sigma t stack =
  let rec aux env t stack =
    match (Stack.decomp stack, EConstr.kind sigma t) with
    | Some (h,stacktl), Lambda (_,_,c) ->
       aux (h::env) c stacktl
    | _ -> (substl env t, stack)
  in
  aux env t stack

let beta_applist sigma (c,l) =
  Stack.zip sigma (apply_subst [] sigma c (Stack.append_app_list l Stack.empty))

(* Iota reduction tools *)

let reducible_mind_case sigma c = match EConstr.kind sigma c with
  | Construct _ | CoFix _ -> true
  | _  -> false

let contract_cofix sigma (bodynum,(names,types,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    mkCoFix (ind,typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(** Similar to the "fix" case below *)
let reduce_and_refold_cofix env sigma cofix sk =
  let raw_answer = contract_cofix sigma cofix in
  apply_subst [] sigma raw_answer sk

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix sigma ((recindices,bodynum),(names,types,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j =
    let ind = nbodies-j-1 in
    mkFix ((recindices,ind),typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

(** First we substitute the Rel bodynum by the fixpoint and then we try to
    replace the fixpoint by the best constant from [cst_l]
    Other rels are directly substituted by constants "magically found from the
    context" in contract_fix *)
let reduce_and_refold_fix env sigma fix sk =
  let raw_answer = contract_fix sigma fix in
  apply_subst [] sigma raw_answer sk

open Primred

module CNativeEntries =
struct

  open UnsafeMonomorphic

  type elem = EConstr.t
  type args = EConstr.t array
  type evd = evar_map
  type uinstance = EConstr.EInstance.t

  let get = Array.get

  let get_int evd e =
    match EConstr.kind evd e with
    | Int i -> i
    | _ -> raise Primred.NativeDestKO

  let get_float evd e =
    match EConstr.kind evd e with
    | Float f -> f
    | _ -> raise Primred.NativeDestKO

  let get_string evd e =
    match EConstr.kind evd e with
    | String s -> s
    | _ -> raise Primred.NativeDestKO

  let get_parray evd e =
    match EConstr.kind evd e with
    | Array(_u,t,def,_ty) -> Parray.of_array t def
    | _ -> raise Not_found

  let mkInt env i =
    mkInt i

  let mkFloat env f =
    mkFloat f

  let mkString env s =
    mkString s

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

  let mkFloatIntPair env f i =
    let float_ty = mkConst @@ get_float_type env in
    let int_ty = mkConst @@ get_int_type env in
    let c = get_pair_constructor env in
    mkApp(mkConstruct c, [|float_ty;int_ty;f;i|])

  let mkLt env =
    let (_eq, lt, _gt) = get_cmp_constructors env in
    mkConstruct lt

  let mkEq env =
    let (eq, _lt, _gt) = get_cmp_constructors env in
    mkConstruct eq

  let mkGt env =
    let (_eq, _lt, gt) = get_cmp_constructors env in
    mkConstruct gt

  let mkFLt env =
    let (_eq, lt, _gt, _nc) = get_f_cmp_constructors env in
    mkConstruct lt

  let mkFEq env =
    let (eq, _lt, _gt, _nc) = get_f_cmp_constructors env in
    mkConstruct eq

  let mkFGt env =
    let (_eq, _lt, gt, _nc) = get_f_cmp_constructors env in
    mkConstruct gt

  let mkFNotComparable env =
    let (_eq, _lt, _gt, nc) = get_f_cmp_constructors env in
    mkConstruct nc

  let mkPNormal env =
    let (pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct pNormal

  let mkNNormal env =
    let (_pNormal,nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct nNormal

  let mkPSubn env =
    let (_pNormal,_nNormal,pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct pSubn

  let mkNSubn env =
    let (_pNormal,_nNormal,_pSubn,nSubn,_pZero,_nZero,_pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct nSubn

  let mkPZero env =
    let (_pNormal,_nNormal,_pSubn,_nSubn,pZero,_nZero,_pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct pZero

  let mkNZero env =
    let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,nZero,_pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct nZero

  let mkPInf env =
    let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,pInf,_nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct pInf

  let mkNInf env =
    let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,nInf,_nan) =
      get_f_class_constructors env in
    mkConstruct nInf

  let mkNaN env =
    let (_pNormal,_nNormal,_pSubn,_nSubn,_pZero,_nZero,_pInf,_nInf,nan) =
      get_f_class_constructors env in
    mkConstruct nan

  let mkArray env u t ty =
    let (t,def) = Parray.to_array t in
    mkArray(u,t,def,ty)

end

module CredNative = RedNative(CNativeEntries)



(** Generic reduction function with environment

    Here is where unfolded constant are stored in order to be
    eventually refolded.

    If tactic_mode is true, it uses ReductionBehaviour, prefers
    refold constant instead of value and tries to infer constants
    fix and cofix came from.

    It substitutes fix and cofix by the constant they come from in
    contract_* in any case .
*)

let debug_RAKAM = CDebug.create ~name:"RAKAM" ()

let apply_branch env sigma (ind, i) args (ci, u, pms, iv, r, lf) =
  let args = Stack.tail ci.ci_npar args in
  let args = Option.get (Stack.list_of_app_stack args) in
  let br = lf.(i - 1) in
  if Int.equal ci.ci_cstr_nargs.(i - 1) ci.ci_cstr_ndecls.(i - 1) then
    (* No let-bindings *)
    let subst = List.rev args in
    Vars.substl subst (snd br)
  else
    (* For backwards compat with unification, we do not reduce the let-bindings
       upfront. *)
    let ctx = expand_branch env sigma u pms (ind, i) br in
    applist (it_mkLambda_or_LetIn (snd br) ctx, args)


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
      let t, stk = whrec (t, Stack.empty) in
      let psubst = match_rigid_arg_pattern whrec env sigma ctx psubst ph t in
      let psubst, stk = apply_rule whrec env sigma ctx psubst es stk in
      if Stack.is_empty stk then psubst else raise PatternFailure

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
  | (PHInd _ | PHConstr _ | PHRel _ | PHSort _ | PHSymbol _ | PHInt _ | PHFloat _ | PHString _), _ -> raise PatternFailure

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
  | Declarations.PECase (pind, pu, pret, pbrs) :: e, Stack.Case (ci, u, pms, p, iv, brs) :: s ->
      if not @@ QInd.equal env pind ci.ci_ind then raise PatternFailure;
      let dummy = mkProp in
      let psubst = match_einstance sigma pu u psubst in
      let (_, _, _, ((ntys_ret, ret), _), _, _, brs) = EConstr.annotate_case env sigma (ci, u, pms, p, NoInvert, dummy, brs) in
      let psubst = match_arg_pattern whrec env sigma (ntys_ret @ ctx) psubst pret ret in
      let psubst = Array.fold_left2 (fun psubst pat (ctx', br) -> match_arg_pattern whrec env sigma (ctx' @ ctx) psubst pat br) psubst pbrs brs in
      apply_rule whrec env sigma ctx psubst e s
  | Declarations.PEProj proj :: e, Stack.Proj (proj', r) :: s ->
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

let whd_state_gen flags ?metas env sigma =
  let open Context.Named.Declaration in
  let rec whrec (x, stack) : state =
    let () =
        let open Pp in
        let pr c = Termops.Internal.print_constr_env env sigma c in
        debug_RAKAM (fun () ->
               (h (str "<<" ++ pr x ++
                   str "|" ++ cut () ++ Stack.pr pr stack ++
                   str ">>")))
    in
    let c0 = EConstr.kind sigma x in
    let fold () =
      let () = debug_RAKAM (fun () ->
          let open Pp in str "<><><><><>") in
      ((EConstr.of_kind c0, stack))
    in
    match c0 with
    | Rel n when RedFlags.red_set flags RedFlags.fDELTA ->
      (match lookup_rel n env with
      | LocalDef (_,body,_) -> whrec (lift n body, stack)
      | _ -> fold ())
    | Var id when RedFlags.red_set flags (RedFlags.fVAR id) ->
      (match lookup_named id env with
      | LocalDef (_,body,_) ->
        whrec (body, stack)
      | _ -> fold ())
    | Evar ev -> fold ()
    | Meta ev ->
      (match safe_meta_value metas ev with
      | Some body -> whrec (body, stack)
      | None -> fold ())
    | Const (c,u as const) ->
      reduction_effect_hook env sigma c
         (lazy (EConstr.to_constr sigma (Stack.zip sigma (x,fst (Stack.strip_app stack)))));
      if RedFlags.red_set flags (RedFlags.fCONST c) then
       let u' = EInstance.kind sigma u in
       match constant_value_in env (c, u') with
       | body ->
         begin
          let body = EConstr.of_constr body in
          whrec (body, stack)
          end
       | exception NotEvaluableConst (IsPrimitive (u,p)) when Stack.check_native_args p stack ->
          let kargs = CPrimitives.kind p in
          let (kargs,o) = Stack.get_next_primitive_args kargs stack in
          (* Should not fail thanks to [check_native_args] *)
          let (before,a,after) = Option.get o in
          whrec (a,Stack.Primitive(p,const,before,kargs)::after)
       | exception NotEvaluableConst (HasRules (u', b, r)) ->
          begin try
            let rhs, stack = apply_rules whrec env sigma u r stack in
            whrec (rhs, stack)
          with PatternFailure ->
            if not b then fold () else
            match Stack.strip_app stack with
            | args, (Stack.Fix (f,s')::s'') when RedFlags.red_set flags RedFlags.fFIX ->
              let x' = Stack.zip sigma (x, args) in
              let out_sk = s' @ (Stack.append_app [|x'|] s'') in
              whrec (reduce_and_refold_fix env sigma f out_sk)
            | _ -> fold ()
          end
       | exception NotEvaluableConst _ -> fold ()
      else fold ()
    | Proj (p, r, c) when RedFlags.red_projection flags p ->
      let stack' = (c, Stack.Proj (p,r) :: stack) in
      whrec stack'

    | LetIn (_,b,_,c) when RedFlags.red_set flags RedFlags.fZETA ->
      whrec (apply_subst [b] sigma c stack)
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  ->
      whrec
        (f, Stack.append_app cl stack)
    | Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when RedFlags.red_set flags RedFlags.fBETA ->
        whrec (apply_subst [] sigma x stack)
      | _ -> fold ())

    | Case (ci,u,pms,p,iv,d,lf) ->
      whrec (d, Stack.Case (ci,u,pms,p,iv,lf) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> fold ()
      |Some (bef,arg,s') ->
        whrec (arg, Stack.Fix(f,bef)::s'))

    | Construct (cstr ,u) ->
      let use_match = RedFlags.red_set flags RedFlags.fMATCH in
      let use_fix = RedFlags.red_set flags RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case case::s') when use_match ->
          let r = apply_branch env sigma cstr args case in
          whrec (r, s')
        |args, (Stack.Proj (p,_)::s') when use_match ->
          whrec (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (f,s')::s'') when use_fix ->
          let x' = Stack.zip sigma (x, args) in
          let out_sk = s' @ (Stack.append_app [|x'|] s'') in
          whrec (reduce_and_refold_fix env sigma f out_sk)
        |_, (Stack.App _)::_ -> assert false
        |_, _ -> fold ()
      else fold ()

    | CoFix cofix ->
      if RedFlags.red_set flags RedFlags.fCOFIX then
        match Stack.strip_app stack with
        |args, ((Stack.Case _ |Stack.Proj _)::s') ->
          whrec (reduce_and_refold_cofix env sigma cofix stack)
        |_ -> fold ()
      else fold ()

    | Int _ | Float _ | String _ | Array _ ->
      begin match Stack.strip_app stack with
       | (_, Stack.Primitive(p,(_, u as kn),rargs,kargs)::s) ->
         let more_to_reduce = List.exists (fun k -> CPrimitives.Kwhnf = k) kargs in
         if more_to_reduce then
           let (kargs,o) = Stack.get_next_primitive_args kargs s in
           (* Should not fail because Primitive is put on the stack only if fully applied *)
           let (before,a,after) = Option.get o in
           whrec (a,Stack.Primitive(p,kn,rargs @ Stack.append_app [|x|] before,kargs)::after)
         else
           let n = List.length kargs in
           let (args,s) = Stack.strip_app s in
           let (args,extra_args) =
             try List.chop n args
             with List.IndexOutOfRange -> (args,[]) (* FIXME probably useless *)
           in
           let args = Array.of_list (Option.get (Stack.list_of_app_stack (rargs @ Stack.append_app [|x|] args))) in
           let s = extra_args @ s in
           begin match CredNative.red_prim env sigma p u args with
             | Some t -> whrec (t,s)
             | None -> ((mkApp (mkConstU kn, args), s))
           end
       | _ -> fold ()
      end

    | Rel _ | Var _ | LetIn _ | Proj _ -> fold ()
    | Sort _ | Ind _ | Prod _ -> fold ()
  in
  whrec

(** reduction machine without global env and refold machinery *)
let local_whd_state_gen flags ?metas env sigma =
  let rec whrec (x, stack) =
    let c0 = EConstr.kind sigma x in
    let s = (EConstr.of_kind c0, stack) in
    match c0 with
    | LetIn (_,b,_,c) when RedFlags.red_set flags RedFlags.fZETA ->
      whrec (apply_subst [b] sigma c stack)
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  -> whrec (f, Stack.append_app cl stack)
    | Lambda (_,_,c) ->
      (match Stack.decomp stack with
      | Some (a,m) when RedFlags.red_set flags RedFlags.fBETA ->
        whrec (apply_subst [a] sigma c m)
      | _ -> s)

    | Proj (p,r,c) when RedFlags.red_projection flags p ->
      (whrec (c, Stack.Proj (p,r) :: stack))

    | Case (ci,u,pms,p,iv,d,lf) ->
      whrec (d, Stack.Case (ci,u,pms,p,iv,lf) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> s
      |Some (bef,arg,s') -> whrec (arg, Stack.Fix(f,bef)::s'))

    | Evar ev -> s
    | Meta ev ->
      (match safe_meta_value metas ev with
        Some c -> whrec (c,stack)
      | None -> s)

    | Construct (cstr, u) ->
      let use_match = RedFlags.red_set flags RedFlags.fMATCH in
      let use_fix = RedFlags.red_set flags RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case case :: s') when use_match ->
          let r = apply_branch env sigma cstr args case in
          whrec (r, s')
        |args, (Stack.Proj (p,_) :: s') when use_match ->
          whrec (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (f,s')::s'') when use_fix ->
          let x' = Stack.zip sigma (x,args) in
          whrec (contract_fix sigma f, s' @ (Stack.append_app [|x'|] s''))
        |_, (Stack.App _)::_ -> assert false
        |_, _ -> s
      else s

    | CoFix cofix ->
      if RedFlags.red_set flags RedFlags.fCOFIX then
        match Stack.strip_app stack with
        |args, ((Stack.Case _ | Stack.Proj _)::s') ->
          whrec (contract_cofix sigma cofix, stack)
        |_ -> s
      else s

    | Rel _ | Var _ | Sort _ | Prod _ | LetIn _ | Const _  | Ind _ | Proj _
      | Int _ | Float _ | String _ | Array _ -> s

  in
  whrec

let stack_red_of_state_red f ?metas =
  let f env sigma x = EConstr.decompose_app_list sigma (Stack.zip sigma (f ?metas env sigma (x, Stack.empty))) in
  f

let red_of_state_red ?metas ~delta f env sigma x =
  let rec is_whnf c = match Constr.kind c with
    | Const _ | Var _ -> not delta
    | Construct _ | Ind _ | Int _ | Float _ | String _
    | Sort _ | Prod _ -> true
    | App (h,_) -> is_whnf h
    | _ -> false
  in
  (* preserve physical equality if possible
     not sure if anything relies on reduction unfolding head evars
     for now use Unsafe.to_constr to keep such unfolds *)
  if is_whnf (EConstr.Unsafe.to_constr x) then x
  else Stack.zip sigma (f ?metas env sigma (x,Stack.empty))

(* 0. No Reduction Functions *)

let whd_nored_state = local_whd_state_gen RedFlags.nored
let whd_nored_stack = stack_red_of_state_red whd_nored_state
let whd_nored ?metas = red_of_state_red ?metas ~delta:false whd_nored_state

(* 1. Beta Reduction Functions *)

let whd_beta_state = local_whd_state_gen RedFlags.beta
let whd_beta_stack = stack_red_of_state_red whd_beta_state
let whd_beta = red_of_state_red ~delta:false whd_beta_state

let whd_betalet_state = local_whd_state_gen RedFlags.betazeta
let whd_betalet_stack = stack_red_of_state_red whd_betalet_state
let whd_betalet = red_of_state_red ~delta:false whd_betalet_state

(* 2. Delta Reduction Functions *)

let whd_const_state c e = whd_state_gen RedFlags.(mkflags [fCONST c]) e
let whd_const c = red_of_state_red ~delta:true (fun ?metas -> whd_const_state c)

let whd_delta_state = whd_state_gen RedFlags.delta
let whd_delta_stack = stack_red_of_state_red whd_delta_state
let whd_delta = red_of_state_red ~delta:true whd_delta_state

let whd_betadeltazeta_state = whd_state_gen RedFlags.betadeltazeta
let whd_betadeltazeta_stack = stack_red_of_state_red whd_betadeltazeta_state
let whd_betadeltazeta = red_of_state_red ~delta:true whd_betadeltazeta_state

(* 3. Iota reduction Functions *)

let whd_betaiota_state = local_whd_state_gen RedFlags.betaiota
let whd_betaiota_stack = stack_red_of_state_red whd_betaiota_state
let whd_betaiota ?metas = red_of_state_red ?metas ~delta:false whd_betaiota_state

let whd_betaiotazeta_state = local_whd_state_gen RedFlags.betaiotazeta
let whd_betaiotazeta_stack = stack_red_of_state_red whd_betaiotazeta_state
let whd_betaiotazeta ?metas = red_of_state_red ?metas ~delta:false whd_betaiotazeta_state

let whd_all_state = whd_state_gen RedFlags.all
let whd_all_stack = stack_red_of_state_red whd_all_state
let whd_all ?metas = red_of_state_red ?metas ~delta:true whd_all_state

let whd_allnolet_state = whd_state_gen RedFlags.allnolet
let whd_allnolet_stack = stack_red_of_state_red whd_allnolet_state
let whd_allnolet = red_of_state_red ~delta:true whd_allnolet_state

let whd_stack_gen reds = stack_red_of_state_red (whd_state_gen reds)

let is_head_evar env sigma c =
  let head, _ = whd_all_state env sigma (c,Stack.empty) in
  EConstr.isEvar sigma head

(* 4. Ad-hoc eta reduction *)

let shrink_eta sigma c =
  let rec whrec x = match EConstr.kind sigma x with
    | Cast (c, _, _) -> whrec c
    | Lambda (_, _, c) ->
      let (f, cl) = decompose_app sigma (whrec c) in
      let napp = Array.length cl in
      if napp > 0 then
        let x' = whrec (Array.last cl) in
        match EConstr.kind sigma x' with
        | Rel 1 ->
          let lc = Array.sub cl 0 (napp-1) in
          let u = mkApp (f, lc) in
          if noccurn sigma 1 u then pop u else x
        | _ -> x
      else x
    | Meta _ | App _ | Case _ | Fix _ | Construct _ | CoFix _ | Evar _ | Rel _ | Var _ | Sort _ | Prod _
    | LetIn _ | Const _  | Ind _ | Proj _ | Int _ | Float _ | String _ | Array _ -> x
  in
  whrec c

(* 5. Zeta Reduction Functions *)

let whd_zeta_state = local_whd_state_gen RedFlags.zeta
let whd_zeta_stack = stack_red_of_state_red whd_zeta_state
let whd_zeta = red_of_state_red ~delta:false whd_zeta_state

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
    EConstr.of_constr (CClosure.norm_term
      (Evarutil.create_clos_infos env sigma flgs)
      (CClosure.create_tab ())
      (Esubst.subs_id 0, UVars.Instance.empty) (EConstr.Unsafe.to_constr t))
  with e when is_anomaly e -> user_err Pp.(str "Tried to normalize ill-typed term")

let clos_whd_flags flgs env sigma t =
  try
    EConstr.of_constr (CClosure.whd_val
      (Evarutil.create_clos_infos env sigma flgs)
      (CClosure.create_tab ())
      (CClosure.inject (EConstr.Unsafe.to_constr t)))
  with e when is_anomaly e -> user_err Pp.(str "Tried to normalize ill-typed term")

let nf_beta = clos_norm_flags RedFlags.beta
let nf_betaiota = clos_norm_flags RedFlags.betaiota
let nf_betaiotazeta = clos_norm_flags RedFlags.betaiotazeta
let nf_zeta = clos_norm_flags RedFlags.zeta
let nf_all env sigma =
  clos_norm_flags RedFlags.all env sigma


(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

let is_transparent e k =
  match Conv_oracle.get_strategy (Environ.oracle e) (Evaluable.to_kevaluable k) with
  | Conv_oracle.Opaque -> false
  | _ -> true

(* Conversion utility functions *)

type conversion_test = Constraints.t -> Constraints.t

(* NOTE: We absorb anomalies happening in the conversion tactic, which
   is a bit ugly. This is mostly due to efficiency both in tactics and
   in the conversion machinery itself. It is not uncommon for a tactic
   to send some ill-typed term to the engine.

   We would usually say that a tactic that converts ill-typed terms is
   buggy, but fixing the tactic could have a very large runtime cost
   *)
exception AnomalyInConversion of exn

let _ = CErrors.register_handler (function
    | AnomalyInConversion e ->
      Some Pp.(str "Conversion test raised an anomaly:" ++
               spc () ++ CErrors.print e)
    | _ -> None)

let report_anomaly (e, info) =
  let e =
    if is_anomaly e then AnomalyInConversion e
    else e
  in
  Exninfo.iraise (e, info)

module CheckUnivs =
struct

open Conversion

let check_eq univs u u' =
  if Evd.check_eq univs u u' then Result.Ok univs else Result.Error None

let check_leq univs u u' =
  if Evd.check_leq univs u u' then Result.Ok univs else Result.Error None

let checked_sort_cmp_universes _env pb s0 s1 univs =
  let s0 = ESorts.make s0 in
  let s1 = ESorts.make s1 in
  match pb with
  | CUMUL -> check_leq univs s0 s1
  | CONV -> check_eq univs s0 s1

let check_convert_instances ~flex:_ u u' univs =
  let csts = UVars.enforce_eq_instances u u' (Sorts.QConstraints.empty,Constraints.empty) in
  if Evd.check_quconstraints univs csts then Result.Ok univs else Result.Error None

(* general conversion and inference functions *)
let check_inductive_instances cv_pb variance u1 u2 univs =
  let csts = get_cumulativity_constraints cv_pb variance u1 u2 in
  if (Evd.check_quconstraints univs csts) then Result.Ok univs
  else Result.Error None

let checked_universes =
  { compare_sorts = checked_sort_cmp_universes;
    compare_instances = check_convert_instances;
    compare_cumul_instances = check_inductive_instances; }

end

let is_fconv ?(reds=TransparentState.full) pb env sigma t1 t2 =
  let univs = Evd.universes sigma in
  let t1 = EConstr.Unsafe.to_constr t1 in
  let t2 = EConstr.Unsafe.to_constr t2 in
  let b = match pb with
  | Conversion.CUMUL -> leq_constr_univs univs t1 t2
  | Conversion.CONV -> eq_constr_univs univs t1 t2
  in
  if b then true
  else
    let evars = Evd.evar_handler sigma in
    try
      let env = Environ.set_universes (Evd.universes sigma) env in
      begin match Conversion.generic_conv ~l2r:false pb ~evars reds env (sigma, CheckUnivs.checked_universes) t1 t2 with
      | Result.Ok (_ : Evd.evar_map) -> true
      | Result.Error None -> false
      | Result.Error (Some e) -> Empty.abort e
      end
    with
    | e ->
      let e = Exninfo.capture e in
      report_anomaly e

let is_conv ?(reds=TransparentState.full) env sigma x y =
  is_fconv ~reds Conversion.CONV env sigma x y
let is_conv_leq ?(reds=TransparentState.full) env sigma x y =
  is_fconv ~reds Conversion.CUMUL env sigma x y
let check_conv ?(pb=Conversion.CUMUL) ?(ts=TransparentState.full) env sigma x y =
  is_fconv ~reds:ts pb env sigma x y

let sigma_compare_sorts _env pb s0 s1 sigma =
  match pb with
  | Conversion.CONV ->
    begin
      try Result.Ok (Evd.set_eq_sort sigma (ESorts.make s0) (ESorts.make s1))
      with UGraph.UniverseInconsistency err -> Result.Error (Some err)
    end
  | Conversion.CUMUL ->
    begin
      try Result.Ok (Evd.set_leq_sort sigma (ESorts.make s0) (ESorts.make s1))
      with UGraph.UniverseInconsistency err -> Result.Error (Some err)
    end

let sigma_compare_instances ~flex i0 i1 sigma =
  match Evd.set_eq_instances ~flex sigma i0 i1 with
  | sigma -> Result.Ok sigma
  | exception Evd.UniversesDiffer -> Result.Error None
  | exception UGraph.UniverseInconsistency err -> Result.Error (Some err)

let sigma_check_inductive_instances cv_pb variance u1 u2 sigma =
  match Evarutil.compare_cumulative_instances cv_pb variance u1 u2 sigma with
  | Inl sigma -> Result.Ok sigma
  | Inr err -> Result.Error (Some err)

let sigma_univ_state =
  let open Conversion in
  { compare_sorts = sigma_compare_sorts;
    compare_instances = sigma_compare_instances;
    compare_cumul_instances = sigma_check_inductive_instances; }

let univproblem_compare_sorts env pb s0 s1 uset =
  let open UnivProblem in
  match pb with
  | Conversion.CONV -> Result.Ok (UnivProblem.Set.add (UEq (s0, s1)) uset)
  | Conversion.CUMUL -> Result.Ok (UnivProblem.Set.add (ULe (s0, s1)) uset)

let univproblem_compare_instances ~flex i0 i1 uset =
  Result.Ok (UnivProblem.enforce_eq_instances_univs flex i0 i1 uset)

let univproblem_check_inductive_instances cv_pb variance u1 u2 sigma =
  Result.Ok (UnivProblem.compare_cumulative_instances cv_pb variance u1 u2 sigma)

let univproblem_univ_state =
  let open Conversion in
  { compare_sorts = univproblem_compare_sorts;
    compare_instances = univproblem_compare_instances;
    compare_cumul_instances = univproblem_check_inductive_instances; }

type genconv = {
  genconv : 'a 'err. conv_pb -> l2r:bool -> Evd.evar_map -> TransparentState.t ->
    Environ.env -> ('a, 'err) Conversion.generic_conversion_function
}

let infer_conv_gen conv_fun ?(catch_incon=true) ?(pb=Conversion.CUMUL)
    ?(ts=TransparentState.full) env sigma x y =
  try
      let ans = match pb with
      | Conversion.CUMUL ->
          EConstr.leq_constr_universes env sigma x y
      | Conversion.CONV ->
          EConstr.eq_constr_universes env sigma x y
      in
      let ans = match ans with
      | None -> None
      | Some cstr ->
        try Some (Evd.add_universe_constraints sigma cstr)
        with UGraph.UniverseInconsistency _ | Evd.UniversesDiffer -> None
      in
      match ans with
      | Some sigma -> ans
      | None ->
        let x = EConstr.Unsafe.to_constr x in
        let y = EConstr.Unsafe.to_constr y in
        let env = Environ.set_universes (Evd.universes sigma) env in
        (* First try conversion with postponed universe problems as a kind of FO
           approximation. This may result in unsatisfiable constraints even if
           some unfoldings of the arguments could have been unified, but this
           should be exceedingly rare. *)
        let ans = match conv_fun.genconv pb ~l2r:false sigma ts env (UnivProblem.Set.empty, univproblem_univ_state) x y with
        | Result.Ok cstr -> Some cstr
        | Result.Error None ->
          None (* no universe unification can make these terms convertible *)
        | Result.Error (Some e) -> Empty.abort e
        in
        match ans with
        | None -> None
        | Some cstr ->
          match Evd.add_universe_constraints sigma cstr with
          | sigma -> Some sigma
          | exception UGraph.UniverseInconsistency _ | exception Evd.UniversesDiffer ->
            (* Retry with local universe checking, which may imply constant unfolding *)
            match conv_fun.genconv pb ~l2r:false sigma ts env (sigma, sigma_univ_state) x y with
            | Result.Ok sigma -> Some sigma
            | Result.Error None -> None
            | Result.Error (Some e) -> raise (UGraph.UniverseInconsistency e)
  with
  | UGraph.UniverseInconsistency _ when catch_incon -> None
  | e ->
    let e = Exninfo.capture e in
    report_anomaly e

let infer_conv = infer_conv_gen { genconv = fun pb ~l2r sigma ->
      Conversion.generic_conv pb ~l2r ~evars:(Evd.evar_handler sigma) }

let infer_conv_ustate ?(catch_incon=true) ?(pb=Conversion.CUMUL)
    ?(ts=TransparentState.full) env sigma x y =
  try
      let ans = match pb with
      | Conversion.CUMUL ->
          EConstr.leq_constr_universes env sigma x y
      | Conversion.CONV ->
          EConstr.eq_constr_universes env sigma x y
      in
      match ans with
      | Some cstr -> Some cstr
      | None ->
        let x = EConstr.Unsafe.to_constr x in
        let y = EConstr.Unsafe.to_constr y in
        let env = Environ.set_universes (Evd.universes sigma) env in
        match
          Conversion.generic_conv pb ~l2r:false ~evars:(Evd.evar_handler sigma) ts
            env (UnivProblem.Set.empty, univproblem_univ_state) x y
        with
        | Result.Ok cstr -> Some cstr
        | Result.Error None -> None
        | Result.Error (Some e) -> raise (UGraph.UniverseInconsistency e)
  with
  | UGraph.UniverseInconsistency _ when catch_incon -> None
  | e ->
    let e = Exninfo.capture e in
    report_anomaly e

let evars_of_evar_map sigma =
  { Genlambda.evars_val = Evd.evar_handler sigma }

let vm_infer_conv ?(pb=Conversion.CUMUL) env sigma t1 t2 =
  infer_conv_gen { genconv = fun pb ~l2r sigma ts ->
      Vconv.vm_conv_gen pb (evars_of_evar_map sigma) }
    ~catch_incon:true ~pb env sigma t1 t2

let native_conv_generic pb sigma t =
  Nativeconv.native_conv_gen pb (evars_of_evar_map sigma) t

let native_infer_conv ?(pb=Conversion.CUMUL) env sigma t1 t2 =
  infer_conv_gen { genconv = fun pb ~l2r sigma ts -> native_conv_generic pb sigma }
    ~catch_incon:true ~pb env sigma t1 t2

let check_hyps_inclusion env sigma x hyps =
  let env = Environ.set_universes (Evd.universes sigma) env in
  let evars = Evd.evar_handler sigma in
  Typeops.check_hyps_inclusion env ~evars x hyps

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

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

let whd_decompose_prod env sigma =
  let rec decrec env hyps c =
    let t = whd_all env sigma c in
    match EConstr.kind sigma t with
      | Prod (n,a,c0) ->
         decrec (push_rel (LocalAssum (n,a)) env) ((n,a)::hyps) c0
      | _ -> hyps, t
  in
  decrec env []

let whd_decompose_lambda env sigma =
  let rec decrec env hyps c =
    let t = whd_all env sigma c in
    match EConstr.kind sigma t with
      | Lambda (n,a,c0) ->
         decrec (push_rel (LocalAssum (n,a)) env) ((n,a)::hyps) c0
      | _ -> hyps, t
  in
  decrec env []

let whd_decompose_prod_n env sigma n =
  let rec decrec env m hyps c = if Int.equal m 0 then (hyps,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Prod (n,a,c0) ->
         decrec (push_rel (LocalAssum (n,a)) env) (m-1) ((n,a)::hyps) c0
      | _ -> invalid_arg "whd_decompose_prod_n"
  in
  decrec env n []

let whd_decompose_lambda_n env sigma n =
  let rec decrec env m hyps c = if Int.equal m 0 then (hyps,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Lambda (n,a,c0) ->
         decrec (push_rel (LocalAssum (n,a)) env) (m-1) ((n,a)::hyps) c0
      | _ -> invalid_arg "whd_decompose_lambda_n"
  in
  decrec env n []

let whd_decompose_prod_decls env sigma =
  let rec prodec_rec env l c =
    let t = whd_allnolet env sigma c in
    match EConstr.kind sigma t with
    | Prod (x,t,c)  ->
        let d = LocalAssum (x,t) in
        prodec_rec (push_rel d env) (Context.Rel.add d l) c
    | LetIn (x,b,t,c) ->
        (* note: there is a compromise in situations such as
           "let x := forall y, P in x": expose the let-in and stop looking
            for products or ignore the let and find a new product *)
        let d = LocalDef (x,b,t) in
        prodec_rec (push_rel d env) (Context.Rel.add d l) c
    | _               ->
      (* deal with situations of the form "(let x:=t in fun y => u) v", or even
         "(let x:=fun y => u in x) v", ...
         ideally, shouldn't we move instead the let-ins outside the redexes? *)
      let t' = whd_all env sigma t in
        if EConstr.eq_constr sigma t t' then l,t
        else prodec_rec env l t'
  in
  prodec_rec env Context.Rel.empty

let splay_arity env sigma c =
  let l, c = whd_decompose_prod env sigma c in
  match EConstr.kind sigma c with
    | Sort s -> l,s
    | _ -> raise Reduction.NotArity

let dest_arity env sigma c =
  let l, c = whd_decompose_prod_decls env sigma c in
  match EConstr.kind sigma c with
    | Sort s -> l,s
    | _ -> raise Reduction.NotArity

let sort_of_arity env sigma c = snd (dest_arity env sigma c)

(* deprecated (wrong behavior)  *)
let hnf_decompose_prod_n_decls env sigma n =
  let rec decrec env m ln c = if Int.equal m 0 then (ln,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Prod (n,a,c0) ->
          decrec (push_rel (LocalAssum (n,a)) env)
            (m-1) (Context.Rel.add (LocalAssum (n,a)) ln) c0
      | _                      -> invalid_arg "whd_decompose_prod_n_decls"
  in
  decrec env n Context.Rel.empty

(* deprecated (wrong behavior) *)
let hnf_decompose_lambda_n_assum env sigma n =
  let rec decrec env m ln c = if Int.equal m 0 then (ln,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Lambda (n,a,c0) ->
          decrec (push_rel (LocalAssum (n,a)) env)
            (m-1) (Context.Rel.add (LocalAssum (n,a)) ln) c0
      | _                      -> invalid_arg "whd_decompose_lambda_n_assum"
  in
  decrec env n Context.Rel.empty

let whd_decompose_prod_n_assum env sigma n =
  let rec decrec env m ctx c = if Int.equal m 0 then (ctx,c) else
    match EConstr.kind sigma (whd_allnolet env sigma c) with
      | Prod (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (push_rel d env) (m-1) (Context.Rel.add d ctx) c0
      | LetIn (x,b,t,c) ->
          let d = LocalDef (x,b,t) in
          decrec (push_rel d env) m (Context.Rel.add d ctx) c
      | _ ->
        (* deal with situations of the form "(let x:=t in fun y => u) v", or even
           "(let x:=fun y => u in x) v", ...
           ideally, shouldn't we move instead the let-ins outside the redexes? *)
        let c' = whd_all env sigma c in
        if EConstr.eq_constr sigma c c' then invalid_arg "whd_decompose_prod_n_assum"
        else decrec env m ctx c'
  in
  decrec env n Context.Rel.empty

let whd_decompose_prod_n_decls env sigma n =
  let rec decrec env m ctx c = if Int.equal m 0 then (ctx,c) else
    match EConstr.kind sigma (whd_all env sigma c) with
      | Prod (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (push_rel d env) (m-1) (Context.Rel.add d ctx) c0
      | LetIn (x,b,t,c) ->
          let d = LocalDef (x,b,t) in
          decrec (push_rel d env) (m-1) (Context.Rel.add d ctx) c
      | _ ->
        (* deal with situations of the form "(let x:=t in fun y => u) v", or even
           "(let x:=fun y => u in x) v", ...
           ideally, shouldn't we move instead the let-ins outside the redexes? *)
        let c' = whd_all env sigma c in
        if EConstr.eq_constr sigma c c' then invalid_arg "whd_decompose_prod_n_decls"
        else decrec env m ctx c'
  in
  decrec env n Context.Rel.empty

let whd_decompose_lambda_n_assum env sigma n =
  let rec decrec env m ctx c = if Int.equal m 0 then (ctx,c) else
    match EConstr.kind sigma (whd_allnolet env sigma c) with
      | Lambda (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (push_rel d env) (m-1) (Context.Rel.add d ctx) c0
      | LetIn (x,b,t,c) ->
          let d = LocalDef (x,b,t) in
          decrec (push_rel d env) m (Context.Rel.add d ctx) c
      | _ ->
        (* deal with situations of the form "(let x:=t in fun y => u) v", or even
           "(let x:=fun y => u in x) v", ...
           ideally, shouldn't we move instead the let-ins outside the redexes? *)
        let c' = whd_all env sigma c in
        if EConstr.eq_constr sigma c c' then invalid_arg "whd_decompose_lambda_n_assum"
        else decrec env m ctx c'
  in
  decrec env n Context.Rel.empty

let is_sort env sigma t =
  match EConstr.kind sigma (whd_all env sigma t) with
  | Sort s -> true
  | _ -> false

(* reduction to head-normal-form allowing delta/zeta only in argument
   of case/fix (heuristic used by evar_conv) *)

let whd_betaiota_deltazeta_for_iota_state ts ?metas env sigma s =
  let all' = RedFlags.red_add_transparent RedFlags.all ts in
  (* Unset the sharing flag to get a call-by-name reduction. This matters for
     the shape of the generated term. *)
  let env' = Environ.set_typing_flags { (Environ.typing_flags env) with Declarations.share_reduction = false } env in
  let whd_opt c =
    let open CClosure in
    let infos = Evarutil.create_clos_infos env' sigma all' in
    let tab = create_tab () in
    let c = inject (EConstr.Unsafe.to_constr (Stack.zip sigma c)) in
    let (c, stk) = whd_stack infos tab c [] in
    match fterm_of c with
    | (FConstruct _ | FCoFix _) ->
      (* Non-neutral normal, can trigger reduction below *)
      let c = EConstr.of_constr (term_of_process c stk) in
      Some (decompose_app sigma c)
    | _ -> None
  in
  let rec whrec s =
    let (t, stack as s) = whd_state_gen RedFlags.betaiota ?metas env sigma s in
    let rewrite_step =
      match kind sigma t with
      | Const (cst, u) when Environ.is_symbol env cst ->
        let r = Environ.lookup_rewrite_rules cst env in
        begin match apply_rules whrec env sigma u r stack with
        | r -> Some r
        | exception PatternFailure -> None
        end
      | _ -> None
    in
    match rewrite_step with
    | Some r -> whrec r
    | None ->
    match Stack.strip_app stack with
      |args, (Stack.Case _ :: _ as stack') ->
        begin match whd_opt (t, args) with
        | Some (t_o, args) when reducible_mind_case sigma t_o -> whrec (t_o, Stack.append_app args stack')
        | (Some _ | None) -> s
        end
      |args, (Stack.Fix _ :: _ as stack') ->
        begin match whd_opt (t, args) with
        | Some (t_o, args) when isConstruct sigma t_o -> whrec (t_o, Stack.append_app args stack')
        | (Some _ | None) -> s
        end
      |args, (Stack.Proj (p,_) :: stack'') ->
        begin match whd_opt (t, args) with
        | Some (t_o, args) when isConstruct sigma t_o ->
          whrec (args.(Projection.npars p + Projection.arg p), stack'')
        | (Some _ | None) -> s
        end
      |_, ((Stack.App _|Stack.Primitive _) :: _|[]) -> s
  in
  whrec s

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

module Infer = struct

open Conversion

let infer_eq (univs, cstrs as cuniv) u u' =
  if UGraph.check_eq_sort univs u u' then Result.Ok cuniv
  else try
    let cstrs' = UnivSubst.enforce_eq_sort u u' Constraints.empty in
    Result.Ok (UGraph.merge_constraints cstrs' univs, Constraints.union cstrs cstrs')
  with UGraph.UniverseInconsistency err -> Result.Error (Some err)

let infer_leq (univs, cstrs as cuniv) u u' =
  if UGraph.check_leq_sort univs u u' then Result.Ok cuniv
  else match UnivSubst.enforce_leq_alg_sort u u' univs with
  | cstrs', univs ->
    Result.Ok (univs, Univ.Constraints.union cstrs cstrs')
  | exception UGraph.UniverseInconsistency err -> Result.Error (Some err)

let infer_cmp_universes _env pb s0 s1 univs =
  match pb with
  | CUMUL -> infer_leq univs s0 s1
  | CONV -> infer_eq univs s0 s1

let infer_convert_instances ~flex u u' (univs,cstrs as cuniv) =
  if flex then
    if UGraph.check_eq_instances univs u u' then Result.Ok cuniv
    else Result.Error None
  else
    let qcstrs, cstrs' = UVars.enforce_eq_instances u u' Sorts.QUConstraints.empty in
    if Sorts.QConstraints.trivial qcstrs then
      Result.Ok (univs, Constraints.union cstrs cstrs')
    else
      Result.Error None

let infer_inductive_instances cv_pb variance u1 u2 (univs,csts) =
  let qcsts, csts' = get_cumulativity_constraints cv_pb variance u1 u2 in
  if Sorts.QConstraints.trivial qcsts then
    match UGraph.merge_constraints csts' univs with
    | univs -> Result.Ok (univs, Univ.Constraints.union csts csts')
    | exception (UGraph.UniverseInconsistency err) -> Result.Error (Some err)
  else Result.Error None

let inferred_universes =
  { compare_sorts = infer_cmp_universes;
    compare_instances = infer_convert_instances;
    compare_cumul_instances = infer_inductive_instances; }

end

let inferred_universes = Infer.inferred_universes

(* Deprecated *)

let splay_prod = whd_decompose_prod
let splay_lam = whd_decompose_lambda
let splay_prod_assum = whd_decompose_prod_decls
let splay_prod_n = hnf_decompose_prod_n_decls
let splay_lam_n = hnf_decompose_lambda_n_assum

let hnf_decompose_prod = whd_decompose_prod
let hnf_decompose_lambda = whd_decompose_lambda
let hnf_decompose_prod_decls = whd_decompose_prod_decls
