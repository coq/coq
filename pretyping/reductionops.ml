(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Context
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
    let effect = String.Map.find funkey !effect_table in
    effect env sigma (Lazy.force c)
  with Not_found -> ()

let cache_reduction_effect (con,funkey) =
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
  Lib.add_leaf (inReductionEffect (x,funkey))


(** Machinery to custom the behavior of the reduction *)
module ReductionBehaviour = struct
  open Globnames
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

  let table =
    Summary.ref (GlobRef.Map.empty : t GlobRef.Map.t) ~name:"reductionbehaviour"

  let load _ (_,(r, b)) =
    table := GlobRef.Map.add r b !table

  let cache o = load 1 o

  let classify (local,_) = if local then Dispose else Substitute

  let subst (subst, (local, (r,o) as orig)) =
    let r' = subst_global_reference subst r in if r==r' then orig
    else (local,(r',o))

  let discharge = function
    | false, (gr, b) ->
      let b =
        if Lib.is_in_section gr then
          let vars = Lib.section_instance gr in
          let extra = Array.length vars in
          more_args extra b
        else b
      in
      Some (false, (gr, b))
    | true, _ -> None

  let rebuild = function
    | req, (GlobRef.ConstRef c, _ as x) -> req, x
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

  let set ~local r b =
    Lib.add_leaf (inRedBehaviour (local, (r, b)))

  let get r = GlobRef.Map.find_opt r !table

  let print ref =
    let open Pp in
    let pr_global = Nametab.pr_global_env Id.Set.empty in
    match get ref with
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

end

(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack :
sig
  open EConstr
  type app_node
  val pr_app_node : (EConstr.t -> Pp.t) -> app_node -> Pp.t

  type case_stk =
    case_info * EInstance.t * EConstr.t array * EConstr.t pcase_return * EConstr.t  pcase_invert * EConstr.t pcase_branch array

  type member =
  | App of app_node
  | Case of case_stk
  | Proj of Projection.t
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
  val expand_case : env -> evar_map -> case_stk -> case_info * EInstance.t * constr array * (rel_context * constr) * (rel_context * constr) array
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
    case_info * EInstance.t * EConstr.t array * EConstr.t pcase_return * EConstr.t  pcase_invert * EConstr.t pcase_branch array

  type member =
  | App of app_node
  | Case of case_stk
  | Proj of Projection.t
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
    | Proj p  ->
      str "ZProj(" ++ Constant.debug_print (Projection.constant p) ++ str ")"
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
      | (Proj (p)::s1, Proj(p2)::s2) ->
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
      | Case ((_,_,pms1,(_, t1),_,a1)) :: q1, Case ((_,_,pms2, (_, t2),_,a2)) :: q2 ->
        let f' o (_, t1) (_, t2) = f o t1 t2 in
        aux (Array.fold_left2 f' (f (Array.fold_left2 f o pms1 pms2) t1 t2) a1 a2) q1 q2
      | Proj (p1) :: q1, Proj (p2) :: q2 ->
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
  | f, (Proj (p)::s) -> zip (mkProj (p,f),s)
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

let safe_meta_value sigma ev =
  try Some (Evd.meta_value sigma ev)
  with Not_found -> None

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

  let get_parray evd e =
    match EConstr.kind evd e with
    | Array(_u,t,def,_ty) -> Parray.of_array t def
    | _ -> raise Not_found

  let mkInt env i =
    mkInt i

  let mkFloat env f =
    mkFloat f

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

let whd_state_gen flags env sigma =
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
    | Rel n when CClosure.RedFlags.red_set flags CClosure.RedFlags.fDELTA ->
      (match lookup_rel n env with
      | LocalDef (_,body,_) -> whrec (lift n body, stack)
      | _ -> fold ())
    | Var id when CClosure.RedFlags.red_set flags (CClosure.RedFlags.fVAR id) ->
      (match lookup_named id env with
      | LocalDef (_,body,_) ->
        whrec (body, stack)
      | _ -> fold ())
    | Evar ev -> fold ()
    | Meta ev ->
      (match safe_meta_value sigma ev with
      | Some body -> whrec (body, stack)
      | None -> fold ())
    | Const (c,u as const) ->
      reduction_effect_hook env sigma c
         (lazy (EConstr.to_constr sigma (Stack.zip sigma (x,fst (Stack.strip_app stack)))));
      if CClosure.RedFlags.red_set flags (CClosure.RedFlags.fCONST c) then
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
       | exception NotEvaluableConst _ -> fold ()
      else fold ()
    | Proj (p, c) when CClosure.RedFlags.red_projection flags p ->
      let stack' = (c, Stack.Proj (p) :: stack) in
      whrec stack'

    | LetIn (_,b,_,c) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fZETA ->
      whrec (apply_subst [b] sigma c stack)
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  ->
      whrec
        (f, Stack.append_app cl stack)
    | Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when CClosure.RedFlags.red_set flags CClosure.RedFlags.fBETA ->
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
      let use_match = CClosure.RedFlags.red_set flags CClosure.RedFlags.fMATCH in
      let use_fix = CClosure.RedFlags.red_set flags CClosure.RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case case::s') when use_match ->
          let r = apply_branch env sigma cstr args case in
          whrec (r, s')
        |args, (Stack.Proj (p)::s') when use_match ->
          whrec (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (f,s')::s'') when use_fix ->
          let x' = Stack.zip sigma (x, args) in
          let out_sk = s' @ (Stack.append_app [|x'|] s'') in
          whrec (reduce_and_refold_fix env sigma f out_sk)
        |_, (Stack.App _)::_ -> assert false
        |_, _ -> fold ()
      else fold ()

    | CoFix cofix ->
      if CClosure.RedFlags.red_set flags CClosure.RedFlags.fCOFIX then
        match Stack.strip_app stack with
        |args, ((Stack.Case _ |Stack.Proj _)::s') ->
          whrec (reduce_and_refold_cofix env sigma cofix stack)
        |_ -> fold ()
      else fold ()

    | Int _ | Float _ | Array _ ->
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
let local_whd_state_gen flags env sigma =
  let rec whrec (x, stack) =
    let c0 = EConstr.kind sigma x in
    let s = (EConstr.of_kind c0, stack) in
    match c0 with
    | LetIn (_,b,_,c) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fZETA ->
      whrec (apply_subst [b] sigma c stack)
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  -> whrec (f, Stack.append_app cl stack)
    | Lambda (_,_,c) ->
      (match Stack.decomp stack with
      | Some (a,m) when CClosure.RedFlags.red_set flags CClosure.RedFlags.fBETA ->
        whrec (apply_subst [a] sigma c m)
      | _ -> s)

    | Proj (p,c) when CClosure.RedFlags.red_projection flags p ->
      (whrec (c, Stack.Proj (p) :: stack))

    | Case (ci,u,pms,p,iv,d,lf) ->
      whrec (d, Stack.Case (ci,u,pms,p,iv,lf) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> s
      |Some (bef,arg,s') -> whrec (arg, Stack.Fix(f,bef)::s'))

    | Evar ev -> s
    | Meta ev ->
      (match safe_meta_value sigma ev with
        Some c -> whrec (c,stack)
      | None -> s)

    | Construct (cstr, u) ->
      let use_match = CClosure.RedFlags.red_set flags CClosure.RedFlags.fMATCH in
      let use_fix = CClosure.RedFlags.red_set flags CClosure.RedFlags.fFIX in
      if use_match || use_fix then
        match Stack.strip_app stack with
        |args, (Stack.Case case :: s') when use_match ->
          let r = apply_branch env sigma cstr args case in
          whrec (r, s')
        |args, (Stack.Proj (p) :: s') when use_match ->
          whrec (Stack.nth args (Projection.npars p + Projection.arg p), s')
        |args, (Stack.Fix (f,s')::s'') when use_fix ->
          let x' = Stack.zip sigma (x,args) in
          whrec (contract_fix sigma f, s' @ (Stack.append_app [|x'|] s''))
        |_, (Stack.App _)::_ -> assert false
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
      | Int _ | Float _ | Array _ -> s

  in
  whrec

let raw_whd_state_gen flags env =
  let f sigma s = whd_state_gen flags env sigma s in
  f

let stack_red_of_state_red f =
  let f env sigma x = EConstr.decompose_app sigma (Stack.zip sigma (f env sigma (x, Stack.empty))) in
  f

let red_of_state_red f env sigma x =
  Stack.zip sigma (f env sigma (x,Stack.empty))

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

let whd_const_state c e = raw_whd_state_gen CClosure.RedFlags.(mkflags [fCONST c]) e
let whd_const c = red_of_state_red (whd_const_state c)

let whd_delta_state e = raw_whd_state_gen CClosure.delta e
let whd_delta_stack = stack_red_of_state_red whd_delta_state
let whd_delta = red_of_state_red whd_delta_state

let whd_betadeltazeta_state = raw_whd_state_gen CClosure.betadeltazeta
let whd_betadeltazeta_stack = stack_red_of_state_red whd_betadeltazeta_state
let whd_betadeltazeta = red_of_state_red whd_betadeltazeta_state

(* 3. Iota reduction Functions *)

let whd_betaiota_state = local_whd_state_gen CClosure.betaiota
let whd_betaiota_stack = stack_red_of_state_red whd_betaiota_state
let whd_betaiota = red_of_state_red whd_betaiota_state

let whd_betaiotazeta_state = local_whd_state_gen CClosure.betaiotazeta
let whd_betaiotazeta_stack = stack_red_of_state_red whd_betaiotazeta_state
let whd_betaiotazeta = red_of_state_red whd_betaiotazeta_state

let whd_all_state = raw_whd_state_gen CClosure.all
let whd_all_stack = stack_red_of_state_red whd_all_state
let whd_all = red_of_state_red whd_all_state

let whd_allnolet_state = raw_whd_state_gen CClosure.allnolet
let whd_allnolet_stack = stack_red_of_state_red whd_allnolet_state
let whd_allnolet = red_of_state_red whd_allnolet_state

let is_head_evar env sigma c =
  let head, _ = whd_all_state env sigma (c,Stack.empty) in
  EConstr.isEvar sigma head

(* 4. Ad-hoc eta reduction *)

let shrink_eta sigma c =
  let rec whrec x = match EConstr.kind sigma x with
    | Cast (c, _, _) -> whrec c
    | Lambda (_, _, c) ->
      let (f, cl) = decompose_app_vect sigma (whrec c) in
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
    | Meta ev ->
      (match safe_meta_value sigma ev with
        Some c -> whrec c
      | None -> x)
    | App _ | Case _ | Fix _ | Construct _ | CoFix _ | Evar _ | Rel _ | Var _ | Sort _ | Prod _
    | LetIn _ | Const _  | Ind _ | Proj _ | Int _ | Float _ | Array _ -> x
  in
  whrec c

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
    EConstr.of_constr (CClosure.norm_val
      (Evarutil.create_clos_infos env sigma flgs)
      (CClosure.create_tab ())
      (CClosure.inject (EConstr.Unsafe.to_constr t)))
  with e when is_anomaly e -> user_err Pp.(str "Tried to normalize ill-typed term")

let clos_whd_flags flgs env sigma t =
  try
    EConstr.of_constr (CClosure.whd_val
      (Evarutil.create_clos_infos env sigma flgs)
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

let is_transparent e k =
  match Conv_oracle.get_strategy (Environ.oracle e) k with
  | Conv_oracle.Opaque -> false
  | _ -> true

(* Conversion utility functions *)

type conversion_test = Constraints.t -> Constraints.t

let pb_is_equal pb = pb == Reduction.CONV

let pb_equal = function
  | Reduction.CUMUL -> Reduction.CONV
  | Reduction.CONV -> Reduction.CONV

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

let f_conv ?l2r ?reds env ?evars x y =
  let inj = EConstr.Unsafe.to_constr in
  Reduction.conv ?l2r ?reds env ?evars (inj x) (inj y)

let f_conv_leq ?l2r ?reds env ?evars x y =
  let inj = EConstr.Unsafe.to_constr in
  Reduction.conv_leq ?l2r ?reds env ?evars (inj x) (inj y)

let test_trans_conversion (f: constr Reduction.extended_conversion_function) reds env sigma x y =
  try
    let evars ev = existential_opt_value0 sigma ev in
    let env = Environ.set_universes (Evd.universes sigma) env in
    let _ = f ~reds env ~evars x y in
    true
  with Reduction.NotConvertible -> false
    | e ->
      let e = Exninfo.capture e in
      report_anomaly e

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
    let env = Environ.set_universes (Evd.universes sigma) env in
    try f ~reds:ts env ~evars:(existential_opt_value0 sigma) x y; true
    with Reduction.NotConvertible -> false
    | UGraph.UniverseInconsistency _ -> false
    | e ->
      let e = Exninfo.capture e in
      report_anomaly e

let sigma_compare_sorts env pb s0 s1 sigma =
  match pb with
  | Reduction.CONV -> Evd.set_eq_sort env sigma s0 s1
  | Reduction.CUMUL -> Evd.set_leq_sort env sigma s0 s1

let sigma_compare_instances ~flex i0 i1 sigma =
  try Evd.set_eq_instances ~flex sigma i0 i1
  with Evd.UniversesDiffer
     | UGraph.UniverseInconsistency _ ->
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

let univproblem_compare_sorts env pb s0 s1 uset =
  let open UnivProblem in
  match pb with
  | Reduction.CONV -> UnivProblem.Set.add (UEq (s0, s1)) uset
  | Reduction.CUMUL -> UnivProblem.Set.add (ULe (s0, s1)) uset

let univproblem_compare_instances ~flex i0 i1 uset =
  UnivProblem.enforce_eq_instances_univs flex i0 i1 uset

let univproblem_check_inductive_instances cv_pb variances u u' uset =
  let open UnivProblem in
  let open Univ.Variance in
  let mk u = Sorts.sort_of_univ @@ Univ.Universe.make u in
  let fold cstr v u u' = match v with
  | Irrelevant -> Set.add (UWeak (u,u')) cstr
  | Covariant when cv_pb == Reduction.CUMUL -> Set.add (ULe (mk u, mk u')) cstr
  | Covariant | Invariant -> Set.add (UEq (mk u, mk u')) cstr
  in
  Array.fold_left3 fold uset
    variances (Univ.Instance.to_array u) (Univ.Instance.to_array u')

let univproblem_univ_state =
  let open Reduction in
  { compare_sorts = univproblem_compare_sorts;
    compare_instances = univproblem_compare_instances;
    compare_cumul_instances = univproblem_check_inductive_instances; }

let infer_conv_gen conv_fun ?(catch_incon=true) ?(pb=Reduction.CUMUL)
    ?(ts=TransparentState.full) env sigma x y =
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
        with UGraph.UniverseInconsistency _ | Evd.UniversesDiffer -> None
      in
      match ans with
      | Some sigma -> ans
      | None ->
        let x = EConstr.Unsafe.to_constr x in
        let y = EConstr.Unsafe.to_constr y in
        let env = Environ.set_universes (Evd.universes sigma) env in
        let sigma' =
          conv_fun pb ~l2r:false sigma ts
            env (sigma, sigma_univ_state) x y in
        Some sigma'
  with
  | Reduction.NotConvertible -> None
  | UGraph.UniverseInconsistency _ when catch_incon -> None
  | e ->
    let e = Exninfo.capture e in
    report_anomaly e

let infer_conv = infer_conv_gen (fun pb ~l2r sigma ->
      Reduction.generic_conv pb ~l2r (existential_opt_value0 sigma))

let infer_conv_ustate ?(catch_incon=true) ?(pb=Reduction.CUMUL)
    ?(ts=TransparentState.full) env sigma x y =
  try
      let ans = match pb with
      | Reduction.CUMUL ->
          EConstr.leq_constr_universes env sigma x y
      | Reduction.CONV ->
          EConstr.eq_constr_universes env sigma x y
      in
      match ans with
      | Some cstr -> Some cstr
      | None ->
        let x = EConstr.Unsafe.to_constr x in
        let y = EConstr.Unsafe.to_constr y in
        let env = Environ.set_universes (Evd.universes sigma) env in
        let cstr =
          Reduction.generic_conv pb ~l2r:false (existential_opt_value0 sigma) ts
            env (UnivProblem.Set.empty, univproblem_univ_state) x y in
        Some cstr
  with
  | Reduction.NotConvertible -> None
  | UGraph.UniverseInconsistency _ when catch_incon -> None
  | e ->
    let e = Exninfo.capture e in
    report_anomaly e

let vm_infer_conv ?(pb=Reduction.CUMUL) env sigma t1 t2 =
  infer_conv_gen (fun pb ~l2r sigma ts ->
      Vconv.vm_conv_gen pb (Evd.existential_opt_value0 sigma))
    ~catch_incon:true ~pb env sigma t1 t2

let native_conv_generic pb sigma t =
  let evars_of_evar_map sigma =
    { Nativelambda.evars_val = Evd.existential_opt_value0 sigma;
      Nativelambda.evars_metas = Evd.meta_type0 sigma }
  in
  Nativeconv.native_conv_gen pb (evars_of_evar_map sigma) t

let native_infer_conv ?(pb=Reduction.CUMUL) env sigma t1 t2 =
  infer_conv_gen (fun pb ~l2r sigma ts -> native_conv_generic pb sigma)
    ~catch_incon:true ~pb env sigma t1 t2

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let default_plain_instance_ident = Id.of_string "H"

type subst_fun = { sfun : metavariable -> EConstr.t }

(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance sigma s c = match s with
| None -> c
| Some s ->
  let rec irec n u = match EConstr.kind sigma u with
    | Meta p -> (try lift n (s.sfun p) with Not_found -> u)
    | App (f,l) when isCast sigma f ->
        let (f,_,t) = destCast sigma f in
        let l' = Array.Fun1.Smart.map irec n l in
        (match EConstr.kind sigma f with
        | Meta p ->
            (* Don't flatten application nodes: this is used to extract a
               proof-term from a proof-tree and we want to keep the structure
               of the proof-tree *)
            (try let g = s.sfun p in
            match EConstr.kind sigma g with
            | App _ ->
                let l' = Array.Fun1.Smart.map lift 1 l' in
                let r = Sorts.Relevant in (* TODO fix relevance *)
                let na = make_annot (Name default_plain_instance_ident) r in
                mkLetIn (na,g,t,mkApp(mkRel 1, l'))
            | _ -> mkApp (g,l')
            with Not_found -> mkApp (f,l'))
        | _ -> mkApp (irec n f,l'))
    | Cast (m,_,_) when isMeta sigma m ->
        (try lift n (s.sfun (destMeta sigma m)) with Not_found -> u)
    | _ ->
        map_with_binders sigma succ irec n u
  in
  irec 0 c

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

let instance env sigma s c =
  (* if s = [] then c else *)
  (* No need to compute contexts under binders as whd_betaiota is local *)
  let rec strongrec t = EConstr.map sigma strongrec (whd_betaiota env sigma t) in
  strongrec (plain_instance sigma s c)

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
    | _ -> raise Reduction.NotArity

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

let whd_betaiota_deltazeta_for_iota_state ts env sigma s =
  let all' = CClosure.RedFlags.red_add_transparent CClosure.all ts in
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
      Some (decompose_app_vect sigma c)
    | _ -> None
  in
  let rec whrec s =
    let (t, stack as s) = whd_state_gen CClosure.betaiota env sigma s in
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
      |args, (Stack.Proj p :: stack'') ->
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

(*************************************)
(* Metas *)

type meta_instance_subst = {
  sigma : Evd.evar_map;
  mutable cache : EConstr.t Metamap.t;
}

let create_meta_instance_subst sigma = {
  sigma;
  cache = Metamap.empty;
}

let eval_subst env subst =
  let rec ans mv =
    try Metamap.find mv subst.cache
    with Not_found ->
      match meta_opt_fvalue subst.sigma mv with
      | None -> mkMeta mv
      | Some (b, _) ->
        let metas =
          if Metaset.is_empty b.freemetas then None
          else Some { sfun = ans }
        in
        let res = instance env subst.sigma metas b.rebus in
        let () = subst.cache <- Metamap.add mv res subst.cache in
        res
  in
  { sfun = ans }

let meta_instance env subst b =
  let fm = b.freemetas in
  if Metaset.is_empty fm then b.rebus
  else
    let sfun = eval_subst env subst in
    instance env subst.sigma (Some sfun) b.rebus

let nf_meta env sigma c =
  let sigma = create_meta_instance_subst sigma in
  let cl = mk_freelisted c in
  meta_instance env sigma { cl with rebus = cl.rebus }

module Infer = struct

open Reduction

let infer_eq (univs, cstrs as cuniv) u u' =
  if UGraph.check_eq_sort univs u u' then cuniv
  else
    univs, (UnivSubst.enforce_eq_sort u u' cstrs)

let infer_leq (univs, cstrs as cuniv) u u' =
  if UGraph.check_leq_sort univs u u' then cuniv
  else
    let cstrs', _ = UnivSubst.enforce_leq_alg_sort u u' univs in
      univs, Univ.Constraints.union cstrs cstrs'

let infer_cmp_universes _env pb s0 s1 univs =
  match pb with
  | CUMUL -> infer_leq univs s0 s1
  | CONV -> infer_eq univs s0 s1

let infer_convert_instances ~flex u u' (univs,cstrs) =
  let cstrs' =
    if flex then
      if UGraph.check_eq_instances univs u u' then cstrs
      else raise NotConvertible
    else Univ.enforce_eq_instances u u' cstrs
  in (univs, cstrs')

let infer_inductive_instances cv_pb variance u1 u2 (univs,csts') =
  let csts = get_cumulativity_constraints cv_pb variance u1 u2 in
  (univs, Univ.Constraints.union csts csts')

let inferred_universes : (UGraph.t * Univ.Constraints.t) universe_compare =
  { compare_sorts = infer_cmp_universes;
    compare_instances = infer_convert_instances;
    compare_cumul_instances = infer_inductive_instances; }

end

let inferred_universes = Infer.inferred_universes
