(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Tac2expr
open Tac2print

(** Union find *)

module UF :
sig
type elt
type 'a t
val equal : elt -> elt -> bool
val create : unit -> 'a t
val fresh : 'a t -> elt
val find : elt -> 'a t -> (elt * 'a option)
val union : elt -> elt -> 'a t -> unit
val set : elt -> 'a -> 'a t -> unit
module Map : CSig.MapS with type key = elt
end
=
struct
type elt = int
let equal = Int.equal
module Map = Int.Map

type 'a node =
| Canon of int * 'a option
| Equiv of elt

type 'a t = {
  mutable uf_data : 'a node array;
  mutable uf_size : int;
}

let resize p =
  if Int.equal (Array.length p.uf_data) p.uf_size then begin
    let nsize = 2 * p.uf_size + 1 in
    let v = Array.make nsize (Equiv 0) in
    Array.blit p.uf_data 0 v 0 (Array.length p.uf_data);
    p.uf_data <- v;
  end

let create () = { uf_data = [||]; uf_size = 0 }

let fresh p =
  resize p;
  let n = p.uf_size in
  p.uf_data.(n) <- (Canon (1, None));
  p.uf_size <- n + 1;
  n

let rec lookup n p =
  let node = Array.get p.uf_data n in
  match node with
  | Canon (size, v) -> n, size, v
  | Equiv y ->
    let ((z, _, _) as res) = lookup y p in
    if not (Int.equal z y) then Array.set p.uf_data n (Equiv z);
    res

let find n p =
  let (x, _, v) = lookup n p in (x, v)

let union x y p =
  let ((x, size1, _) as xcan) = lookup x p in
  let ((y, size2, _) as ycan) = lookup y p in
  let xcan, ycan = if size1 < size2 then xcan, ycan else ycan, xcan in
  let x, _, xnode = xcan in
  let y, _, ynode = ycan in
  assert (Option.is_empty xnode);
  assert (Option.is_empty ynode);
  p.uf_data.(x) <- Equiv y;
  p.uf_data.(y) <- Canon (size1 + size2, None)

let set x v p =
  let (x, s, v') = lookup x p in
  assert (Option.is_empty v');
  p.uf_data.(x) <- Canon (s, Some v)

end

module TVar = struct
  type t = UF.elt
  let equal = UF.equal
  module Map = UF.Map
end

type mix_var =
| GVar of UF.elt
| LVar of int

type mix_type_scheme = int * mix_var glb_typexpr

(* Changing the APIs enough to get which variables are used in random genargs seems very hard
   so instead we use mutation to detect them *)
type used = { mutable used : bool }

type t = {
  env_var : (mix_type_scheme * used) Id.Map.t;
  (** Type schemes of bound variables *)
  env_cst : UF.elt glb_typexpr UF.t;
  (** Unification state *)
  env_als : UF.elt Id.Map.t ref;
  (** Map user-facing type variables to unification variables *)
  env_opn : bool;
  (** Accept unbound type variables *)
  env_rec : (KerName.t * int) Id.Map.t;
  (** Recursive type definitions *)
  env_strict : bool;
  (** True iff in strict mode *)
}

let empty_env ?(strict=true) () = {
  env_var = Id.Map.empty;
  env_cst = UF.create ();
  env_als = ref Id.Map.empty;
  env_opn = true;
  env_rec = Id.Map.empty;
  env_strict = strict;
}

let env_strict env = env.env_strict

let set_rec self env = { env with env_rec = self }

let reject_unbound_tvar env = { env with env_opn = false }

let find_rec_var id env = Id.Map.find_opt id env.env_rec

let mem_var id env = Id.Map.mem id env.env_var

let find_var id env =
  let t, used = Id.Map.find id env.env_var in
  used.used <- true;
  t

let is_used_var id env =
  let _, {used} = Id.Map.find id env.env_var in
  used

let bound_vars env = Id.Map.domain env.env_var

let get_variable0 mem var = match var with
| RelId qid ->
  let open Libnames in
  let open Locus in
  let id = qualid_basename qid in
  if qualid_is_ident qid && mem id then ArgVar CAst.(make ?loc:qid.CAst.loc id)
  else
    let kn =
      try Tac2env.locate_ltac qid
      with Not_found ->
        CErrors.user_err ?loc:qid.CAst.loc Pp.(str "Unbound value " ++ pr_qualid qid)
    in
    ArgArg kn
| AbsKn kn -> ArgArg kn

let get_variable env var =
  let mem id = Id.Map.mem id env.env_var in
  get_variable0 mem var

let env_name env =
  (* Generate names according to a provided environment *)
  let mk num =
    let base = num mod 26 in
    let rem = num / 26 in
    let name = String.make 1 (Char.chr (97 + base)) in
    let suff = if Int.equal rem 0 then "" else string_of_int rem in
    let name = name ^ suff in
    name
  in
  let fold id elt acc = UF.Map.add elt (Id.to_string id) acc in
  let vars = Id.Map.fold fold env.env_als.contents UF.Map.empty in
  let vars = ref vars in
  let rec fresh n =
    let name = mk n in
    if UF.Map.exists (fun _ name' -> String.equal name name') !vars then fresh (succ n)
    else name
  in
  fun n ->
    if UF.Map.mem n !vars then UF.Map.find n !vars
    else
      let ans = fresh 0 in
      let () = vars := UF.Map.add n ans !vars in
      ans

let fresh_id env = UF.fresh env.env_cst

let get_alias {CAst.loc;v=id} env =
  try Id.Map.find id env.env_als.contents
  with Not_found ->
    if env.env_opn then
      let n = fresh_id env in
      let () = env.env_als := Id.Map.add id n env.env_als.contents in
      n
    else CErrors.user_err ?loc Pp.(str "Unbound type parameter " ++ Id.print id)

let push_name id t env = match id with
| Anonymous -> env
| Name id -> { env with env_var = Id.Map.add id (t, {used=false}) env.env_var }

let push_ids ids env =
  let merge_fun _ fresh orig = match fresh, orig with
    | None, None -> assert false
    | Some x, _ -> Some (x, {used=false})
    | None, Some x -> Some x
  in
  { env with env_var = Id.Map.merge merge_fun ids env.env_var }

let rec subst_type subst (t : 'a glb_typexpr) = match t with
| GTypVar id -> subst id
| GTypArrow (t1, t2) -> GTypArrow (subst_type subst t1, subst_type subst t2)
| GTypRef (qid, args) ->
  GTypRef (qid, List.map (fun t -> subst_type subst t) args)

(** First-order unification algorithm *)
let is_unfoldable kn = match snd (Tac2env.interp_type kn) with
| GTydDef (Some _) -> true
| GTydDef None | GTydAlg _ | GTydRec _ | GTydOpn -> false

let unfold env kn args =
  let (nparams, def) = Tac2env.interp_type kn in
  let def = match def with
  | GTydDef (Some t) -> t
  | _ -> assert false
  in
  let args = Array.of_list args in
  let subst n = args.(n) in
  subst_type subst def

(** View function, allows to ensure head normal forms *)
let rec kind env t = match t with
| GTypVar id ->
  let (id, v) = UF.find id env.env_cst in
  begin match v with
  | None -> GTypVar id
  | Some t -> kind env t
  end
| GTypRef (Other kn, tl) ->
  if is_unfoldable kn then kind env (unfold env kn tl) else t
| GTypArrow _ | GTypRef (Tuple _, _) -> t

(** Normalize unification variables without unfolding type aliases *)
let rec nf env t = match t with
| GTypVar id ->
  let (id, v) = UF.find id env.env_cst in
  begin match v with
  | None -> GTypVar id
  | Some t -> nf env t
  end
| GTypRef (kn, tl) ->
  let tl = List.map (fun t -> nf env t) tl in
  GTypRef (kn, tl)
| GTypArrow (t, u) ->
  let t = nf env t in
  let u = nf env u in
  GTypArrow (t, u)

let pr_glbtype env t =
  let t = nf env t in
  let name = env_name env in
  pr_glbtype name t

let normalize env (count, vars) (t : TVar.t glb_typexpr) =
  let get_var id =
    try UF.Map.find id !vars
    with Not_found ->
      let () = assert env.env_opn in
      let n = GTypVar !count in
      let () = incr count in
      let () = vars := UF.Map.add id n !vars in
      n
  in
  let rec subst id = match UF.find id env.env_cst with
  | id, None -> get_var id
  | _, Some t -> subst_type subst t
  in
  subst_type subst t

exception Occur

let rec occur_check env id t = match kind env t with
| GTypVar id' -> if TVar.equal id id' then raise Occur
| GTypArrow (t1, t2) ->
  let () = occur_check env id t1 in
  occur_check env id t2
| GTypRef (kn, tl) ->
  List.iter (fun t -> occur_check env id t) tl

exception CannotUnify of TVar.t glb_typexpr * TVar.t glb_typexpr

let unify_var env id t = match kind env t with
| GTypVar id' ->
  if not (TVar.equal id id') then UF.union id id' env.env_cst
| GTypArrow _ | GTypRef _ ->
  try
    let () = occur_check env id t in
    UF.set id t env.env_cst
  with Occur -> raise (CannotUnify (GTypVar id, t))

let eq_or_tuple eq t1 t2 = match t1, t2 with
| Tuple n1, Tuple n2 -> Int.equal n1 n2
| Other o1, Other o2 -> eq o1 o2
| _ -> false

let rec unify0 env t1 t2 = match kind env t1, kind env t2 with
| GTypVar id, _ -> unify_var env id t2
| _, GTypVar id -> unify_var env id t1
| GTypArrow (t1, u1), GTypArrow (t2, u2) ->
  let () = unify0 env t1 t2 in
  unify0 env u1 u2
| GTypRef (kn1, tl1), GTypRef (kn2, tl2) ->
  if eq_or_tuple KerName.equal kn1 kn2 then
    List.iter2 (fun t1 t2 -> unify0 env t1 t2) tl1 tl2
  else raise (CannotUnify (t1, t2))
| _ -> raise (CannotUnify (t1, t2))

let unify ?loc env t1 t2 =
  try unify0 env t1 t2
  with CannotUnify (u1, u2) ->
    CErrors.user_err ?loc Pp.(str "This expression has type" ++ spc () ++ pr_glbtype env t1 ++
      spc () ++ str "but an expression was expected of type" ++ spc () ++ pr_glbtype env t2)

let unify_arrow ?loc env ft args =
  let ft0 = ft in
  let rec iter ft args is_fun = match kind env ft, args with
  | t, [] -> t
  | GTypArrow (t1, ft), (loc, t2) :: args ->
    let () = unify ?loc env t2 t1 in
    iter ft args true
  | GTypVar id, (_, t) :: args ->
    let ft = GTypVar (fresh_id env) in
    let () = unify ?loc env (GTypVar id) (GTypArrow (t, ft)) in
    iter ft args true
  | GTypRef _, _ :: _ ->
    if is_fun then
      CErrors.user_err ?loc Pp.(str "This function has type" ++ spc () ++ pr_glbtype env ft0 ++
        spc () ++ str "and is applied to too many arguments")
    else
      CErrors.user_err ?loc Pp.(str "This expression has type" ++ spc () ++ pr_glbtype env ft0 ++
        spc () ++ str "and is not a function")
  in
  iter ft args false

let rec fv_type f t accu = match t with
| GTypVar id -> f id accu
| GTypArrow (t1, t2) -> fv_type f t1 (fv_type f t2 accu)
| GTypRef (kn, tl) -> List.fold_left (fun accu t -> fv_type f t accu) accu tl

let fv_env env =
  let rec f id accu = match UF.find id env.env_cst with
  | id, None -> UF.Map.add id () accu
  | _, Some t -> fv_type f t accu
  in
  let fold_var id ((_, t), _) accu =
    let fmix id accu = match id with
    | LVar _ -> accu
    | GVar id -> f id accu
    in
    fv_type fmix t accu
  in
  let fv_var = Id.Map.fold fold_var env.env_var UF.Map.empty in
  let fold_als _ id accu = f id accu in
  Id.Map.fold fold_als !(env.env_als) fv_var

let abstract_var env (t : TVar.t glb_typexpr) : mix_type_scheme =
  let fv = fv_env env in
  let count = ref 0 in
  let vars = ref UF.Map.empty in
  let rec subst id =
    let (id, t) = UF.find id env.env_cst in
    match t with
    | None ->
      if UF.Map.mem id fv then GTypVar (GVar id)
      else
        begin try UF.Map.find id !vars
        with Not_found ->
          let n = !count in
          let var = GTypVar (LVar n) in
          let () = incr count in
          let () = vars := UF.Map.add id var !vars in
          var
        end
    | Some t -> subst_type subst t
  in
  let t = subst_type subst t in
  (!count, t)

let monomorphic (t : TVar.t glb_typexpr) : mix_type_scheme =
  let subst id = GTypVar (GVar id) in
  (0, subst_type subst t)

let polymorphic ((n, t) : type_scheme) : mix_type_scheme =
  let subst id = GTypVar (LVar id) in
  (n, subst_type subst t)
