(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Util
open Names
open Libnames
open Table
open Miniml
(*i*)

(*s Exceptions. *)

exception Found
exception Impossible

(*S Names operations. *)

let anonymous_name = Id.of_string "x"
let dummy_name = Id.of_string "_"

let anonymous = Id anonymous_name

let id_of_name = function
  | Name.Anonymous -> anonymous_name
  | Name.Name id when Id.equal id dummy_name -> anonymous_name
  | Name.Name id -> id

let id_of_mlid = function
  | Dummy -> dummy_name
  | Id id -> id
  | Tmp id -> id

let tmp_id = function
  | Id id -> Tmp id
  | a -> a

let is_tmp = function Tmp _ -> true | _ -> false

(*S Operations upon ML types (with meta). *)

let meta_count = ref 0

let reset_meta_count () = meta_count := 0

let new_meta _ =
  incr meta_count;
  Tmeta {id = !meta_count; contents = None}

let rec eq_ml_type t1 t2 = match t1, t2 with
| Tarr (tl1, tr1), Tarr (tl2, tr2) ->
  eq_ml_type tl1 tl2 && eq_ml_type tr1 tr2
| Tglob (gr1, t1), Tglob (gr2, t2) ->
  GlobRef.CanOrd.equal gr1 gr2 && List.equal eq_ml_type t1 t2
| Tvar i1, Tvar i2 -> Int.equal i1 i2
| Tvar' i1, Tvar' i2 -> Int.equal i1 i2
| Tmeta m1, Tmeta m2 -> eq_ml_meta m1 m2
| Tdummy k1, Tdummy k2 -> k1 == k2
| Tunknown, Tunknown -> true
| Taxiom, Taxiom -> true
| (Tarr _ | Tglob _ | Tvar _ | Tvar' _ | Tmeta _ | Tdummy _ | Tunknown | Taxiom), _
  -> false

and eq_ml_meta m1 m2 =
 Int.equal m1.id m2.id && Option.equal eq_ml_type m1.contents m2.contents

(* Simultaneous substitution of [[Tvar 1; ... ; Tvar n]] by [l] in a ML type. *)

let type_subst_list l t =
  let rec subst t = match t with
    | Tvar j -> List.nth l (j-1)
    | Tmeta {contents=None} -> t
    | Tmeta {contents=Some u} -> subst u
    | Tarr (a,b) -> Tarr (subst a, subst b)
    | Tglob (r, l) -> Tglob (r, List.map subst l)
    | a -> a
  in subst t

(* Simultaneous substitution of [[|Tvar 1; ... ; Tvar n|]] by [v] in a ML type. *)

let type_subst_vect v t =
  let rec subst t = match t with
    | Tvar j -> v.(j-1)
    | Tmeta {contents=None} -> t
    | Tmeta {contents=Some u} -> subst u
    | Tarr (a,b) -> Tarr (subst a, subst b)
    | Tglob (r, l) -> Tglob (r, List.map subst l)
    | a -> a
  in subst t

(*s From a type schema to a type. All [Tvar] become fresh [Tmeta]. *)

let instantiation (nb,t) = type_subst_vect (Array.init nb new_meta) t

(*s Occur-check of a free meta in a type *)

let rec type_occurs alpha t =
  match t with
  | Tmeta {id=beta; contents=None} -> Int.equal alpha beta
  | Tmeta {contents=Some u} -> type_occurs alpha u
  | Tarr (t1, t2) -> type_occurs alpha t1 || type_occurs alpha t2
  | Tglob (r,l) -> List.exists (type_occurs alpha) l
  | (Tdummy _ | Tvar _ | Tvar' _ | Taxiom | Tunknown) -> false

(*s Most General Unificator *)

let rec mgu = function
  | Tmeta m, Tmeta m' when Int.equal m.id m'.id -> ()
  | Tmeta m, t | t, Tmeta m ->
    (match m.contents with
      | Some u -> mgu (u, t)
      | None when type_occurs m.id t -> raise Impossible
      | None -> m.contents <- Some t)
  | Tarr(a, b), Tarr(a', b') ->
      mgu (a, a'); mgu (b, b')
  | Tglob (r,l), Tglob (r',l') when GlobRef.CanOrd.equal r r' ->
       List.iter mgu (List.combine l l')
  | Tdummy _, Tdummy _ -> ()
  | Tvar i, Tvar j when Int.equal i j -> ()
  | Tvar' i, Tvar' j when  Int.equal i j -> ()
  | Tunknown, Tunknown -> ()
  | Taxiom, Taxiom -> ()
  | _ -> raise Impossible

let skip_typing () = lang () == Scheme || is_extrcompute ()

let needs_magic p =
  if skip_typing () then false
  else try mgu p; false with Impossible -> true

let put_magic_if b a = if b then MLmagic a else a

let put_magic p a = if needs_magic p then MLmagic a else a

let generalizable a =
  lang () != Ocaml ||
    match a with
      | MLapp _ -> false
      | _ -> true (* TODO, this is just an approximation for the moment *)

(*S ML type env. *)

module Mlenv = struct

  let meta_cmp m m' = compare m.id m'.id
  module Metaset = Set.Make(struct type t = ml_meta let compare = meta_cmp end)

  (* Main MLenv type. [env] is the real environment, whereas [free]
     (tries to) record the free meta variables occurring in [env]. *)

  type t = { env : ml_schema list; mutable free : Metaset.t}

  (* Empty environment. *)

  let empty = { env = []; free = Metaset.empty }

  (* [get] returns a instantiated copy of the n-th most recently added
     type in the environment. *)

  let get mle n =
    assert (List.length mle.env >= n);
    instantiation (List.nth mle.env (n-1))

  (* [find_free] finds the free meta in a type. *)

  let rec find_free set = function
    | Tmeta m when Option.is_empty m.contents -> Metaset.add m set
    | Tmeta {contents = Some t} -> find_free set t
    | Tarr (a,b) -> find_free (find_free set a) b
    | Tglob (_,l) -> List.fold_left find_free set l
    | _ -> set

  (* The [free] set of an environment can be outdate after
     some unifications. [clean_free] takes care of that. *)

  let clean_free mle =
    let rem = ref Metaset.empty
    and add = ref Metaset.empty in
    let clean m = match m.contents with
      | None -> ()
      | Some u -> rem := Metaset.add m !rem; add := find_free !add u
    in
    Metaset.iter clean mle.free;
    mle.free <- Metaset.union (Metaset.diff mle.free !rem) !add

  (* From a type to a type schema. If a [Tmeta] is still uninstantiated
     and does appears in the [mle], then it becomes a [Tvar]. *)

  let generalization mle t =
    let c = ref 0 in
    let map = ref (Int.Map.empty : int Int.Map.t) in
    let add_new i = incr c; map := Int.Map.add i !c !map; !c in
    let rec meta2var t = match t with
      | Tmeta {contents=Some u} -> meta2var u
      | Tmeta ({id=i} as m) ->
          (try Tvar (Int.Map.find i !map)
           with Not_found ->
             if Metaset.mem m mle.free then t
             else Tvar (add_new i))
      | Tarr (t1,t2) -> Tarr (meta2var t1, meta2var t2)
      | Tglob (r,l) -> Tglob (r, List.map meta2var l)
      | t -> t
    in !c, meta2var t

  (* Adding a type in an environment, after generalizing. *)

  let push_gen mle t =
    clean_free mle;
    { env = generalization mle t :: mle.env; free = mle.free }

  (* Adding a type with no [Tvar], hence no generalization needed. *)

  let push_type mle t =
    { env = (0,t) :: mle.env; free = find_free mle.free t}

  (* Adding a type with no [Tvar] nor [Tmeta]. *)

  let push_std_type mle t =
    { env = (0,t) :: mle.env; free = mle.free}

end

(*S Operations upon ML types (without meta). *)

(*s Does a section path occur in a ML type ? *)

let rec type_mem_kn kn = function
  | Tmeta {contents = Some t} -> type_mem_kn kn t
  | Tglob (r,l) -> occur_kn_in_ref kn r || List.exists (type_mem_kn kn) l
  | Tarr (a,b) -> (type_mem_kn kn a) || (type_mem_kn kn b)
  | _ -> false

(*s Greatest variable occurring in [t]. *)

let type_maxvar t =
  let rec parse n = function
    | Tmeta {contents = Some t} -> parse n t
    | Tvar i -> max i n
    | Tarr (a,b) -> parse (parse n a) b
    | Tglob (_,l) -> List.fold_left parse n l
    | _ -> n
  in parse 0 t

(*s From [a -> b -> c] to [[a;b],c]. *)

let rec type_decomp = function
  | Tmeta {contents = Some t} -> type_decomp t
  | Tarr (a,b) -> let l,h = type_decomp b in a::l, h
  | a -> [],a

(*s The converse: From [[a;b],c] to [a -> b -> c]. *)

let rec type_recomp (l,t) = match l with
  | [] -> t
  | a::l -> Tarr (a, type_recomp (l,t))

(*s Translating [Tvar] to [Tvar'] to avoid clash. *)

let rec var2var' = function
  | Tmeta {contents = Some t} -> var2var' t
  | Tvar i -> Tvar' i
  | Tarr (a,b) -> Tarr (var2var' a, var2var' b)
  | Tglob (r,l) -> Tglob (r, List.map var2var' l)
  | a -> a

type abbrev_map = GlobRef.t -> ml_type option

(*s Delta-reduction of type constants everywhere in a ML type [t].
   [env] is a function of type [ml_type_env]. *)

let type_expand env t =
  let rec expand = function
    | Tmeta {contents = Some t} -> expand t
    | Tglob (r,l) ->
        (match env r with
           | Some mlt -> expand (type_subst_list l mlt)
           | None -> Tglob (r, List.map expand l))
    | Tarr (a,b) -> Tarr (expand a, expand b)
    | a -> a
  in if Table.type_expand () then expand t else t

let type_simpl = type_expand (fun _ -> None)

(*s Generating a signature from a ML type. *)

let type_to_sign env t = match type_expand env t with
  | Tdummy d when not (conservative_types ()) -> Kill d
  | _ -> Keep

let type_to_signature env t =
  let rec f = function
    | Tmeta {contents = Some t} -> f t
    | Tarr (Tdummy d, b) when not (conservative_types ())  -> Kill d :: f b
    | Tarr (_, b) -> Keep :: f b
    | _ -> []
  in f (type_expand env t)

let isKill = function Kill _ -> true | _ -> false

let isTdummy = function Tdummy _ -> true | _ -> false

let isMLdummy = function MLdummy _ -> true | _ -> false

let sign_of_id = function
  | Dummy -> Kill Kprop
  | (Id _ | Tmp _) -> Keep

(* Classification of signatures *)

type sign_kind =
  | EmptySig
  | NonLogicalSig (* at least a [Keep] *)
  | SafeLogicalSig (* only [Kill Ktype] *)
  | UnsafeLogicalSig (* No [Keep], not all [Kill Ktype] *)

let rec sign_kind = function
  | [] -> EmptySig
  | Keep :: _ -> NonLogicalSig
  | Kill k :: s ->
     match k, sign_kind s with
     | _, NonLogicalSig -> NonLogicalSig
     | Ktype, (SafeLogicalSig | EmptySig) -> SafeLogicalSig
     | _, _ -> UnsafeLogicalSig

(* Removing the final [Keep] in a signature *)

let rec sign_no_final_keeps = function
  | [] -> []
  | k :: s ->
     match k, sign_no_final_keeps s with
     | Keep, [] -> []
     | k, l -> k::l

(*s Removing [Tdummy] from the top level of a ML type. *)

let type_expunge_from_sign env s t =
  let rec expunge s t = match s, t with
    | [], _ -> t
    | Keep :: s, Tarr(a,b) -> Tarr (a, expunge s b)
    | Kill _ :: s, Tarr(a,b) -> expunge s b
    | _, Tmeta {contents = Some t} -> expunge s t
    | _, Tglob (r,l) ->
       (match env r with
        | Some mlt -> expunge s (type_subst_list l mlt)
        | None -> assert false)
    | _ -> assert false
  in
  let t = expunge (sign_no_final_keeps s) t in
  if lang () != Haskell && sign_kind s == UnsafeLogicalSig then
    Tarr (Tdummy Kprop, t)
  else t

let type_expunge env t =
  type_expunge_from_sign env (type_to_signature env t) t

(*S Generic functions over ML ast terms. *)

let mlapp f a = if List.is_empty a then f else MLapp (f,a)

(** Equality *)

let eq_ml_ident i1 i2 = match i1, i2 with
| Dummy, Dummy -> true
| Id id1, Id id2 -> Id.equal id1 id2
| Tmp id1, Tmp id2 -> Id.equal id1 id2
| Dummy, (Id _ | Tmp _)
| Id _, (Dummy | Tmp _)
| Tmp _, (Dummy | Id _)
  -> false

let rec eq_ml_ast t1 t2 = match t1, t2 with
| MLrel i1, MLrel i2 ->
  Int.equal i1 i2
| MLapp (f1, t1), MLapp (f2, t2) ->
  eq_ml_ast f1 f2 && List.equal eq_ml_ast t1 t2
| MLlam (na1, t1), MLlam (na2, t2) ->
  eq_ml_ident na1 na2 && eq_ml_ast t1 t2
| MLletin (na1, c1, t1), MLletin (na2, c2, t2) ->
  eq_ml_ident na1 na2 && eq_ml_ast c1 c2 && eq_ml_ast t1 t2
| MLglob gr1, MLglob gr2 -> GlobRef.CanOrd.equal gr1 gr2
| MLcons (t1, gr1, c1), MLcons (t2, gr2, c2) ->
  eq_ml_type t1 t2 && GlobRef.CanOrd.equal gr1 gr2 && List.equal eq_ml_ast c1 c2
| MLtuple t1, MLtuple t2 ->
  List.equal eq_ml_ast t1 t2
| MLcase (t1, c1, p1), MLcase (t2, c2, p2) ->
  eq_ml_type t1 t2 && eq_ml_ast c1 c2 && Array.equal eq_ml_branch p1 p2
| MLfix (i1, id1, t1), MLfix (i2, id2, t2) ->
  Int.equal i1 i2 && Array.equal Id.equal id1 id2 && Array.equal eq_ml_ast t1 t2
| MLexn e1, MLexn e2 -> String.equal e1 e2
| MLdummy k1, MLdummy k2 -> k1 == k2
| MLaxiom _, MLaxiom _ -> true (* ignore the name of the axiom *)
| MLmagic t1, MLmagic t2 -> eq_ml_ast t1 t2
| MLuint i1, MLuint i2 -> Uint63.equal i1 i2
| MLfloat f1, MLfloat f2 -> Float64.equal f1 f2
| MLstring s1, MLstring s2 -> Pstring.equal s1 s2
| MLparray (t1,def1), MLparray (t2, def2) -> Array.equal eq_ml_ast t1 t2 && eq_ml_ast def1 def2
| (MLrel _|MLapp _|MLlam _|MLletin _|MLglob _|MLcons _
  |MLtuple _|MLcase _|MLfix _|MLexn _|MLdummy _|MLaxiom _
  | MLmagic _| MLuint _| MLfloat _| MLstring _| MLparray _), _
  -> false

and eq_ml_pattern p1 p2 = match p1, p2 with
| Pcons (gr1, p1), Pcons (gr2, p2) ->
  GlobRef.CanOrd.equal gr1 gr2 && List.equal eq_ml_pattern p1 p2
| Ptuple p1, Ptuple p2 ->
  List.equal eq_ml_pattern p1 p2
| Prel i1, Prel i2 ->
  Int.equal i1 i2
| Pwild, Pwild -> true
| Pusual gr1, Pusual gr2 -> GlobRef.CanOrd.equal gr1 gr2
| _ -> false

and eq_ml_branch (id1, p1, t1) (id2, p2, t2) =
  List.equal eq_ml_ident id1 id2 &&
  eq_ml_pattern p1 p2 &&
  eq_ml_ast t1 t2

(*s [ast_iter_rel f t] applies [f] on every [MLrel] in t. It takes care
   of the number of bingings crossed before reaching the [MLrel]. *)

let ast_iter_rel f =
  let rec iter n = function
    | MLrel i -> f (i-n)
    | MLlam (_,a) -> iter (n+1) a
    | MLletin (_,a,b) -> iter n a; iter (n+1) b
    | MLcase (_,a,v) ->
        iter n a; Array.iter (fun (l,_,t) -> iter (n + (List.length l)) t) v
    | MLfix (_,ids,v) -> let k = Array.length ids in Array.iter (iter (n+k)) v
    | MLapp (a,l) -> iter n a; List.iter (iter n) l
    | MLcons (_,_,l) | MLtuple l ->  List.iter (iter n) l
    | MLmagic a -> iter n a
    | MLparray (t,def) -> Array.iter (iter n) t; iter n def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> ()
  in iter 0

(*s Map over asts. *)

let ast_map_branch f (c,ids,a) = (c,ids,f a)

(* Warning: in [ast_map] we assume that [f] does not change the type
   of [MLcons] and of [MLcase] heads *)

let ast_map f = function
  | MLlam (i,a) -> MLlam (i, f a)
  | MLletin (i,a,b) -> MLletin (i, f a, f b)
  | MLcase (typ,a,v) -> MLcase (typ,f a, Array.map (ast_map_branch f) v)
  | MLfix (i,ids,v) -> MLfix (i, ids, Array.map f v)
  | MLapp (a,l) -> MLapp (f a, List.map f l)
  | MLcons (typ,c,l) -> MLcons (typ,c, List.map f l)
  | MLtuple l -> MLtuple (List.map f l)
  | MLmagic a -> MLmagic (f a)
  | MLparray (t,def) -> MLparray (Array.map f t, f def)
  | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
  | MLuint _ | MLfloat _ | MLstring _ as a -> a

(*s Map over asts, with binding depth as parameter. *)

let ast_map_lift_branch f n (ids,p,a) = (ids,p, f (n+(List.length ids)) a)

(* Same warning as for [ast_map]... *)

let ast_map_lift f n = function
  | MLlam (i,a) -> MLlam (i, f (n+1) a)
  | MLletin (i,a,b) -> MLletin (i, f n a, f (n+1) b)
  | MLcase (typ,a,v) -> MLcase (typ,f n a,Array.map (ast_map_lift_branch f n) v)
  | MLfix (i,ids,v) ->
      let k = Array.length ids in MLfix (i,ids,Array.map (f (k+n)) v)
  | MLapp (a,l) -> MLapp (f n a, List.map (f n) l)
  | MLcons (typ,c,l) -> MLcons (typ,c, List.map (f n) l)
  | MLtuple l -> MLtuple (List.map (f n) l)
  | MLmagic a -> MLmagic (f n a)
  | MLparray (t,def) -> MLparray (Array.map (f n) t, f n def)
  | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
  | MLuint _ | MLfloat _ | MLstring _ as a -> a

(*s Iter over asts. *)

let ast_iter_branch f (c,ids,a) = f a

let ast_iter f = function
  | MLlam (i,a) -> f a
  | MLletin (i,a,b) -> f a; f b
  | MLcase (_,a,v) -> f a; Array.iter (ast_iter_branch f) v
  | MLfix (i,ids,v) -> Array.iter f v
  | MLapp (a,l) -> f a; List.iter f l
  | MLcons (_,_,l) | MLtuple l -> List.iter f l
  | MLmagic a -> f a
  | MLparray (t,def) -> Array.iter f t; f def
  | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
  | MLuint _ | MLfloat _ | MLstring _ -> ()

(*S Operations concerning De Bruijn indices. *)

(*s [ast_occurs k t] returns [true] if [(Rel k)] occurs in [t]. *)

let ast_occurs k t =
  try
    ast_iter_rel (fun i -> if Int.equal i k then raise Found) t; false
  with Found -> true

(*s [occurs_itvl k k' t] returns [true] if there is a [(Rel i)]
   in [t] with [k<=i<=k'] *)

let ast_occurs_itvl k k' t =
  try
    ast_iter_rel (fun i -> if (k <= i) && (i <= k') then raise Found) t; false
  with Found -> true

(* Number of occurrences of [Rel 1] in [t], with special treatment of match:
   occurrences in different branches aren't added, but we rather use max. *)

let nb_occur_match =
  let rec nb k = function
    | MLrel i -> if Int.equal i k then 1 else 0
    | MLcase(_,a,v) ->
        (nb k a) +
        Array.fold_left
          (fun r (ids,_,a) -> max r (nb (k+(List.length ids)) a)) 0 v
    | MLletin (_,a,b) -> (nb k a) + (nb (k+1) b)
    | MLfix (_,ids,v) -> let k = k+(Array.length ids) in
      Array.fold_left (fun r a -> r+(nb k a)) 0 v
    | MLlam (_,a) -> nb (k+1) a
    | MLapp (a,l) -> List.fold_left (fun r a -> r+(nb k a)) (nb k a) l
    | MLcons (_,_,l) | MLtuple l -> List.fold_left (fun r a -> r+(nb k a)) 0 l
    | MLmagic a -> nb k a
    | MLparray (t,def) -> Array.fold_left (fun r a -> r+(nb k a)) 0 t + nb k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> 0
  in nb 1

(* Replace unused variables by _ *)

let dump_unused_vars a =
  let rec ren env a = match a with
    | MLrel i ->
       let () = (List.nth env (i-1)) := true in a

    | MLlam (id,b) ->
       let occ_id = ref false in
       let b' = ren (occ_id::env) b in
       if !occ_id then if b' == b then a else MLlam(id,b')
       else MLlam(Dummy,b')

    | MLletin (id,b,c) ->
       let occ_id = ref false in
       let b' = ren env b in
       let c' = ren (occ_id::env) c in
       if !occ_id then
         if b' == b && c' == c then a else MLletin(id,b',c')
       else
         (* 'let' without occurrence: shouldn't happen after simpl *)
         MLletin(Dummy,b',c')

    | MLcase (t,e,br) ->
       let e' = ren env e in
       let br' = Array.Smart.map (ren_branch env) br in
       if e' == e && br' == br then a else MLcase (t,e',br')

    | MLfix (i,ids,v) ->
       let env' = List.init (Array.length ids) (fun _ -> ref false) @ env in
       let v' = Array.Smart.map (ren env') v in
       if v' == v then a else MLfix (i,ids,v')

    | MLapp (b,l) ->
       let b' = ren env b and l' = List.Smart.map (ren env) l in
       if b' == b && l' == l then a else MLapp (b',l')

    | MLcons(t,r,l) ->
       let l' = List.Smart.map (ren env) l in
       if l' == l then a else MLcons (t,r,l')

    | MLtuple l ->
       let l' = List.Smart.map (ren env) l in
       if l' == l then a else MLtuple l'

    | MLmagic b ->
       let b' = ren env b in
       if b' == b then a else MLmagic b'

    | MLparray(t,def) ->
       let t' = Array.Smart.map (ren env) t in
       let def' = ren env def in
       if def' == def && t' == t then a else MLparray(t',def')

    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> a

    and ren_branch env ((ids,p,b) as tr) =
      let occs = List.map (fun _ -> ref false) ids in
      let b' = ren (List.rev_append occs env) b in
      let ids' =
        List.map2
          (fun id occ -> if !occ then id else Dummy)
          ids occs
      in
      if b' == b && List.equal eq_ml_ident ids ids' then tr
      else (ids',p,b')
  in
  ren [] a

(*s Lifting on terms.
    [ast_lift k t] lifts the binding depth of [t] across [k] bindings. *)

let ast_lift k t =
  let rec liftrec n = function
    | MLrel i as a -> if i-n < 1 then a else MLrel (i+k)
    | a -> ast_map_lift liftrec n a
  in if Int.equal k 0 then t else liftrec 0 t

let ast_pop t = ast_lift (-1) t

(*s [permut_rels k k' c] translates [Rel 1 ... Rel k] to [Rel (k'+1) ...
  Rel (k'+k)] and [Rel (k+1) ... Rel (k+k')] to [Rel 1 ... Rel k'] *)

let permut_rels k k' =
  let rec permut n = function
    | MLrel i as a ->
        let i' = i-n in
        if i'<1 || i'>k+k' then a
        else if i'<=k then MLrel (i+k')
        else MLrel (i-k)
    | a -> ast_map_lift permut n a
  in permut 0

(*s Substitution. [ml_subst e t] substitutes [e] for [Rel 1] in [t].
    Lifting (of one binder) is done at the same time. *)

let ast_subst e =
  let rec subst n = function
    | MLrel i as a ->
        let i' = i-n in
        if Int.equal i' 1 then ast_lift n e
        else if i'<1 then a
        else MLrel (i-1)
    | a -> ast_map_lift subst n a
  in subst 0

(*s Generalized substitution.
   [gen_subst v d t] applies to [t] the substitution coded in the
   [v] array: [(Rel i)] becomes [v.(i-1)]. [d] is the correction applies
   to [Rel] greater than [Array.length v]. *)

let gen_subst v d t =
  let rec subst n = function
    | MLrel i as a ->
        let i'= i-n in
        if i' < 1 then a
        else if i' <= Array.length v then
          match v.(i'-1) with
            | None -> assert false
            | Some u -> ast_lift n u
        else MLrel (i+d)
    | a -> ast_map_lift subst n a
  in subst 0 t

(*S Operations concerning match patterns *)

let is_basic_pattern = function
  | Prel _ | Pwild -> true
  | Pusual _ | Pcons _ | Ptuple _ -> false

let has_deep_pattern br =
  let deep = function
    | Pcons (_,l) | Ptuple l -> not (List.for_all is_basic_pattern l)
    | Pusual _ | Prel _ | Pwild -> false
  in
  Array.exists (function (_,pat,_) -> deep pat) br

let is_regular_match br =
  if Array.is_empty br then false (* empty match becomes MLexn *)
  else
    try
      let get_r (ids,pat,c) =
        match pat with
          | Pusual r -> r
          | Pcons (r,l) ->
            let is_rel i = function Prel j -> Int.equal i j | _ -> false in
            if not (List.for_all_i is_rel 1 (List.rev l))
            then raise Impossible;
            r
          | _ -> raise Impossible
      in
      let ind = match get_r br.(0) with
        | GlobRef.ConstructRef (ind,_) -> ind
        | _ -> raise Impossible
      in
      let is_ref i tr = match get_r tr with
      | GlobRef.ConstructRef (ind', j) -> Ind.CanOrd.equal ind ind' && Int.equal j (i + 1)
      | _ -> false
      in
      Array.for_all_i is_ref 0 br
    with Impossible -> false

(*S Operations concerning lambdas. *)

(*s [collect_lams MLlam(id1,...MLlam(idn,t)...)] returns
    [[idn;...;id1]] and the term [t]. *)

let collect_lams =
  let rec collect acc = function
    | MLlam(id,t) -> collect (id::acc) t
    | x           -> acc,x
  in collect []

(*s [collect_n_lams] does the same for a precise number of [MLlam]. *)

let collect_n_lams =
  let rec collect acc n t =
    if Int.equal n 0 then acc,t
    else match t with
      | MLlam(id,t) -> collect (id::acc) (n-1) t
      | _ -> assert false
  in collect []

(*s [remove_n_lams] just removes some [MLlam]. *)

let rec remove_n_lams n t =
  if Int.equal n 0 then t
  else match t with
      | MLlam(_,t) -> remove_n_lams (n-1) t
      | _ -> assert false

(*s [nb_lams] gives the number of head [MLlam]. *)

let rec nb_lams = function
  | MLlam(_,t) -> succ (nb_lams t)
  | _ -> 0

(*s [named_lams] does the converse of [collect_lams]. *)

let rec named_lams ids a = match ids with
  | [] -> a
  | id :: ids -> named_lams ids (MLlam (id,a))

(*s The same for a specific identifier (resp. anonymous, dummy) *)

let rec many_lams id a = function
  | 0 -> a
  | n -> many_lams id (MLlam (id,a)) (pred n)

let anonym_tmp_lams a n = many_lams (Tmp anonymous_name) a n
let dummy_lams a n = many_lams Dummy a n

(*s mixed according to a signature. *)

let rec anonym_or_dummy_lams a = function
  | [] -> a
  | Keep :: s -> MLlam(anonymous, anonym_or_dummy_lams a s)
  | Kill _ :: s -> MLlam(Dummy, anonym_or_dummy_lams a s)

(*S Operations concerning eta. *)

(*s The following function creates [MLrel n;...;MLrel 1] *)

let rec eta_args n =
  if Int.equal n 0 then [] else (MLrel n)::(eta_args (pred n))

(*s Same, but filtered by a signature. *)

let rec eta_args_sign n = function
  | [] -> []
  | Keep :: s -> (MLrel n) :: (eta_args_sign (n-1) s)
  | Kill _ :: s -> eta_args_sign (n-1) s

(*s This one tests [MLrel (n+k); ... ;MLrel (1+k)] *)

let rec test_eta_args_lift k n = function
  | [] -> Int.equal n 0
  | MLrel m :: q -> Int.equal (k+n) m && (test_eta_args_lift k (pred n) q)
  | _ -> false

(*s Computes an eta-reduction. *)

let eta_red e =
  let ids,t = collect_lams e in
  let n = List.length ids in
  if Int.equal n 0 then e
  else match t with
    | MLapp (f,a) ->
        let m = List.length a in
        let ids,body,args =
          if Int.equal m n then
            [], f, a
          else if m < n then
            List.skipn m ids, f, a
          else (* m > n *)
            let a1,a2 = List.chop (m-n) a in
            [], MLapp (f,a1), a2
        in
        let p = List.length args in
        if test_eta_args_lift 0 p args && not (ast_occurs_itvl 1 p body)
        then named_lams ids (ast_lift (-p) body)
        else e
    | _ -> e

(* Performs an eta-reduction when the core is atomic and value,
   or otherwise returns None *)

let atomic_eta_red e =
  let ids,t = collect_lams e in
  let n = List.length ids in
  match t with
  | MLapp (f,a) when test_eta_args_lift 0 n a ->
     (match f with
      | MLrel k when k>n -> Some (MLrel (k-n))
      | MLglob _ | MLdummy _ -> Some f
      | _ -> None)
  | _ -> None

(*s Computes all head linear beta-reductions possible in [(t a)].
  Non-linear head beta-redex become let-in. *)

let rec linear_beta_red a t = match a,t with
  | [], _ -> t
  | a0::a, MLlam (id,t) ->
      (match nb_occur_match t with
         | 0 -> linear_beta_red a (ast_pop t)
         | 1 -> linear_beta_red a (ast_subst a0 t)
         | _ ->
             let a = List.map (ast_lift 1) a in
             MLletin (id, a0, linear_beta_red a t))
  | _ -> MLapp (t, a)

let rec tmp_head_lams = function
  | MLlam (id, t) -> MLlam (tmp_id id, tmp_head_lams t)
  | e -> e

(*s Applies a substitution [s] of constants by their body, plus
  linear beta reductions at modified positions.
  Moreover, we mark some lambdas as suitable for later linear
  reduction (this helps the inlining of recursors).
*)

let rec ast_glob_subst s t = match t with
  | MLapp ((MLglob ((GlobRef.ConstRef kn) as refe)) as f, a) ->
      let a = List.map (fun e -> tmp_head_lams (ast_glob_subst s e)) a in
      (try linear_beta_red a (Refmap'.find refe s)
       with Not_found -> MLapp (f, a))
  | MLglob ((GlobRef.ConstRef kn) as refe) ->
      (try Refmap'.find refe s with Not_found -> t)
  | _ -> ast_map (ast_glob_subst s) t


(*S Auxiliary functions used in simplification of ML cases. *)

(* Factorisation of some match branches into a common "x -> f x"
   branch may break types sometimes. Example: [type 'x a = A].
   Then [let id = function A -> A] has type ['x a -> 'y a],
   which is incompatible with the type of [let id x = x].
   We now check that the type arguments of the inductive are
   preserved by our transformation.

   TODO: this verification should be done someday modulo
   expansion of type definitions.
*)

(*s [branch_as_function b typ (l,p,c)] tries to see branch [c]
  as a function [f] applied to [MLcons(r,l)]. For that it transforms
  any [MLcons(r,l)] in [MLrel 1] and raises [Impossible]
  if any variable in [l] occurs outside such a [MLcons] *)

let branch_as_fun typ (l,p,c) =
  let nargs = List.length l in
  let cons = match p with
    | Pusual r -> MLcons (typ, r, eta_args nargs)
    | Pcons (r,pl) ->
      let pat2rel = function Prel i -> MLrel i | _ -> raise Impossible in
      MLcons (typ, r, List.map pat2rel pl)
    | _ -> raise Impossible
  in
  let rec genrec n = function
    | MLrel i as c ->
        let i' = i-n in
        if i'<1 then c
        else if i'>nargs then MLrel (i-nargs+1)
        else raise Impossible
    | MLcons _ as cons' when eq_ml_ast cons' (ast_lift n cons) -> MLrel (n+1)
    | a -> ast_map_lift genrec n a
  in genrec 0 c

(*s [branch_as_cst (l,p,c)] tries to see branch [c] as a constant
   independent from the pattern [MLcons(r,l)]. For that is raises [Impossible]
   if any variable in [l] occurs in [c], and otherwise returns [c] lifted to
   appear like a function with one arg (for uniformity with [branch_as_fun]).
   NB: [MLcons(r,l)] might occur nonetheless in [c], but only when [l] is
   empty, i.e. when [r] is a constant constructor
*)

let branch_as_cst (l,_,c) =
  let n = List.length l in
  if ast_occurs_itvl 1 n c then raise Impossible;
  ast_lift (1-n) c

(* A branch [MLcons(r,l)->c] can be seen at the same time as a function
   branch and a constant branch, either because:
   - [MLcons(r,l)] doesn't occur in [c]. For example : "A -> B"
   - this constructor is constant (i.e. [l] is empty). For example "A -> A"
   When searching for the best factorisation below, we'll try both.
*)

(* The following structure allows recording which element occurred
   at what position, and then finally return the most frequent
   element and its positions. *)

let census_add, census_max, census_clean =
  let h = ref [] in
  let clearf () = h := [] in
  let rec add k v = function
  | [] -> raise Not_found
  | (k', s) as p :: l ->
    if eq_ml_ast k k' then (k', Int.Set.add v s) :: l
    else p :: add k v l
  in
  let addf k i =
    try h := add k i !h
    with Not_found -> h := (k, Int.Set.singleton i) :: !h
  in
  let maxf () =
    let len = ref 0 and lst = ref Int.Set.empty and elm = ref (MLaxiom "should not appear") in
    List.iter
      (fun (e, s) ->
         let n = Int.Set.cardinal s in
         if n > !len then begin len := n; lst := s; elm := e end)
      !h;
    (!elm,!lst)
  in
  (addf,maxf,clearf)

(* [factor_branches] return the longest possible list of branches
   that have the same factorization, either as a function or as a
   constant.
*)

let is_opt_pat (_,p,_) = match p with
  | Prel _ | Pwild -> true
  | _ -> false

let factor_branches o typ br =
  if Array.exists is_opt_pat br then None (* already optimized *)
  else begin
    census_clean ();
    for i = 0 to Array.length br - 1 do
      if o.opt_case_idr then
        (try census_add (branch_as_fun typ br.(i)) i with Impossible -> ());
      if o.opt_case_cst then
        (try census_add (branch_as_cst br.(i)) i with Impossible -> ());
    done;
    let br_factor, br_set = census_max () in
    census_clean ();
    let n = Int.Set.cardinal br_set in
    if Int.equal n 0 then None
    else if Array.length br >= 2 && n < 2 then None
    else Some (br_factor, br_set)
  end

(*s If all branches are functions, try to permute the case and the functions. *)

let rec merge_ids ids ids' = match ids,ids' with
  | [],l -> l
  | l,[] -> l
  | i::ids, i'::ids' ->
      (if i == Dummy then i' else i) :: (merge_ids ids ids')

let is_exn = function MLexn _ -> true | _ -> false

let permut_case_fun br acc =
  let nb = ref max_int in
  Array.iter (fun (_,_,t) ->
                let ids, c = collect_lams t in
                let n = List.length ids in
                if (n < !nb) && (not (is_exn c)) then nb := n) br;
  if Int.equal !nb  max_int || Int.equal !nb 0 then ([],br)
  else begin
    let br = Array.copy br in
    let ids = ref [] in
    for i = 0 to Array.length br - 1 do
      let (l,p,t) = br.(i) in
      let local_nb = nb_lams t in
      if local_nb < !nb then (* t = MLexn ... *)
        br.(i) <- (l,p,remove_n_lams local_nb t)
      else begin
        let local_ids,t = collect_n_lams !nb t in
        ids := merge_ids !ids local_ids;
        br.(i) <- (l,p,permut_rels !nb (List.length l) t)
      end
    done;
    (!ids,br)
  end

(*S Generalized iota-reduction. *)

(* Definition of a generalized iota-redex: it's a [MLcase(e,br)]
   where the head [e] is a [MLcons] or made of [MLcase]'s with
   [MLcons] as leaf branches.
   A generalized iota-redex is transformed into beta-redexes. *)

(* In [iota_red], we try to simplify a [MLcase(_,MLcons(typ,r,a),br)].
   Argument [i] is the branch we consider, we should lift what
   comes from [br] by [lift] *)

let rec iota_red i lift br ((typ,r,a) as cons) =
  if i >= Array.length br then raise Impossible;
  let (ids,p,c) = br.(i) in
  match p with
    | Pusual r' | Pcons (r',_) when not (GlobRef.CanOrd.equal r' r) -> iota_red (i+1) lift br cons
    | Pusual r' ->
      let c = named_lams (List.rev ids) c in
      let c = ast_lift lift c
      in MLapp (c,a)
    | Prel 1 when Int.equal (List.length ids) 1 ->
      let c = MLlam (List.hd ids, c) in
      let c = ast_lift lift c
      in MLapp(c,[MLcons(typ,r,a)])
    | Pwild when List.is_empty ids -> ast_lift lift c
    | _ -> raise Impossible (* TODO: handle some more cases *)

(* [iota_gen] is an extension of [iota_red] where we allow to
   traverse matches in the head of the first match *)

let iota_gen br hd =
  let rec iota k = function
    | MLcons (typ,r,a) -> iota_red 0 k br (typ,r,a)
    | MLcase(typ,e,br') ->
        let new_br =
          Array.map (fun (i,p,c)->(i,p,iota (k+(List.length i)) c)) br'
        in MLcase(typ,e,new_br)
    | _ -> raise Impossible
  in iota 0 hd

let is_atomic = function
  | MLrel _ | MLglob _ | MLexn _ | MLdummy _ -> true
  | _ -> false

let is_imm_apply = function MLapp (MLrel 1, _) -> true | _ -> false

(** Program creates a let-in named "program_branch_NN" for each branch of match.
    Unfolding them leads to more natural code (and more dummy removal) *)

let is_program_branch = function
  | Tmp _ | Dummy -> false
  | Id id ->
    let s = Id.to_string id in
    try Scanf.sscanf s "program_branch_%d%!" (fun _ -> true)
    with Scanf.Scan_failure _ | End_of_file -> false

let expand_linear_let o id e =
   o.opt_lin_let || is_tmp id || is_program_branch id || is_imm_apply e

(*S The main simplification function. *)

(* Some beta-iota reductions + simplifications. *)

let rec unmagic = function MLmagic e -> unmagic e | e -> e
let is_magic = function MLmagic _ -> true | _ -> false
let magic_hd a = match a with
  | MLmagic _ :: _ -> a
  | e :: a -> MLmagic e :: a
  | [] -> assert false

let rec simpl o = function
  | MLapp (f, []) -> simpl o f
  | MLapp (MLapp(f,a),a') -> simpl o (MLapp(f,a@a'))
  | MLapp (f, a) ->
     (* When the head of the application is magic, no need for magic on args *)
     let a = if is_magic f then List.map unmagic a else a in
     simpl_app o (List.map (simpl o) a) (simpl o f)
  | MLcase (typ,e,br) ->
      let br = Array.map (fun (l,p,t) -> (l,p,simpl o t)) br in
      simpl_case o typ br (simpl o e)
  | MLletin(Dummy,_,e) -> simpl o (ast_pop e)
  | MLletin(id,c,e) ->
      let e = simpl o e in
      if
        (is_atomic c) || (is_atomic e) ||
        (let n = nb_occur_match e in
         (Int.equal n 0 || (Int.equal n 1 && expand_linear_let o id e)))
      then
        simpl o (ast_subst c e)
      else
        MLletin(id, simpl o c, e)
  | MLfix(i,ids,c) ->
      let n = Array.length ids in
      if ast_occurs_itvl 1 n c.(i) then
        MLfix (i, ids, Array.map (simpl o) c)
      else simpl o (ast_lift (-n) c.(i)) (* Dummy fixpoint *)
  | MLmagic(MLmagic _ as e) -> simpl o e
  | MLmagic(MLapp (f,l)) -> simpl o (MLapp (MLmagic f, l))
  | MLmagic(MLletin(id,c,e)) -> simpl o (MLletin(id,c,MLmagic e))
  | MLmagic(MLcase(typ,e,br)) ->
     let br' = Array.map (fun (ids,p,c) -> (ids,p,MLmagic c)) br in
     simpl o (MLcase(typ,e,br'))
  | MLmagic(MLdummy _ as e) when lang () == Haskell -> e
  | MLmagic(MLexn _ as e) -> e
  | MLlam _ as e ->
     (match atomic_eta_red e with
      | Some e' -> e'
      | None -> ast_map (simpl o) e)
  | a -> ast_map (simpl o) a

(* invariant : list [a] of arguments is non-empty *)

and simpl_app o a = function
  | MLlam (Dummy,t) ->
      simpl o (MLapp (ast_pop t, List.tl a))
  | MLlam (id,t) -> (* Beta redex *)
      (match nb_occur_match t with
         | 0 -> simpl o (MLapp (ast_pop t, List.tl a))
         | 1 when (is_tmp id || o.opt_lin_beta) ->
             simpl o (MLapp (ast_subst (List.hd a) t, List.tl a))
         | _ ->
             let a' = List.map (ast_lift 1) (List.tl a) in
             simpl o (MLletin (id, List.hd a, MLapp (t, a'))))
  | MLmagic (MLlam (id,t)) ->
      (* When we've at least one argument, we permute the magic
         and the lambda, to simplify things a bit (see #2795).
         Alas, the 1st argument must also be magic then. *)
      simpl_app o (magic_hd a) (MLlam (id,MLmagic t))
  | MLletin (id,e1,e2) when o.opt_let_app ->
      (* Application of a letin: we push arguments inside *)
      MLletin (id, e1, simpl o (MLapp (e2, List.map (ast_lift 1) a)))
  | MLcase (typ,e,br) when o.opt_case_app ->
      (* Application of a case: we push arguments inside *)
      let br' =
        Array.map
          (fun (l,p,t) ->
             let k = List.length l in
             let a' = List.map (ast_lift k) a in
             (l, p, simpl o (MLapp (t,a')))) br
      in simpl o (MLcase (typ,e,br'))
  | (MLdummy _ | MLexn _) as e -> e
        (* We just discard arguments in those cases. *)
  | f -> MLapp (f,a)

(* Invariant : all empty matches should now be [MLexn] *)

and simpl_case o typ br e =
  try
    (* Generalized iota-redex *)
    if not o.opt_case_iot then raise Impossible;
    simpl o (iota_gen br e)
  with Impossible ->
    (* Swap the case and the lam if possible *)
    let ids,br = if o.opt_case_fun then permut_case_fun br [] else [],br in
    let n = List.length ids in
    if not (Int.equal n 0) then
      simpl o (named_lams ids (MLcase (typ, ast_lift n e, br)))
    else
      (* Can we merge several branches as the same constant or function ? *)
      if lang() == Scheme || is_custom_match br
      then MLcase (typ, e, br)
      else match factor_branches o typ br with
        | Some (f,ints) when Int.equal (Int.Set.cardinal ints) (Array.length br) ->
          (* If all branches have been factorized, we remove the match *)
          simpl o (MLletin (Tmp anonymous_name, e, f))
        | Some (f,ints) ->
          let last_br =
            if ast_occurs 1 f then ([Tmp anonymous_name], Prel 1, f)
            else ([], Pwild, ast_pop f)
          in
          let brl = Array.to_list br in
          let brl_opt = List.filteri (fun i _ -> not (Int.Set.mem i ints)) brl in
          let brl_opt = brl_opt @ [last_br] in
          MLcase (typ, e, Array.of_list brl_opt)
        | None -> MLcase (typ, e, br)

(*S Local prop elimination. *)
(* We try to eliminate as many [prop] as possible inside an [ml_ast]. *)

(*s In a list, it selects only the elements corresponding to a [Keep]
   in the boolean list [l]. *)

let rec select_via_bl l args = match l,args with
  | [],_ -> args
  | Keep::l,a::args -> a :: (select_via_bl l args)
  | Kill _::l,a::args -> select_via_bl l args
  | _ -> assert false

(*s [kill_some_lams] removes some head lambdas according to the signature [bl].
   This list is build on the identifier list model: outermost lambda
   is on the right.
   [Rels] corresponding to removed lambdas are not supposed to occur
   (except maybe in the case of Kimplicit), and
   the other [Rels] are made correct via a [gen_subst].
   Output is not directly a [ml_ast], compose with [named_lams] if needed. *)

let is_impl_kill = function Kill (Kimplicit _) -> true | _ -> false

let kill_some_lams bl (ids,c) =
  let n = List.length bl in
  let n' = List.fold_left (fun n b -> if b == Keep then (n+1) else n) 0 bl in
  if Int.equal n n' then ids,c
  else if Int.equal n' 0 && not (List.exists is_impl_kill bl)
  then [],ast_lift (-n) c
  else begin
    let v = Array.make n None in
    let rec parse_ids i j = function
      | [] -> ()
      | Keep :: l -> v.(i) <- Some (MLrel j); parse_ids (i+1) (j+1) l
      | Kill (Kimplicit _ as k) :: l ->
         v.(i) <- Some (MLdummy k); parse_ids (i+1) j l
      | Kill _ :: l -> parse_ids (i+1) j l
    in parse_ids 0 1 bl;
    select_via_bl bl ids, gen_subst v (n'-n) c
  end

(*s [kill_dummy_lams] uses the last function to kill the lambdas corresponding
  to a [dummy_name]. It can raise [Impossible] if there is nothing to do, or
  if there is no lambda left at all. In addition, it now accepts a signature
  that may mention some implicits. *)

let rec merge_implicits ids s = match ids, s with
  | [],_ -> []
  | _,[] -> List.map sign_of_id ids
  | Dummy::ids, _::s -> Kill Kprop :: merge_implicits ids s
  | _::ids, (Kill (Kimplicit _) as k)::s -> k :: merge_implicits ids s
  | _::ids, _::s -> Keep :: merge_implicits ids s

let kill_dummy_lams sign c =
  let ids,c = collect_lams c in
  let bl = merge_implicits ids (List.rev sign) in
  if not (List.memq Keep bl) then raise Impossible;
  let rec fst_kill n = function
    | [] -> raise Impossible
    | Kill _ :: bl -> n
    | Keep :: bl -> fst_kill (n+1) bl
  in
  let skip = max 0 ((fst_kill 0 bl) - 1) in
  let ids_skip, ids = List.chop skip ids in
  let _, bl = List.chop skip bl in
  let c = named_lams ids_skip c in
  let ids',c = kill_some_lams bl (ids,c) in
  (ids,bl), named_lams ids' c

(*s [eta_expansion_sign] takes a function [fun idn ... id1 -> c]
   and a signature [s] and builds a eta-long version. *)

(* For example, if [s = [Keep;Keep;Kill Prop;Keep]] then the output is :
   [fun idn ... id1 x x _ x -> (c' 4 3 __ 1)]  with [c' = lift 4 c] *)

let eta_expansion_sign s (ids,c) =
  let rec abs ids rels i = function
    | [] ->
        let a = List.rev_map (function MLrel x -> MLrel (i-x) | a -> a) rels
        in ids, MLapp (ast_lift (i-1) c, a)
    | Keep :: l -> abs (anonymous :: ids) (MLrel i :: rels) (i+1) l
    | Kill k :: l -> abs (Dummy :: ids) (MLdummy k :: rels) (i+1) l
  in abs ids [] 1 s

(*s If [s = [b1; ... ; bn]] then [case_expunge] decomposes [e]
  in [n] lambdas (with eta-expansion if needed) and removes all dummy lambdas
  corresponding to [Kill _] in [s]. *)

let case_expunge s e =
  let m = List.length s in
  let n = nb_lams e in
  let p = if m <= n then collect_n_lams m e
  else eta_expansion_sign (List.skipn n s) (collect_lams e) in
  kill_some_lams (List.rev s) p

(*s [term_expunge] takes a function [fun idn ... id1 -> c]
  and a signature [s] and remove dummy lams. The difference
  with [case_expunge] is that we here leave one dummy lambda
  if all lambdas are logical dummy and the target language is strict. *)

let term_expunge s (ids,c) =
  if List.is_empty s then c
  else
    let ids,c = kill_some_lams (List.rev s) (ids,c) in
    if List.is_empty ids && lang () != Haskell &&
       sign_kind s == UnsafeLogicalSig
    then MLlam (Dummy, ast_lift 1 c)
    else named_lams ids c

(*s [kill_dummy_args (ids,bl) r t] looks for occurrences of [MLrel r] in [t]
  and purge the args of [MLrel r] corresponding to a [Kill] in [bl].
  It makes eta-expansion if needed. *)

let kill_dummy_args (ids,bl) r t =
  let m = List.length ids in
  let sign = List.rev bl in
  let rec found n = function
    | MLrel r' when Int.equal r' (r + n) -> true
    | MLmagic e -> found n e
    | _ -> false
  in
  let rec killrec n = function
    | MLapp(e, a) when found n e ->
        let k = max 0 (m - (List.length a)) in
        let a = List.map (killrec n) a in
        let a = List.map (ast_lift k) a in
        let a = select_via_bl sign (a @ (eta_args k)) in
        named_lams (List.firstn k ids) (MLapp (ast_lift k e, a))
    | e when found n e ->
        let a = select_via_bl sign (eta_args m) in
        named_lams ids (MLapp (ast_lift m e, a))
    | e -> ast_map_lift killrec n e
  in killrec 0 t

(*s The main function for local [dummy] elimination. *)

let sign_of_args a =
 List.map (function MLdummy k -> Kill k | _ -> Keep) a

let rec kill_dummy = function
  | MLfix(i,fi,c) ->
      (try
         let k,c = kill_dummy_fix i c [] in
         ast_subst (MLfix (i,fi,c)) (kill_dummy_args k 1 (MLrel 1))
       with Impossible -> MLfix (i,fi,Array.map kill_dummy c))
  | MLapp (MLfix (i,fi,c),a) ->
      let a = List.map kill_dummy a in
      (* Heuristics: if some arguments are implicit args, we try to
         eliminate the corresponding arguments of the fixpoint *)
      (try
         let k,c = kill_dummy_fix i c (sign_of_args a) in
         let fake = MLapp (MLrel 1, List.map (ast_lift 1) a) in
         let fake' = kill_dummy_args k 1 fake in
         ast_subst (MLfix (i,fi,c)) fake'
       with Impossible -> MLapp(MLfix(i,fi,Array.map kill_dummy c),a))
  | MLletin(id, MLfix (i,fi,c),e) ->
      (try
         let k,c = kill_dummy_fix i c [] in
         let e = kill_dummy (kill_dummy_args k 1 e) in
         MLletin(id, MLfix(i,fi,c),e)
      with Impossible ->
        MLletin(id, MLfix(i,fi,Array.map kill_dummy c),kill_dummy e))
  | MLletin(id,c,e) ->
      (try
         let k,c = kill_dummy_lams [] (kill_dummy_hd c) in
         let e = kill_dummy (kill_dummy_args k 1 e) in
         let c = kill_dummy c in
         if is_atomic c then ast_subst c e else MLletin (id, c, e)
       with Impossible -> MLletin(id,kill_dummy c,kill_dummy e))
  | a -> ast_map kill_dummy a

(* Similar function, but acting only on head lambdas and let-ins *)

and kill_dummy_hd = function
  | MLlam(id,e) -> MLlam(id, kill_dummy_hd e)
  | MLletin(id,c,e) ->
      (try
         let k,c = kill_dummy_lams [] (kill_dummy_hd c) in
         let e = kill_dummy_hd (kill_dummy_args k 1 e) in
         let c = kill_dummy c in
         if is_atomic c then ast_subst c e else MLletin (id, c, e)
       with Impossible -> MLletin(id,kill_dummy c,kill_dummy_hd e))
  | a -> a

and kill_dummy_fix i c s =
  let n = Array.length c in
  let k,ci = kill_dummy_lams s (kill_dummy_hd c.(i)) in
  let c = Array.copy c in c.(i) <- ci;
  for j = 0 to (n-1) do
    c.(j) <- kill_dummy (kill_dummy_args k (n-i) c.(j))
  done;
  k,c

(*s Putting things together. *)

let normalize a =
  let o = optims () in
  let rec norm a =
    let a' = if o.opt_kill_dum then kill_dummy (simpl o a) else simpl o a in
    if eq_ml_ast a a' then a else norm a'
  in norm a

(*S Special treatment of fixpoint for pretty-printing purpose. *)

let general_optimize_fix f ids n args m c =
  let v = Array.init n (fun i -> i) in
  let aux i = function
    | MLrel j when v.(j-1)>=0 ->
        if ast_occurs (j+1) c then raise Impossible else v.(j-1)<-(-i-1)
    | _ -> raise Impossible
  in List.iteri aux args;
  let args_f = List.rev_map (fun i -> MLrel (i+m+1)) (Array.to_list v) in
  let new_f = anonym_tmp_lams (MLapp (MLrel (n+m+1),args_f)) m in
  let new_c = named_lams ids (normalize (MLapp ((ast_subst new_f c),args))) in
  MLfix(0,[|f|],[|new_c|])

let optimize_fix a =
  if not (optims()).opt_fix_fun then a
  else
    let ids,a' = collect_lams a in
    let n = List.length ids in
    if Int.equal n 0 then a
    else match a' with
      | MLfix(_,[|f|],[|c|]) ->
          let new_f = MLapp (MLrel (n+1),eta_args n) in
          let new_c = named_lams ids (normalize (ast_subst new_f c))
          in MLfix(0,[|f|],[|new_c|])
      | MLapp(a',args) ->
          let m = List.length args in
          (match a' with
             | MLfix(_,_,_) when
                 (test_eta_args_lift 0 n args) && not (ast_occurs_itvl 1 m a')
                 -> a'
             | MLfix(_,[|f|],[|c|]) ->
                 (try general_optimize_fix f ids n args m c
                  with Impossible -> a)
             | _ -> a)
      | _ -> a

(*S Inlining. *)

(* Utility functions used in the decision of inlining. *)

let ml_size_branch size pv = Array.fold_left (fun a (_,_,t) -> a + size t) 0 pv

let rec ml_size = function
  | MLapp(t,l) -> List.length l + ml_size t + ml_size_list l
  | MLlam(_,t) -> 1 + ml_size t
  | MLcons(_,_,l) | MLtuple l -> ml_size_list l
  | MLcase(_,t,pv) -> 1 + ml_size t + ml_size_branch ml_size pv
  | MLfix(_,_,f) -> ml_size_array f
  | MLletin (_,_,t) -> ml_size t
  | MLmagic t -> ml_size t
  | MLparray(t,def) -> ml_size_array t + ml_size def
  | MLglob _ | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _
  | MLuint _ | MLfloat _ | MLstring _ -> 0

and ml_size_list l = List.fold_left (fun a t -> a + ml_size t) 0 l

and ml_size_array a = Array.fold_left (fun a t -> a + ml_size t) 0 a

let is_fix = function MLfix _ -> true | _ -> false

(*s Strictness *)

(* A variable is strict if the evaluation of the whole term implies
   the evaluation of this variable. Non-strict variables can be found
   behind Match, for example. Expanding a term [t] is a good idea when
   it begins by at least one non-strict lambda, since the corresponding
   argument to [t] might be unevaluated in the expanded code. *)

exception Toplevel

let lift n l = List.map ((+) n) l

let pop n l = List.map (fun x -> if x<=n then raise Toplevel else x-n) l

(* This function returns a list of de Bruijn indices of non-strict variables,
   or raises [Toplevel] if it has an internal non-strict variable.
   In fact, not all variables are checked for strictness, only the ones which
   de Bruijn index is in the candidates list [cand]. The flag [add] controls
   the behaviour when going through a lambda: should we add the corresponding
   variable to the candidates?  We use this flag to check only the external
   lambdas, those that will correspond to arguments. *)

let rec non_stricts add cand = function
  | MLlam (id,t) ->
      let cand = lift 1 cand in
      let cand = if add then 1::cand else cand in
      pop 1 (non_stricts add cand t)
  | MLrel n ->
      List.filter (fun m -> not (Int.equal m n)) cand
  | MLapp (t,l)->
      let cand = non_stricts false cand t in
      List.fold_left (non_stricts false) cand l
  | MLcons (_,_,l) ->
      List.fold_left (non_stricts false) cand l
  | MLletin (_,t1,t2) ->
      let cand = non_stricts false cand t1 in
      pop 1 (non_stricts add (lift 1 cand) t2)
  | MLfix (_,i,f)->
      let n = Array.length i in
      let cand = lift n cand in
      let cand = Array.fold_left (non_stricts false) cand f in
      pop n cand
  | MLcase (_,t,v) ->
      (* The only interesting case: for a variable to be non-strict, *)
      (* it is sufficient that it appears non-strict in at least one branch, *)
      (* so we make an union (in fact a merge). *)
      let cand = non_stricts false cand t in
      Array.fold_left
        (fun c (i,_,t)->
           let n = List.length i in
           let cand = lift n cand in
           let cand = pop n (non_stricts add cand t) in
           List.merge Int.compare cand c) [] v
        (* [merge] may duplicates some indices, but I don't mind. *)
  | MLmagic t ->
      non_stricts add cand t
  | _ ->
      cand

(* The real test: we are looking for internal non-strict variables, so we start
   with no candidates, and the only positive answer is via the [Toplevel]
   exception. *)

let is_not_strict t =
  try let _ = non_stricts true [] t in false
  with Toplevel -> true

(*s Inlining decision *)

(* [inline_test] answers the following question:
   If we could inline [t] (the user said nothing special),
   should we inline ?

   We expand small terms with at least one non-strict
   variable (i.e. a variable that may not be evaluated).

   Furthermore we don't expand fixpoints.

   Moreover, as mentioned by X. Leroy (bug #2241),
   inlining a constant from inside an opaque module might
   break types. To avoid that, we require below that
   both [r] and its body are globally visible. This isn't
   fully satisfactory, since [r] might not be visible (functor),
   and anyway it might be interesting to inline [r] at least
   inside its own structure. But to be safe, we adopt this
   restriction for the moment.
*)

open Declareops

let inline_test r t =
  if not (auto_inline ()) then false
  else
    let c = match r with GlobRef.ConstRef c -> c | _ -> assert false in
    let has_body =
      Environ.mem_constant c (Global.env()) && constant_has_body (Global.lookup_constant c)
    in
    has_body &&
      (let t1 = eta_red t in
       let t2 = snd (collect_lams t1) in
       not (is_fix t2) && ml_size t < 12 && is_not_strict t)

let con_of_string s =
  let d, id = Libnames.split_dirpath (dirpath_of_string s) in
  Constant.make2 (ModPath.MPfile d) (Label.of_id id)

let manual_inline_set =
  List.fold_right (fun x -> Cset_env.add (con_of_string x))
    [ "Coq.Init.Wf.well_founded_induction_type";
      "Coq.Init.Wf.well_founded_induction";
      "Coq.Init.Wf.Acc_iter";
      "Coq.Init.Wf.Fix_F";
      "Coq.Init.Wf.Fix";
      "Coq.Init.Datatypes.andb";
      "Coq.Init.Datatypes.orb";
      "Coq.Init.Logic.eq_rec_r";
      "Coq.Init.Logic.eq_rect_r";
      "Coq.Init.Specif.proj1_sig";
    ]
    Cset_env.empty

let manual_inline = function
  | GlobRef.ConstRef c -> Cset_env.mem c manual_inline_set
  | _ -> false

(* If the user doesn't say he wants to keep [t], we inline in two cases:
   \begin{itemize}
   \item the user explicitly requests it
   \item [expansion_test] answers that the inlining is a good idea, and
   we are free to act (AutoInline is set)
   \end{itemize} *)

let inline r t =
  not (to_keep r) (* The user DOES want to keep it *)
  && not (is_inline_custom r)
  && (to_inline r (* The user DOES want to inline it *)
     || (lang () != Haskell &&
         (is_projection r || is_recursor r ||
          manual_inline r || inline_test r t)))

