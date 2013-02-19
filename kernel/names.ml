(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* File created around Apr 1994 for CiC V5.10.5 by Chet Murthy collecting
   parts of file initial.ml from CoC V4.8, Dec 1988, by Gérard Huet,
   Thierry Coquand and Christine Paulin *)
(* Hash-consing by Bruno Barras in Feb 1998 *)
(* Extra functions for splitting/generation of identifiers by Hugo Herbelin *)
(* Restructuration by Jacek Chrzaszcz as part of the implementation of
   the module system, Aug 2002 *)
(* Abstraction over the type of constant for module inlining by Claudio
   Sacerdoti, Nov 2004 *)
(* Miscellaneous features or improvements by Hugo Herbelin, 
   Élie Soubiran, ... *)

open Pp
open Errors
open Util

(** {6 Identifiers } *)

module Id =
struct
  type t = string

  let equal = String.equal

  let compare = String.compare

  let check_soft x =
    let iter (fatal, x) =
      if fatal then error x else Pp.msg_warning (str x)
    in
    Option.iter iter (Unicode.ident_refutation x)

  let check x =
    let iter (_, x) = Errors.error x in
    Option.iter iter (Unicode.ident_refutation x)

  let of_string s =
    let () = check_soft s in
    let s = String.copy s in
    String.hcons s

  let to_string id = String.copy id

  let print id = str id

  module Self =
  struct
    type t = string
    let compare = compare
  end

  module Set = Set.Make(Self)
  module Map =
  struct
    include Map.Make(Self)
    exception Finded
    let exists f m =
      try iter (fun a b -> if f a b then raise Finded) m ; false
      with Finded -> true
    let singleton k v = add k v empty
  end

  module Pred = Predicate.Make(Self)

  let hcons = String.hcons

end


module Name =
struct
  type t = Name of Id.t | Anonymous

  let equal n1 n2 = match n1, n2 with
  | Anonymous, Anonymous -> true
  | Name id1, Name id2 -> String.equal id1 id2
  | _ -> false

  module Self_Hashcons =
    struct
      type _t = t
      type t = _t
      type u = Id.t -> Id.t
      let hashcons hident = function
        | Name id -> Name (hident id)
        | n -> n
      let equal n1 n2 =
        n1 == n2 ||
        match (n1,n2) with
          | (Name id1, Name id2) -> id1 == id2
          | (Anonymous,Anonymous) -> true
          | _ -> false
      let hash = Hashtbl.hash
    end

  module Hname = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons Hname.generate Id.hcons

end

type name = Name.t = Name of Id.t | Anonymous
(** Alias, to import constructors. *)

(** {6 Various types based on identifiers } *)

type variable = Id.t

type module_ident = Id.t

module ModIdmap = Id.Map

(** {6 Directory paths = section names paths } *)

(** Dirpaths are lists of module identifiers.
    The actual representation is reversed to optimise sharing:
    Coq.A.B is ["B";"A";"Coq"] *)

let default_module_name = "If you see this, it's a bug"

module Dir_path =
struct
  type t = module_ident list

  let rec compare (p1 : t) (p2 : t) =
    if p1 == p2 then 0
    else begin match p1, p2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | id1 :: p1, id2 :: p2 ->
      let c = Id.compare id1 id2 in
      if Int.equal c 0 then compare p1 p2 else c
    end

  let equal p1 p2 = Int.equal (compare p1 p2) 0

  let make x = x
  let repr x = x

  let empty = []

  let is_empty d = match d with [] -> true | _ -> false

  let to_string = function
    | [] -> "<>"
    | sl -> String.concat "." (List.rev_map Id.to_string sl)

  let initial = [default_module_name]

  module Self_Hashcons =
    struct
      type t_ = t
      type t = t_
      type u = Id.t -> Id.t
      let hashcons hident d = List.smartmap hident d
      let rec equal d1 d2 =
        d1 == d2 ||
        match (d1, d2) with
        | [], [] -> true
        | id1 :: d1, id2 :: d2 -> id1 == id2 && equal d1 d2
        | _ -> false
      let hash = Hashtbl.hash
    end

  module Hdir = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons Hdir.generate Id.hcons

end

(** {6 Unique names for bound modules } *)

module MBId =
struct
  type t = int * Id.t * Dir_path.t

  let gen =
    let seed = ref 0 in fun () ->
      let ans = !seed in
      let () = incr seed in
      ans

  let make dir s = (gen(), s, dir)

  let repr mbid = mbid

  let to_string (i, s, p) =
    Dir_path.to_string p ^ "." ^ s

  let debug_to_string (i, s, p) =
    "<"(*^string_of_dirpath p ^"#"^*) ^ s ^"#"^ string_of_int i^">"

  let compare (x : t) (y : t) =
    if x == y then 0
    else match (x, y) with
    | (nl, idl, dpl), (nr, idr, dpr) ->
      let ans = Int.compare nl nr in
      if not (Int.equal ans 0) then ans
      else
        let ans = Id.compare idl idr in
        if not (Int.equal ans 0) then ans
        else
          Dir_path.compare dpl dpr

  let equal x y = Int.equal (compare x y) 0

  let to_id (_, s, _) = s

  module Self_Hashcons =
    struct
      type _t = t
      type t = _t
      type u = (Id.t -> Id.t) * (Dir_path.t -> Dir_path.t)
      let hashcons (hid,hdir) (n,s,dir) = (n,hid s,hdir dir)
      let equal ((n1,s1,dir1) as x) ((n2,s2,dir2) as y) =
        (x == y) ||
        (Int.equal n1 n2 && s1 == s2 && dir1 == dir2)
      let hash = Hashtbl.hash
    end

  module HashMBId = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons HashMBId.generate (Id.hcons, Dir_path.hcons)

end

(** {6 Names of structure elements } *)

module Label =
struct
  include Id
  let make = Id.of_string
  let of_id id = id
  let to_id id = id
end

(** {6 The module part of the kernel name } *)

type module_path =
  | MPfile of Dir_path.t
  | MPbound of MBId.t
  | MPdot of module_path * Label.t

let rec check_bound_mp = function
  | MPbound _ -> true
  | MPdot(mp,_) ->check_bound_mp mp
  | _ -> false

let rec string_of_mp = function
  | MPfile sl -> Dir_path.to_string sl
  | MPbound uid -> MBId.to_string uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ Label.to_string l

(** we compare labels first if both are MPdots *)
let rec mp_ord mp1 mp2 =
  if mp1 == mp2 then 0
  else match (mp1, mp2) with
  | MPfile p1, MPfile p2 ->
    Dir_path.compare p1 p2
  | MPbound id1, MPbound id2 ->
    MBId.compare id1 id2
  | MPdot (mp1, l1), MPdot (mp2, l2) ->
      let c = String.compare l1 l2 in
        if not (Int.equal c 0) then c
        else mp_ord mp1 mp2
  | MPfile _, _ -> -1
  | MPbound _, MPfile _ -> 1
  | MPbound _, MPdot _ -> -1
  | MPdot _, _ -> 1

let mp_eq mp1 mp2 = Int.equal (mp_ord mp1 mp2) 0

module MPord = struct
  type t = module_path
  let compare = mp_ord
end

module MPset = Set.Make(MPord)
module MPmap = Map.Make(MPord)

let initial_path = MPfile Dir_path.initial

(** {6 Kernel names } *)

type kernel_name = module_path * Dir_path.t * Label.t

let make_kn mp dir l = (mp,dir,l)
let repr_kn kn = kn

let modpath kn =
  let mp,_,_ = repr_kn kn in mp

let label kn =
  let _,_,l = repr_kn kn in l

let string_of_kn (mp,dir,l) =
  let str_dir = match dir with
  | [] -> "."
  | _ -> "#" ^ Dir_path.to_string dir ^ "#"
  in
  string_of_mp mp ^ str_dir ^ Label.to_string l

let pr_kn kn = str (string_of_kn kn)

let kn_ord (kn1 : kernel_name) (kn2 : kernel_name) =
  if kn1 == kn2 then 0
  else
    let mp1, dir1, l1 = kn1 in
    let mp2, dir2, l2 = kn2 in
    let c = String.compare l1 l2 in
      if not (Int.equal c 0) then c
      else
        let c = Dir_path.compare dir1 dir2 in
        if not (Int.equal c 0) then c
        else MPord.compare mp1 mp2

let kn_equal kn1 kn2 = Int.equal (kn_ord kn1 kn2) 0

module KNord = struct
  type t = kernel_name
  let compare = kn_ord
end

module KNmap = Map.Make(KNord)
module KNpred = Predicate.Make(KNord)
module KNset = Set.Make(KNord)

(** {6 Kernel pairs } *)

(** For constant and inductive names, we use a kernel name couple (kn1,kn2)
   where kn1 corresponds to the name used at toplevel (i.e. what the user see)
   and kn2 corresponds to the canonical kernel name i.e. in the environment
   we have {% kn1 \rhd_{\delta}^* kn2 \rhd_{\delta} t %}

   Invariants :
    - the user and canonical kn may differ only on their [module_path],
      the dirpaths and labels should be the same
    - when user and canonical parts differ, we cannot be in a section
      anymore, hence the dirpath must be empty
    - two pairs with the same user part should have the same canonical part

   Note: since most of the time the canonical and user parts are equal,
   we handle this case with a particular constructor to spare some memory *)

module KernelPair = struct

  type kernel_pair =
    | Same of kernel_name (** user = canonical *)
    | Dual of kernel_name * kernel_name (** user then canonical *)

  type t = kernel_pair

  let canonical = function
    | Same kn -> kn
    | Dual (_,kn) -> kn

  let user = function
    | Same kn -> kn
    | Dual (kn,_) -> kn

  let same kn = Same kn
  let dual knu knc = Dual (knu,knc)
  let make knu knc = if knu == knc then Same knc else Dual (knu,knc)

  let debug_to_string = function
    | Same kn -> "(" ^ string_of_kn kn ^ ")"
    | Dual (knu,knc) -> "(" ^ string_of_kn knu ^ "," ^ string_of_kn knc ^ ")"

  (** Default comparison is on the canonical part *)
  let equal x y = x == y || kn_equal (canonical x) (canonical y)

  (** For ordering kernel pairs, both user or canonical parts may make
      sense, according to your needs : user for the environments, canonical
      for other uses (ex: non-logical things). *)

  module UserOrd = struct
    type t = kernel_pair
    let compare x y = kn_ord (user x) (user y)
  end

  module CanOrd = struct
    type t = kernel_pair
    let compare x y = kn_ord (canonical x) (canonical y)
  end

  (** Hash-consing : we discriminate only on the user part, since having
      the same user part implies having the same canonical part
      (invariant of the system). *)

  module Self_Hashcons =
    struct
      type t = kernel_pair
      type u = kernel_name -> kernel_name
      let hashcons hkn = function
        | Same kn -> Same (hkn kn)
        | Dual (knu,knc) -> make (hkn knu) (hkn knc)
      let equal x y = (user x) == (user y)
      let hash = Hashtbl.hash
    end

  module HashKP = Hashcons.Make(Self_Hashcons)

end

(** {6 Constant names } *)

type constant = KernelPair.t

let canonical_con = KernelPair.canonical
let user_con = KernelPair.user
let constant_of_kn = KernelPair.same
let constant_of_kn_equiv = KernelPair.make
let make_con mp dir l = KernelPair.same (mp,dir,l)
let make_con_dual mpu mpc dir l = KernelPair.dual (mpu,dir,l) (mpc,dir,l)
let make_con_equiv mpu mpc dir l =
  if mpu == mpc then make_con mpc dir l else make_con_dual mpu mpc dir l
let repr_con = user_con

let eq_constant = KernelPair.equal
let con_ord = KernelPair.CanOrd.compare
let con_user_ord = KernelPair.UserOrd.compare

let con_label cst = label (canonical_con cst)
let con_modpath cst = modpath (canonical_con cst)

let string_of_con cst = string_of_kn (canonical_con cst)
let pr_con cst = str (string_of_con cst)
let debug_string_of_con = KernelPair.debug_to_string
let debug_pr_con cst = str (debug_string_of_con cst)

let con_with_label cst lbl =
  let (mp1,dp1,l1) = user_con cst and (mp2,dp2,l2) = canonical_con cst in
  assert (String.equal l1 l2 && Dir_path.equal dp1 dp2);
  if String.equal lbl l1
  then cst
  else make_con_equiv mp1 mp2 dp1 lbl

module Cmap = Map.Make(KernelPair.CanOrd)
module Cmap_env = Map.Make(KernelPair.UserOrd)
module Cpred = Predicate.Make(KernelPair.CanOrd)
module Cset = Set.Make(KernelPair.CanOrd)
module Cset_env = Set.Make(KernelPair.UserOrd)


(** {6 Names of mutual inductive types } *)

(** The same thing is done for mutual inductive names
    it replaces also the old mind_equiv field of mutual
    inductive types *)
(** Beware: first inductive has index 0 *)
(** Beware: first constructor has index 1 *)

type mutual_inductive = KernelPair.t
type inductive = mutual_inductive * int
type constructor = inductive * int

let mind_modpath mind = modpath (KernelPair.user mind)
let ind_modpath ind = mind_modpath (fst ind)
let constr_modpath c = ind_modpath (fst c)

let mind_of_kn = KernelPair.same
let mind_of_kn_equiv = KernelPair.make
let make_mind mp dir l = KernelPair.same (mp,dir,l)
let make_mind_dual mpu mpc dir l = KernelPair.dual (mpu,dir,l) (mpc,dir,l)
let make_mind_equiv mpu mpc dir l =
  if mpu == mpc then make_mind mpu dir l else make_mind_dual mpu mpc dir l
let canonical_mind = KernelPair.canonical
let user_mind = KernelPair.user
let repr_mind = user_mind
let mind_label mind = label (user_mind mind)

let eq_mind = KernelPair.equal
let mind_ord = KernelPair.CanOrd.compare
let mind_user_ord = KernelPair.UserOrd.compare

let string_of_mind mind = string_of_kn (user_mind mind)
let pr_mind mind = str (string_of_mind mind)
let debug_string_of_mind = KernelPair.debug_to_string
let debug_pr_mind con = str (debug_string_of_mind con)

let ith_mutual_inductive (kn, _) i = (kn, i)
let ith_constructor_of_inductive ind i = (ind, i)
let inductive_of_constructor (ind, i) = ind
let index_of_constructor (ind, i) = i

let eq_ind (m1, i1) (m2, i2) = Int.equal i1 i2 && eq_mind m1 m2
let ind_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then mind_ord m1 m2 else c
let ind_user_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then mind_user_ord m1 m2 else c

let eq_constructor (ind1, j1) (ind2, j2) = Int.equal j1 j2 && eq_ind ind1 ind2
let constructor_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_ord ind1 ind2 else c
let constructor_user_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_user_ord ind1 ind2 else c

module Mindmap = Map.Make(KernelPair.CanOrd)
module Mindset = Set.Make(KernelPair.CanOrd)
module Mindmap_env = Map.Make(KernelPair.UserOrd)

module InductiveOrdered = struct
  type t = inductive
  let compare = ind_ord
end

module InductiveOrdered_env = struct
  type t = inductive
  let compare = ind_user_ord
end

module Indmap = Map.Make(InductiveOrdered)
module Indmap_env = Map.Make(InductiveOrdered_env)

module ConstructorOrdered = struct
  type t = constructor
  let compare = constructor_ord
end

module ConstructorOrdered_env = struct
  type t = constructor
  let compare = constructor_user_ord
end

module Constrmap = Map.Make(ConstructorOrdered)
module Constrmap_env = Map.Make(ConstructorOrdered_env)

(* Better to have it here that in closure, since used in grammar.cma *)
type evaluable_global_reference =
  | EvalVarRef of Id.t
  | EvalConstRef of constant

let eq_egr e1 e2 = match e1, e2 with
    EvalConstRef con1, EvalConstRef con2 -> eq_constant con1 con2
  | EvalVarRef id1, EvalVarRef id2 -> Int.equal (Id.compare id1 id2) 0
  | _, _ -> false

(** {6 Hash-consing of name objects } *)

module Hmod = Hashcons.Make(
  struct
    type t = module_path
    type u = (Dir_path.t -> Dir_path.t) * (MBId.t -> MBId.t) *
	(string -> string)
    let rec hashcons (hdir,huniqid,hstr as hfuns) = function
      | MPfile dir -> MPfile (hdir dir)
      | MPbound m -> MPbound (huniqid m)
      | MPdot (md,l) -> MPdot (hashcons hfuns md, hstr l)
    let rec equal d1 d2 =
      d1 == d2 ||
      match (d1,d2) with
      | MPfile dir1, MPfile dir2 -> dir1 == dir2
      | MPbound m1, MPbound m2 -> m1 == m2
      | MPdot (mod1,l1), MPdot (mod2,l2) -> l1 == l2 && equal mod1 mod2
      | _ -> false
    let hash = Hashtbl.hash
  end)

module Hkn = Hashcons.Make(
  struct
    type t = kernel_name
    type u = (module_path -> module_path)
	* (Dir_path.t -> Dir_path.t) * (string -> string)
    let hashcons (hmod,hdir,hstr) (md,dir,l) =
      (hmod md, hdir dir, hstr l)
    let equal (mod1,dir1,l1) (mod2,dir2,l2) =
      mod1 == mod2 && dir1 == dir2 && l1 == l2
    let hash = Hashtbl.hash
  end)

module Hind = Hashcons.Make(
  struct
    type t = inductive
    type u = mutual_inductive -> mutual_inductive
    let hashcons hmind (mind, i) = (hmind mind, i)
    let equal (mind1,i1) (mind2,i2) = mind1 == mind2 && Int.equal i1 i2
    let hash = Hashtbl.hash
  end)

module Hconstruct = Hashcons.Make(
  struct
    type t = constructor
    type u = inductive -> inductive
    let hashcons hind (ind, j) = (hind ind, j)
    let equal (ind1, j1) (ind2, j2) = ind1 == ind2 && Int.equal j1 j2
    let hash = Hashtbl.hash
  end)

let hcons_mp =
  Hashcons.simple_hcons Hmod.generate (Dir_path.hcons,MBId.hcons,String.hcons)
let hcons_kn = Hashcons.simple_hcons Hkn.generate (hcons_mp,Dir_path.hcons,String.hcons)
let hcons_con = Hashcons.simple_hcons KernelPair.HashKP.generate hcons_kn
let hcons_mind = Hashcons.simple_hcons KernelPair.HashKP.generate hcons_kn
let hcons_ind = Hashcons.simple_hcons Hind.generate hcons_mind
let hcons_construct = Hashcons.simple_hcons Hconstruct.generate hcons_ind


(*******)

type transparent_state = Id.Pred.t * Cpred.t

let empty_transparent_state = (Id.Pred.empty, Cpred.empty)
let full_transparent_state = (Id.Pred.full, Cpred.full)
let var_full_transparent_state = (Id.Pred.full, Cpred.empty)
let cst_full_transparent_state = (Id.Pred.empty, Cpred.full)

type 'a tableKey =
  | ConstKey of constant
  | VarKey of Id.t
  | RelKey of 'a


type inv_rel_key = int (* index in the [rel_context] part of environment
			  starting by the end, {\em inverse}
			  of de Bruijn indice *)

type id_key = inv_rel_key tableKey

let eq_id_key ik1 ik2 =
  if ik1 == ik2 then true
  else match ik1,ik2 with
  | ConstKey cst1, ConstKey cst2 -> kn_equal (user_con cst1) (user_con cst2)
  | VarKey id1, VarKey id2 -> Id.equal id1 id2
  | RelKey k1, RelKey k2 -> Int.equal k1 k2
  | _ -> false

let eq_con_chk cst1 cst2 = kn_equal (user_con cst1) (user_con cst2)
let eq_mind_chk mind1 mind2 = kn_equal (user_mind mind1) (user_mind mind2)
let eq_ind_chk (kn1,i1) (kn2,i2) = Int.equal i1 i2 && eq_mind_chk kn1 kn2

(** Compatibility layers *)

(** Backward compatibility for [Id.t] *)

type identifier = Id.t

let id_eq = Id.equal
let id_ord = Id.compare
let check_ident_soft = Id.check_soft
let check_ident = Id.check
let string_of_id = Id.to_string
let id_of_string = Id.of_string

module Idset = Id.Set
module Idmap = Id.Map
module Idpred = Id.Pred

(** / End of backward compatibility *)

(** Compatibility layer for [Dir_path] *)

type dir_path = Dir_path.t
let dir_path_ord = Dir_path.compare
let dir_path_eq = Dir_path.equal
let make_dirpath = Dir_path.make
let repr_dirpath = Dir_path.repr
let empty_dirpath = Dir_path.empty
let is_empty_dirpath = Dir_path.is_empty
let string_of_dirpath = Dir_path.to_string
let initial_dir = Dir_path.initial

(** / End of compatibility layer for [Dir_path] *)

(** Compatibility layer for [MBId] *)

type mod_bound_id = MBId.t
let mod_bound_id_ord = MBId.compare
let mod_bound_id_eq = MBId.equal
let make_mbid = MBId.make
let repr_mbid = MBId.repr
let debug_string_of_mbid = MBId.debug_to_string
let string_of_mbid = MBId.to_string
let id_of_mbid = MBId.to_id

(** / End of compatibility layer for [MBId] *)

(** Compatibility layer for [Label] *)

type label = Id.t

let mk_label = Label.make
let string_of_label = Label.to_string
let pr_label = Label.print
let id_of_label = Label.to_id
let label_of_id = Label.of_id
let eq_label = Label.equal

(** / End of compatibility layer for [Label] *)

(** Compatibility layer for [Name] *)

let name_eq = Name.equal

(** / End of compatibility layer for [Name] *)
