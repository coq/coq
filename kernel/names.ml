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

module DirPath =
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
  type t = int * Id.t * DirPath.t

  let gen =
    let seed = ref 0 in fun () ->
      let ans = !seed in
      let () = incr seed in
      ans

  let make dir s = (gen(), s, dir)

  let repr mbid = mbid

  let to_string (i, s, p) =
    DirPath.to_string p ^ "." ^ s

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
          DirPath.compare dpl dpr

  let equal x y = Int.equal (compare x y) 0

  let to_id (_, s, _) = s

  module Self_Hashcons =
    struct
      type _t = t
      type t = _t
      type u = (Id.t -> Id.t) * (DirPath.t -> DirPath.t)
      let hashcons (hid,hdir) (n,s,dir) = (n,hid s,hdir dir)
      let equal ((n1,s1,dir1) as x) ((n2,s2,dir2) as y) =
        (x == y) ||
        (Int.equal n1 n2 && s1 == s2 && dir1 == dir2)
      let hash = Hashtbl.hash
    end

  module HashMBId = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons HashMBId.generate (Id.hcons, DirPath.hcons)

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

module ModPath = struct

  type t =
    | MPfile of DirPath.t
    | MPbound of MBId.t
    | MPdot of t * Label.t

  type module_path = t

  let rec is_bound = function
    | MPbound _ -> true
    | MPdot(mp,_) -> is_bound mp
    | _ -> false

  let rec to_string = function
    | MPfile sl -> DirPath.to_string sl
    | MPbound uid -> MBId.to_string uid
    | MPdot (mp,l) -> to_string mp ^ "." ^ Label.to_string l

  (** we compare labels first if both are MPdots *)
  let rec compare mp1 mp2 =
    if mp1 == mp2 then 0
    else match mp1, mp2 with
      | MPfile p1, MPfile p2 -> DirPath.compare p1 p2
      | MPbound id1, MPbound id2 -> MBId.compare id1 id2
      | MPdot (mp1, l1), MPdot (mp2, l2) ->
        let c = String.compare l1 l2 in
        if not (Int.equal c 0) then c
        else compare mp1 mp2
      | MPfile _, _ -> -1
      | MPbound _, MPfile _ -> 1
      | MPbound _, MPdot _ -> -1
      | MPdot _, _ -> 1

  let equal mp1 mp2 = Int.equal (compare mp1 mp2) 0

  let initial = MPfile DirPath.initial

  module Self_Hashcons = struct
    type t = module_path
    type u = (DirPath.t -> DirPath.t) * (MBId.t -> MBId.t) *
	(string -> string)
    let rec hashcons (hdir,huniqid,hstr as hfuns) = function
      | MPfile dir -> MPfile (hdir dir)
      | MPbound m -> MPbound (huniqid m)
      | MPdot (md,l) -> MPdot (hashcons hfuns md, hstr l)
    let rec equal d1 d2 =
      d1 == d2 ||
      match d1,d2 with
      | MPfile dir1, MPfile dir2 -> dir1 == dir2
      | MPbound m1, MPbound m2 -> m1 == m2
      | MPdot (mod1,l1), MPdot (mod2,l2) -> l1 == l2 && equal mod1 mod2
      | _ -> false
    let hash = Hashtbl.hash
  end

  module HashMP = Hashcons.Make(Self_Hashcons)

  let hcons =
    Hashcons.simple_hcons HashMP.generate
      (DirPath.hcons,MBId.hcons,String.hcons)

end

module MPset = Set.Make(ModPath)
module MPmap = Map.Make(ModPath)

(** {6 Kernel names } *)

module KerName = struct

  type t = ModPath.t * DirPath.t * Label.t

  type kernel_name = t

  let make mp dir l = (mp,dir,l)
  let repr kn = kn

  let modpath (mp,_,_) = mp
  let label (_,_,l) = l

  let to_string (mp,dir,l) =
    let dp =
      if DirPath.is_empty dir then "."
      else "#" ^ DirPath.to_string dir ^ "#"
    in
    ModPath.to_string mp ^ dp ^ Label.to_string l

  let print kn = str (to_string kn)

  let compare (kn1 : kernel_name) (kn2 : kernel_name) =
    if kn1 == kn2 then 0
    else
      let mp1,dir1,l1 = kn1 and mp2,dir2,l2 = kn2 in
      let c = String.compare l1 l2 in
      if not (Int.equal c 0) then c
      else
        let c = DirPath.compare dir1 dir2 in
        if not (Int.equal c 0) then c
        else ModPath.compare mp1 mp2

  let equal kn1 kn2 = Int.equal (compare kn1 kn2) 0

  module Self_Hashcons = struct
    type t = kernel_name
    type u = (ModPath.t -> ModPath.t) * (DirPath.t -> DirPath.t)
        * (string -> string)
    let hashcons (hmod,hdir,hstr) (mp,dir,l) =
      (hmod mp,hdir dir,hstr l)
    let equal (mp1,dir1,l1) (mp2,dir2,l2) =
      mp1 == mp2 && dir1 == dir2 && l1 == l2
    let hash = Hashtbl.hash
  end

  module HashKN = Hashcons.Make(Self_Hashcons)

  let hcons =
    Hashcons.simple_hcons HashKN.generate
      (ModPath.hcons,DirPath.hcons,String.hcons)

end

module KNmap = Map.Make(KerName)
module KNpred = Predicate.Make(KerName)
module KNset = Set.Make(KerName)

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

module KerPair = struct

  type t =
    | Same of KerName.t (** user = canonical *)
    | Dual of KerName.t * KerName.t (** user then canonical *)

  type kernel_pair = t

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
    | Same kn -> "(" ^ KerName.to_string kn ^ ")"
    | Dual (knu,knc) ->
      "(" ^ KerName.to_string knu ^ "," ^ KerName.to_string knc ^ ")"

  (** Default comparison is on the canonical part *)
  let equal x y = x == y || KerName.equal (canonical x) (canonical y)

  (** For ordering kernel pairs, both user or canonical parts may make
      sense, according to your needs : user for the environments, canonical
      for other uses (ex: non-logical things). *)

  module UserOrd = struct
    type t = kernel_pair
    let compare x y = KerName.compare (user x) (user y)
  end

  module CanOrd = struct
    type t = kernel_pair
    let compare x y = KerName.compare (canonical x) (canonical y)
  end

  (** Hash-consing : we discriminate only on the user part, since having
      the same user part implies having the same canonical part
      (invariant of the system). *)

  module Self_Hashcons =
    struct
      type t = kernel_pair
      type u = KerName.t -> KerName.t
      let hashcons hkn = function
        | Same kn -> Same (hkn kn)
        | Dual (knu,knc) -> make (hkn knu) (hkn knc)
      let equal x y = (user x) == (user y)
      let hash = Hashtbl.hash
    end

  module HashKP = Hashcons.Make(Self_Hashcons)

end

(** {6 Constant names } *)

type constant = KerPair.t

let canonical_con = KerPair.canonical
let user_con = KerPair.user
let constant_of_kn = KerPair.same
let constant_of_kn_equiv = KerPair.make
let make_con mp dir l = KerPair.same (KerName.make mp dir l)
let make_con_dual mpu mpc dir l =
  KerPair.dual (KerName.make mpu dir l) (KerName.make mpc dir l)
let make_con_equiv mpu mpc dir l =
  if mpu == mpc then make_con mpc dir l else make_con_dual mpu mpc dir l
let repr_con c = KerName.repr (user_con c)

let eq_constant = KerPair.equal
let con_ord = KerPair.CanOrd.compare
let con_user_ord = KerPair.UserOrd.compare

let con_label cst = KerName.label (canonical_con cst)
let con_modpath cst = KerName.modpath (canonical_con cst)

let string_of_con cst = KerName.to_string (canonical_con cst)
let pr_con cst = str (string_of_con cst)
let debug_string_of_con = KerPair.debug_to_string
let debug_pr_con cst = str (debug_string_of_con cst)

let con_with_label cst lbl =
  let (mp1,dp1,l1) = KerName.repr (user_con cst)
  and (mp2,dp2,l2) = KerName.repr (canonical_con cst) in
  assert (String.equal l1 l2 && DirPath.equal dp1 dp2);
  if String.equal lbl l1
  then cst
  else make_con_equiv mp1 mp2 dp1 lbl

module Cmap = Map.Make(KerPair.CanOrd)
module Cmap_env = Map.Make(KerPair.UserOrd)
module Cpred = Predicate.Make(KerPair.CanOrd)
module Cset = Set.Make(KerPair.CanOrd)
module Cset_env = Set.Make(KerPair.UserOrd)


(** {6 Names of mutual inductive types } *)

(** The same thing is done for mutual inductive names
    it replaces also the old mind_equiv field of mutual
    inductive types *)
(** Beware: first inductive has index 0 *)
(** Beware: first constructor has index 1 *)

type mutual_inductive = KerPair.t
type inductive = mutual_inductive * int
type constructor = inductive * int

let mind_modpath mind = KerName.modpath (KerPair.user mind)
let ind_modpath ind = mind_modpath (fst ind)
let constr_modpath c = ind_modpath (fst c)

let mind_of_kn = KerPair.same
let mind_of_kn_equiv = KerPair.make
let make_mind mp dir l = KerPair.same (KerName.make mp dir l)
let make_mind_dual mpu mpc dir l =
  KerPair.dual (KerName.make mpu dir l) (KerName.make mpc dir l)
let make_mind_equiv mpu mpc dir l =
  if mpu == mpc then make_mind mpu dir l else make_mind_dual mpu mpc dir l
let canonical_mind = KerPair.canonical
let user_mind = KerPair.user
let repr_mind mind = KerName.repr (user_mind mind)
let mind_label mind = KerName.label (user_mind mind)

let eq_mind = KerPair.equal
let mind_ord = KerPair.CanOrd.compare
let mind_user_ord = KerPair.UserOrd.compare

let string_of_mind mind = KerName.to_string (user_mind mind)
let pr_mind mind = str (string_of_mind mind)
let debug_string_of_mind = KerPair.debug_to_string
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

module Mindmap = Map.Make(KerPair.CanOrd)
module Mindset = Set.Make(KerPair.CanOrd)
module Mindmap_env = Map.Make(KerPair.UserOrd)

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

let hcons_con = Hashcons.simple_hcons KerPair.HashKP.generate KerName.hcons
let hcons_mind = Hashcons.simple_hcons KerPair.HashKP.generate KerName.hcons
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
  | ConstKey c1, ConstKey c2 -> KerName.equal (user_con c1) (user_con c2)
  | VarKey id1, VarKey id2 -> Id.equal id1 id2
  | RelKey k1, RelKey k2 -> Int.equal k1 k2
  | _ -> false

let eq_con_chk cst1 cst2 = KerName.equal (user_con cst1) (user_con cst2)
let eq_mind_chk mind1 mind2 = KerName.equal (user_mind mind1) (user_mind mind2)
let eq_ind_chk (kn1,i1) (kn2,i2) = Int.equal i1 i2 && eq_mind_chk kn1 kn2

(** Compatibility layers *)

(** Backward compatibility for [Id] *)

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

(** Compatibility layer for [Name] *)

let name_eq = Name.equal

(** Compatibility layer for [DirPath] *)

type dir_path = DirPath.t
let dir_path_ord = DirPath.compare
let dir_path_eq = DirPath.equal
let make_dirpath = DirPath.make
let repr_dirpath = DirPath.repr
let empty_dirpath = DirPath.empty
let is_empty_dirpath = DirPath.is_empty
let string_of_dirpath = DirPath.to_string
let initial_dir = DirPath.initial

(** Compatibility layer for [MBId] *)

type mod_bound_id = MBId.t
let mod_bound_id_ord = MBId.compare
let mod_bound_id_eq = MBId.equal
let make_mbid = MBId.make
let repr_mbid = MBId.repr
let debug_string_of_mbid = MBId.debug_to_string
let string_of_mbid = MBId.to_string
let id_of_mbid = MBId.to_id

(** Compatibility layer for [Label] *)

type label = Id.t
let mk_label = Label.make
let string_of_label = Label.to_string
let pr_label = Label.print
let id_of_label = Label.to_id
let label_of_id = Label.of_id
let eq_label = Label.equal

(** Compatibility layer for [ModPath] *)

type module_path = ModPath.t =
  | MPfile of DirPath.t
  | MPbound of MBId.t
  | MPdot of module_path * Label.t
let check_bound_mp = ModPath.is_bound
let string_of_mp = ModPath.to_string
let mp_ord = ModPath.compare
let mp_eq = ModPath.equal
let initial_path = ModPath.initial

(** Compatibility layer for [KerName] *)

type kernel_name = KerName.t
let make_kn = KerName.make
let repr_kn = KerName.repr
let modpath = KerName.modpath
let label = KerName.label
let string_of_kn = KerName.to_string
let pr_kn = KerName.print
let kn_ord = KerName.compare
let kn_equal = KerName.equal
