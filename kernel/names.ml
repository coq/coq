(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Util

(** {6 Identifiers } *)

module Id =
struct
  type t = string

  let equal = String.equal

  let compare = String.compare

  let hash = String.hash

  let check_soft x =
    let iter (fatal, x) =
      if fatal then Errors.error x else Pp.msg_warning (str x)
    in
    Option.iter iter (Unicode.ident_refutation x)

  let is_valid s = match Unicode.ident_refutation s with
  | None -> true
  | Some _ -> false

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
  module Map = CMap.Make(Self)

  module Pred = Predicate.Make(Self)

  module List = String.List

  let hcons = String.hcons

end


module Name =
struct
  type t = Name of Id.t | Anonymous

  let compare n1 n2 = match n1, n2 with
    | Anonymous, Anonymous -> 0
    | Name id1, Name id2 -> Id.compare id1 id2
    | Anonymous, Name _ -> -1
    | Name _, Anonymous -> 1

  let equal n1 n2 = match n1, n2 with
    | Anonymous, Anonymous -> true
    | Name id1, Name id2 -> String.equal id1 id2
    | _ -> false

  let hash = function
  | Anonymous -> 0
  | Name id -> Id.hash id

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
      let hash = hash
    end

  module Hname = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons Hname.generate Hname.hcons Id.hcons

end

type name = Name.t = Name of Id.t | Anonymous
(** Alias, to import constructors. *)

(** {6 Various types based on identifiers } *)

type variable = Id.t

type module_ident = Id.t

module ModIdset = Id.Set
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

  let rec equal p1 p2 = p1 == p2 || match p1, p2 with
  | [], [] -> true
  | id1 :: p1, id2 :: p2 -> Id.equal id1 id2 && equal p1 p2
  | _ -> false

  let rec hash accu = function
  | [] -> accu
  | id :: dp ->
    let accu = Hashset.Combine.combine (Id.hash id) accu in
    hash accu dp

  let hash dp = hash 0 dp

  let make x = x
  let repr x = x

  let empty = []

  let is_empty d = match d with [] -> true | _ -> false

  let to_string = function
    | [] -> "<>"
    | sl -> String.concat "." (List.rev_map Id.to_string sl)

  let initial = [default_module_name]

  module Hdir = Hashcons.Hlist(Id)

  let hcons = Hashcons.recursive_hcons Hdir.generate Hdir.hcons Id.hcons

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

  let equal x y = x == y ||
    let (i1, id1, p1) = x in
    let (i2, id2, p2) = y in
    Int.equal i1 i2 && Id.equal id1 id2 && DirPath.equal p1 p2

  let to_id (_, s, _) = s

  open Hashset.Combine

  let hash (i, id, dp) =
    combine3 (Int.hash i) (Id.hash id) (DirPath.hash dp)

  module Self_Hashcons =
    struct
      type _t = t
      type t = _t
      type u = (Id.t -> Id.t) * (DirPath.t -> DirPath.t)
      let hashcons (hid,hdir) (n,s,dir) = (n,hid s,hdir dir)
      let equal ((n1,s1,dir1) as x) ((n2,s2,dir2) as y) =
        (x == y) ||
        (Int.equal n1 n2 && s1 == s2 && dir1 == dir2)
      let hash = hash
    end

  module HashMBId = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons HashMBId.generate HashMBId.hcons (Id.hcons, DirPath.hcons)

end

module MBImap = CMap.Make(MBId)
module MBIset = Set.Make(MBId)

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

  let rec equal mp1 mp2 = mp1 == mp2 ||
    match mp1, mp2 with
    | MPfile p1, MPfile p2 -> DirPath.equal p1 p2
    | MPbound id1, MPbound id2 -> MBId.equal id1 id2
    | MPdot (mp1, l1), MPdot (mp2, l2) -> String.equal l1 l2 && equal mp1 mp2
    | (MPfile _ | MPbound _ | MPdot _), _ -> false

  open Hashset.Combine

  let rec hash = function
  | MPfile dp -> combinesmall 1 (DirPath.hash dp)
  | MPbound id -> combinesmall 2 (MBId.hash id)
  | MPdot (mp, lbl) ->
    combinesmall 3 (combine (hash mp) (Label.hash lbl))

  let initial = MPfile DirPath.initial

  let rec dp = function
  | MPfile sl -> sl
  | MPbound (_,_,dp) -> dp
  | MPdot (mp,l) -> dp mp

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
    let hash = hash
  end

  module HashMP = Hashcons.Make(Self_Hashcons)

  let hcons =
    Hashcons.simple_hcons HashMP.generate HashMP.hcons
      (DirPath.hcons,MBId.hcons,String.hcons)

end

module MPset = Set.Make(ModPath)
module MPmap = CMap.Make(ModPath)

(** {6 Kernel names } *)

module KerName = struct

  type t = {
    canary : Canary.t;
    modpath : ModPath.t;
    dirpath : DirPath.t;
    knlabel : Label.t;
    mutable refhash : int;
    (** Lazily computed hash. If unset, it is set to negative values. *)
  }

  let canary = Canary.obj

  type kernel_name = t

  let make modpath dirpath knlabel =
    { modpath; dirpath; knlabel; refhash = -1; canary; }
  let repr kn = (kn.modpath, kn.dirpath, kn.knlabel)

  let make2 modpath knlabel =
    { modpath; dirpath = DirPath.empty; knlabel; refhash = -1; canary; }

  let modpath kn = kn.modpath
  let label kn = kn.knlabel

  let to_string kn =
    let dp =
      if DirPath.is_empty kn.dirpath then "."
      else "#" ^ DirPath.to_string kn.dirpath ^ "#"
    in
    ModPath.to_string kn.modpath ^ dp ^ Label.to_string kn.knlabel

  let print kn = str (to_string kn)

  let compare (kn1 : kernel_name) (kn2 : kernel_name) =
    if kn1 == kn2 then 0
    else
      let c = String.compare kn1.knlabel kn2.knlabel in
      if not (Int.equal c 0) then c
      else
        let c = DirPath.compare kn1.dirpath kn2.dirpath in
        if not (Int.equal c 0) then c
        else ModPath.compare kn1.modpath kn2.modpath

  let equal kn1 kn2 =
    let h1 = kn1.refhash in
    let h2 = kn2.refhash in
    if 0 <= h1 && 0 <= h2 && not (Int.equal h1 h2) then false
    else
      Label.equal kn1.knlabel kn2.knlabel &&
      DirPath.equal kn1.dirpath kn2.dirpath &&
      ModPath.equal kn1.modpath kn2.modpath

  open Hashset.Combine

  let hash kn =
    let h = kn.refhash in
    if h < 0 then
      let { modpath = mp; dirpath = dp; knlabel = lbl; } = kn in
      let h = combine3 (ModPath.hash mp) (DirPath.hash dp) (Label.hash lbl) in
      (* Ensure positivity on all platforms. *)
      let h = h land 0x3FFFFFFF in
      let () = kn.refhash <- h in
      h
    else h

  module Self_Hashcons = struct
    type t = kernel_name
    type u = (ModPath.t -> ModPath.t) * (DirPath.t -> DirPath.t)
        * (string -> string)
    let hashcons (hmod,hdir,hstr) kn =
      let { modpath = mp; dirpath = dp; knlabel = l; refhash; } = kn in
      { modpath = hmod mp; dirpath = hdir dp; knlabel = hstr l; refhash; canary; }
    let equal kn1 kn2 =
      kn1.modpath == kn2.modpath && kn1.dirpath == kn2.dirpath &&
        kn1.knlabel == kn2.knlabel
    let hash = hash
  end

  module HashKN = Hashcons.Make(Self_Hashcons)

  let hcons =
    Hashcons.simple_hcons HashKN.generate HashKN.hcons
      (ModPath.hcons,DirPath.hcons,String.hcons)
end

module KNmap = HMap.Make(KerName)
module KNpred = Predicate.Make(KerName)
module KNset = KNmap.Set

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
  let make knu knc = if knu == knc then Same knc else Dual (knu,knc)

  let make1 = same
  let make2 mp l = same (KerName.make2 mp l)
  let make3 mp dir l = same (KerName.make mp dir l)
  let repr3 kp = KerName.repr (user kp)
  let label kp = KerName.label (user kp)
  let modpath kp = KerName.modpath (user kp)

  let change_label kp lbl =
    let (mp1,dp1,l1) = KerName.repr (user kp)
    and (mp2,dp2,l2) = KerName.repr (canonical kp) in
    assert (String.equal l1 l2 && DirPath.equal dp1 dp2);
    if String.equal lbl l1 then kp
    else
      let kn = KerName.make mp1 dp1 lbl in
      if mp1 == mp2 then same kn
      else make kn (KerName.make mp2 dp2 lbl)

  let to_string kp = KerName.to_string (user kp)
  let print kp = str (to_string kp)

  let debug_to_string = function
    | Same kn -> "(" ^ KerName.to_string kn ^ ")"
    | Dual (knu,knc) ->
      "(" ^ KerName.to_string knu ^ "," ^ KerName.to_string knc ^ ")"

  let debug_print kp = str (debug_to_string kp)

  (** For ordering kernel pairs, both user or canonical parts may make
      sense, according to your needs : user for the environments, canonical
      for other uses (ex: non-logical things). *)

  module UserOrd = struct
    type t = kernel_pair
    let compare x y = KerName.compare (user x) (user y)
    let equal x y = x == y || KerName.equal (user x) (user y)
    let hash x = KerName.hash (user x)
  end

  module CanOrd = struct
    type t = kernel_pair
    let compare x y = KerName.compare (canonical x) (canonical y)
    let equal x y = x == y || KerName.equal (canonical x) (canonical y)
    let hash x = KerName.hash (canonical x)
  end

  (** Default comparison is on the canonical part *)
  let equal = CanOrd.equal

  (** Hash-consing : we discriminate only on the user part, since having
      the same user part implies having the same canonical part
      (invariant of the system). *)

  let hash = function
  | Same kn -> KerName.hash kn
  | Dual (kn, _) -> KerName.hash kn

  module Self_Hashcons =
    struct
      type t = kernel_pair
      type u = KerName.t -> KerName.t
      let hashcons hkn = function
        | Same kn -> Same (hkn kn)
        | Dual (knu,knc) -> make (hkn knu) (hkn knc)
      let equal x y = (user x) == (user y)
      let hash = hash
    end

  module HashKP = Hashcons.Make(Self_Hashcons)

end

(** {6 Constant Names} *)

module Constant = KerPair

module Cmap = HMap.Make(Constant.CanOrd)
module Cmap_env = HMap.Make(Constant.UserOrd)
module Cpred = Predicate.Make(Constant.CanOrd)
module Cset = Cmap.Set
module Cset_env = Cmap_env.Set

(** {6 Names of mutual inductive types } *)

module MutInd = KerPair

module Mindmap = HMap.Make(MutInd.CanOrd)
module Mindset = Mindmap.Set
module Mindmap_env = HMap.Make(MutInd.UserOrd)

(** Beware: first inductive has index 0 *)
(** Beware: first constructor has index 1 *)

type inductive = MutInd.t * int
type constructor = inductive * int

let ind_modpath (mind,_) = MutInd.modpath mind
let constr_modpath (ind,_) = ind_modpath ind

let ith_mutual_inductive (mind, _) i = (mind, i)
let ith_constructor_of_inductive ind i = (ind, i)
let ith_constructor_of_pinductive (ind,u) i = ((ind,i),u)
let inductive_of_constructor (ind, i) = ind
let index_of_constructor (ind, i) = i

let eq_ind (m1, i1) (m2, i2) = Int.equal i1 i2 && MutInd.equal m1 m2
let eq_user_ind (m1, i1) (m2, i2) =
  Int.equal i1 i2 && MutInd.UserOrd.equal m1 m2

let ind_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then MutInd.CanOrd.compare m1 m2 else c
let ind_user_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then MutInd.UserOrd.compare m1 m2 else c

let ind_hash (m, i) =
  Hashset.Combine.combine (MutInd.hash m) (Int.hash i)
let ind_user_hash (m, i) =
  Hashset.Combine.combine (MutInd.UserOrd.hash m) (Int.hash i)

let eq_constructor (ind1, j1) (ind2, j2) = Int.equal j1 j2 && eq_ind ind1 ind2
let eq_user_constructor (ind1, j1) (ind2, j2) =
  Int.equal j1 j2 && eq_user_ind ind1 ind2

let constructor_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_ord ind1 ind2 else c
let constructor_user_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_user_ord ind1 ind2 else c

let constructor_hash (ind, i) =
  Hashset.Combine.combine (ind_hash ind) (Int.hash i)
let constructor_user_hash (ind, i) =
  Hashset.Combine.combine (ind_user_hash ind) (Int.hash i)

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
  | EvalConstRef of Constant.t

let eq_egr e1 e2 = match e1, e2 with
    EvalConstRef con1, EvalConstRef con2 -> Constant.equal con1 con2
  | EvalVarRef id1, EvalVarRef id2 -> Id.equal id1 id2
  | _, _ -> false

(** {6 Hash-consing of name objects } *)

module Hind = Hashcons.Make(
  struct
    type t = inductive
    type u = MutInd.t -> MutInd.t
    let hashcons hmind (mind, i) = (hmind mind, i)
    let equal (mind1,i1) (mind2,i2) = mind1 == mind2 && Int.equal i1 i2
    let hash = ind_hash
  end)

module Hconstruct = Hashcons.Make(
  struct
    type t = constructor
    type u = inductive -> inductive
    let hashcons hind (ind, j) = (hind ind, j)
    let equal (ind1, j1) (ind2, j2) = ind1 == ind2 && Int.equal j1 j2
    let hash = constructor_hash
  end)

let hcons_con = Hashcons.simple_hcons Constant.HashKP.generate Constant.HashKP.hcons KerName.hcons
let hcons_mind = Hashcons.simple_hcons MutInd.HashKP.generate MutInd.HashKP.hcons KerName.hcons
let hcons_ind = Hashcons.simple_hcons Hind.generate Hind.hcons hcons_mind
let hcons_construct = Hashcons.simple_hcons Hconstruct.generate Hconstruct.hcons hcons_ind

(*****************)

type transparent_state = Id.Pred.t * Cpred.t

let empty_transparent_state = (Id.Pred.empty, Cpred.empty)
let full_transparent_state = (Id.Pred.full, Cpred.full)
let var_full_transparent_state = (Id.Pred.full, Cpred.empty)
let cst_full_transparent_state = (Id.Pred.empty, Cpred.full)

type 'a tableKey =
  | ConstKey of 'a
  | VarKey of Id.t
  | RelKey of Int.t

type inv_rel_key = int (* index in the [rel_context] part of environment
			  starting by the end, {\em inverse}
			  of de Bruijn indice *)

let eq_table_key f ik1 ik2 =
  if ik1 == ik2 then true
  else match ik1,ik2 with
  | ConstKey c1, ConstKey c2 -> f c1 c2
  | VarKey id1, VarKey id2 -> Id.equal id1 id2
  | RelKey k1, RelKey k2 -> Int.equal k1 k2
  | _ -> false

let eq_con_chk = Constant.UserOrd.equal
let eq_mind_chk = MutInd.UserOrd.equal
let eq_ind_chk (kn1,i1) (kn2,i2) = Int.equal i1 i2 && eq_mind_chk kn1 kn2


(*******************************************************************)
(** Compatibility layers *)

(** Backward compatibility for [Id] *)

type identifier = Id.t

let id_eq = Id.equal
let id_ord = Id.compare
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

(** Compatibility layer for [Constant] *)

type constant = Constant.t


module Projection = 
struct 
  type t = constant * bool
    
  let make c b = (c, b)

  let constant = fst
  let unfolded = snd
  let unfold (c, b as p) = if b then p else (c, true)
  let equal (c, b) (c', b') = Constant.equal c c' && b == b'

  let hash (c, b) = (if b then 0 else 1) + Constant.hash c

  module Self_Hashcons =
    struct
      type _t = t
      type t = _t
      type u = Constant.t -> Constant.t
      let hashcons hc (c,b) = (hc c,b)
      let equal ((c,b) as x) ((c',b') as y) =
        x == y || (c == c' && b == b')
      let hash = hash
    end

  module HashProjection = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons HashProjection.generate HashProjection.hcons hcons_con

  let compare (c, b) (c', b') =
    if b == b' then Constant.CanOrd.compare c c'
    else if b then 1 else -1

  let map f (c, b as x) =
    let c' = f c in
      if c' == c then x else (c', b)
end

type projection = Projection.t

let constant_of_kn = Constant.make1
let constant_of_kn_equiv = Constant.make
let make_con = Constant.make3
let repr_con = Constant.repr3
let canonical_con = Constant.canonical
let user_con = Constant.user
let con_label = Constant.label
let con_modpath = Constant.modpath
let eq_constant = Constant.equal
let eq_constant_key = Constant.UserOrd.equal
let con_ord = Constant.CanOrd.compare
let con_user_ord = Constant.UserOrd.compare
let string_of_con = Constant.to_string
let pr_con = Constant.print
let debug_string_of_con = Constant.debug_to_string
let debug_pr_con = Constant.debug_print
let con_with_label = Constant.change_label

(** Compatibility layer for [MutInd] *)

type mutual_inductive = MutInd.t
let mind_of_kn = MutInd.make1
let mind_of_kn_equiv = MutInd.make
let make_mind = MutInd.make3
let canonical_mind = MutInd.canonical
let user_mind = MutInd.user
let repr_mind = MutInd.repr3
let mind_label = MutInd.label
let mind_modpath = MutInd.modpath
let eq_mind = MutInd.equal
let mind_ord = MutInd.CanOrd.compare
let mind_user_ord = MutInd.UserOrd.compare
let string_of_mind = MutInd.to_string
let pr_mind = MutInd.print
let debug_string_of_mind = MutInd.debug_to_string
let debug_pr_mind = MutInd.debug_print
