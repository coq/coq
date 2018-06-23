(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

(** Representation and operations on identifiers. *)
module Id =
struct
  type t = string

  let equal = String.equal

  let compare = String.compare

  let hash = String.hash

  let check_valid ?(strict=true) x =
    let iter (fatal, x) = if fatal || strict then CErrors.user_err Pp.(str x) in
    Option.iter iter (Unicode.ident_refutation x)

  let is_valid s = match Unicode.ident_refutation s with
  | None -> true
  | Some _ -> false

  let of_bytes s =
    let s = Bytes.to_string s in
    check_valid s;
    String.hcons s

  let of_string s =
    let () = check_valid s in
    String.hcons s

  let of_string_soft s =
    let () = check_valid ~strict:false s in
    String.hcons s

  let to_string id = id

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

(** Representation and operations on identifiers that are allowed to be anonymous
    (i.e. "_" in concrete syntax). *)
module Name =
struct
  type t = Anonymous     (** anonymous identifier *)
	 | Name of Id.t  (** non-anonymous identifier *)

  let mk_name id =
    Name id

  let is_anonymous = function
    | Anonymous -> true
    | Name _ -> false

  let is_name = is_anonymous %> not

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

  let print = function
    | Anonymous -> str "_"
    | Name id -> Id.print id

  module Self_Hashcons =
    struct
      type nonrec t = t
      type u = Id.t -> Id.t
      let hashcons hident = function
        | Name id -> Name (hident id)
        | n -> n
      let eq n1 n2 =
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

(** Alias, to import constructors. *)
type name = Name.t = Anonymous | Name of Id.t

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

  let compare = List.compare Id.compare
  let equal = List.equal Id.equal

  let rec hash accu = function
  | [] -> accu
  | id :: dp ->
    let accu = Hashset.Combine.combine (Id.hash id) accu in
    hash accu dp

  let hash dp = hash 0 dp

  let make x = x
  let repr x = x

  let empty = []

  let is_empty = List.is_empty

  let to_string = function
    | [] -> "<>"
    | sl -> String.concat "." (List.rev_map Id.to_string sl)

  let print dp = str (to_string dp)

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
    "<"^DirPath.to_string p ^"#" ^ s ^"#"^ string_of_int i^">"

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
      type nonrec t = t
      type u = (Id.t -> Id.t) * (DirPath.t -> DirPath.t)
      let hashcons (hid,hdir) (n,s,dir) = (n,hid s,hdir dir)
      let eq ((n1,s1,dir1) as x) ((n2,s2,dir2) as y) =
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

  let rec debug_to_string = function
    | MPfile sl -> DirPath.to_string sl
    | MPbound uid -> MBId.debug_to_string uid
    | MPdot (mp,l) -> debug_to_string mp ^ "." ^ Label.to_string l

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
    let eq d1 d2 =
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
    modpath : ModPath.t;
    dirpath : DirPath.t;
    knlabel : Label.t;
    mutable refhash : int;
    (** Lazily computed hash. If unset, it is set to negative values. *)
  }

  type kernel_name = t

  let make modpath dirpath knlabel =
    { modpath; dirpath; knlabel; refhash = -1; }
  let repr kn = (kn.modpath, kn.dirpath, kn.knlabel)

  let make2 modpath knlabel =
    { modpath; dirpath = DirPath.empty; knlabel; refhash = -1; }

  let modpath kn = kn.modpath
  let label kn = kn.knlabel

  let to_string_gen mp_to_string kn =
    let dp =
      if DirPath.is_empty kn.dirpath then "."
      else "#" ^ DirPath.to_string kn.dirpath ^ "#"
    in
    mp_to_string kn.modpath ^ dp ^ Label.to_string kn.knlabel

  let to_string kn = to_string_gen ModPath.to_string kn

  let debug_to_string kn = to_string_gen ModPath.debug_to_string kn

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
      { modpath = hmod mp; dirpath = hdir dp; knlabel = hstr l; refhash; }
    let eq kn1 kn2 =
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
      in a given environment (though with backtracking, the hash-table can
      contains pairs with same user part but different canonical part from
      a previous state of the session)

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
  let make knu knc = if KerName.equal knu knc then Same knc else Dual (knu,knc)

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
    | Same kn -> "(" ^ KerName.debug_to_string kn ^ ")"
    | Dual (knu,knc) ->
      "(" ^ KerName.debug_to_string knu ^ "," ^ KerName.debug_to_string knc ^ ")"

  let debug_print kp = str (debug_to_string kp)

  (** For ordering kernel pairs, both user or canonical parts may make
      sense, according to your needs: user for the environments, canonical
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

  module SyntacticOrd = struct
    let compare x y = match x, y with
      | Same knx, Same kny -> KerName.compare knx kny
      | Dual (knux,kncx), Dual (knuy,kncy) ->
        let c = KerName.compare knux knuy in
        if not (Int.equal c 0) then c
        else KerName.compare kncx kncy
      | Same _, _ -> -1
      | Dual _, _ -> 1
    let equal x y = x == y || compare x y = 0
    let hash = function
      | Same kn -> KerName.hash kn
      | Dual (knu, knc) ->
        Hashset.Combine.combine (KerName.hash knu) (KerName.hash knc)
  end

  (** Default (logical) comparison and hash is on the canonical part *)
  let equal = CanOrd.equal
  let hash = CanOrd.hash

  module Self_Hashcons =
    struct
      type t = kernel_pair
      type u = KerName.t -> KerName.t
      let hashcons hkn = function
        | Same kn -> Same (hkn kn)
        | Dual (knu,knc) -> make (hkn knu) (hkn knc)
      let eq x y = (* physical comparison on subterms *)
        x == y ||
        match x,y with
        | Same x, Same y -> x == y
        | Dual (ux,cx), Dual (uy,cy) -> ux == uy && cx == cy
        | (Same _ | Dual _), _ -> false
      (** Hash-consing (despite having the same user part implies having
          the same canonical part is a logical invariant of the system, it
          is not necessarily an invariant in memory, so we treat kernel
          names as they are syntactically for hash-consing) *)
      let hash = function
      | Same kn -> KerName.hash kn
      | Dual (knu, knc) ->
        Hashset.Combine.combine (KerName.hash knu) (KerName.hash knc)
    end

  module HashKP = Hashcons.Make(Self_Hashcons)

end

(** {6 Constant Names} *)

module Constant = KerPair

module Cmap = HMap.Make(Constant.CanOrd)
(** A map whose keys are constants (values of the {!Constant.t} type).
    Keys are ordered wrt. "canonical form" of the constant. *)

module Cmap_env = HMap.Make(Constant.UserOrd)
(** A map whose keys are constants (values of the {!Constant.t} type).
    Keys are ordered wrt. "user form" of the constant. *)

module Cpred = Predicate.Make(Constant.CanOrd)
module Cset = Cmap.Set
module Cset_env = Cmap_env.Set

(** {6 Names of mutual inductive types } *)

module MutInd = KerPair

module Mindmap = HMap.Make(MutInd.CanOrd)
module Mindset = Mindmap.Set
module Mindmap_env = HMap.Make(MutInd.UserOrd)

(** Designation of a (particular) inductive type. *)
type inductive = MutInd.t      (* the name of the inductive type *)
               * int           (* the position of this inductive type
                                  within the block of mutually-recursive inductive types.
                                  BEWARE: indexing starts from 0. *)

(** Designation of a (particular) constructor of a (particular) inductive type. *)
type constructor = inductive   (* designates the inductive type *)
                 * int         (* the index of the constructor
                                  BEWARE: indexing starts from 1. *)

let ind_modpath (mind,_) = MutInd.modpath mind
let constr_modpath (ind,_) = ind_modpath ind

let ith_mutual_inductive (mind, _) i = (mind, i)
let ith_constructor_of_inductive ind i = (ind, i)
let inductive_of_constructor (ind, i) = ind
let index_of_constructor (ind, i) = i

let eq_ind (m1, i1) (m2, i2) = Int.equal i1 i2 && MutInd.equal m1 m2
let eq_user_ind (m1, i1) (m2, i2) =
  Int.equal i1 i2 && MutInd.UserOrd.equal m1 m2
let eq_syntactic_ind (m1, i1) (m2, i2) =
  Int.equal i1 i2 && MutInd.SyntacticOrd.equal m1 m2

let ind_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then MutInd.CanOrd.compare m1 m2 else c
let ind_user_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then MutInd.UserOrd.compare m1 m2 else c
let ind_syntactic_ord (m1, i1) (m2, i2) =
  let c = Int.compare i1 i2 in
  if Int.equal c 0 then MutInd.SyntacticOrd.compare m1 m2 else c

let ind_hash (m, i) =
  Hashset.Combine.combine (MutInd.hash m) (Int.hash i)
let ind_user_hash (m, i) =
  Hashset.Combine.combine (MutInd.UserOrd.hash m) (Int.hash i)
let ind_syntactic_hash (m, i) =
  Hashset.Combine.combine (MutInd.SyntacticOrd.hash m) (Int.hash i)

let eq_constructor (ind1, j1) (ind2, j2) = Int.equal j1 j2 && eq_ind ind1 ind2
let eq_user_constructor (ind1, j1) (ind2, j2) =
  Int.equal j1 j2 && eq_user_ind ind1 ind2
let eq_syntactic_constructor (ind1, j1) (ind2, j2) =
  Int.equal j1 j2 && eq_syntactic_ind ind1 ind2

let constructor_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_ord ind1 ind2 else c
let constructor_user_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_user_ord ind1 ind2 else c
let constructor_syntactic_ord (ind1, j1) (ind2, j2) =
  let c = Int.compare j1 j2 in
  if Int.equal c 0 then ind_syntactic_ord ind1 ind2 else c

let constructor_hash (ind, i) =
  Hashset.Combine.combine (ind_hash ind) (Int.hash i)
let constructor_user_hash (ind, i) =
  Hashset.Combine.combine (ind_user_hash ind) (Int.hash i)
let constructor_syntactic_hash (ind, i) =
  Hashset.Combine.combine (ind_syntactic_hash ind) (Int.hash i)

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

(** {6 Hash-consing of name objects } *)

module Hind = Hashcons.Make(
  struct
    type t = inductive
    type u = MutInd.t -> MutInd.t
    let hashcons hmind (mind, i) = (hmind mind, i)
    let eq (mind1,i1) (mind2,i2) = mind1 == mind2 && Int.equal i1 i2
    let hash = ind_hash
  end)

module Hconstruct = Hashcons.Make(
  struct
    type t = constructor
    type u = inductive -> inductive
    let hashcons hind (ind, j) = (hind ind, j)
    let eq (ind1, j1) (ind2, j2) = ind1 == ind2 && Int.equal j1 j2
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

type mod_bound_id = MBId.t
let eq_constant_key = Constant.UserOrd.equal

(** Compatibility layer for [ModPath] *)

type module_path = ModPath.t =
  | MPfile of DirPath.t
  | MPbound of MBId.t
  | MPdot of module_path * Label.t

(** Compatibility layer for [Constant] *)

module Projection =
struct
  module Repr = struct
    type t =
      { proj_ind : inductive;
        proj_npars : int;
        proj_arg : int;
        proj_name : Label.t; }

    let make proj_ind ~proj_npars ~proj_arg proj_name =
      {proj_ind;proj_npars;proj_arg;proj_name}

    let inductive c = c.proj_ind

    let mind c = fst c.proj_ind

    let constant c = KerPair.change_label (mind c) c.proj_name

    let label c = c.proj_name

    let npars c = c.proj_npars

    let arg c = c.proj_arg

    let equal a b =
      eq_ind a.proj_ind b.proj_ind && Int.equal a.proj_arg b.proj_arg

    let hash p =
      Hashset.Combine.combinesmall p.proj_arg (ind_hash p.proj_ind)

    module SyntacticOrd = struct
      let compare a b =
        let c = ind_syntactic_ord a.proj_ind b.proj_ind in
        if c == 0 then Int.compare a.proj_arg b.proj_arg
        else c

      let equal a b =
        a.proj_arg == b.proj_arg && eq_syntactic_ind a.proj_ind b.proj_ind

      let hash p =
        Hashset.Combine.combinesmall p.proj_arg (ind_hash p.proj_ind)
    end
    module CanOrd = struct
      let compare a b =
        let c = ind_ord a.proj_ind b.proj_ind in
        if c == 0 then Int.compare a.proj_arg b.proj_arg
        else c

      let equal a b =
        a.proj_arg == b.proj_arg && eq_ind a.proj_ind b.proj_ind

      let hash p =
        Hashset.Combine.combinesmall p.proj_arg (ind_hash p.proj_ind)
    end
    module UserOrd = struct
      let compare a b =
        let c = ind_user_ord a.proj_ind b.proj_ind in
        if c == 0 then Int.compare a.proj_arg b.proj_arg
        else c

      let equal a b =
        a.proj_arg == b.proj_arg && eq_user_ind a.proj_ind b.proj_ind

      let hash p =
        Hashset.Combine.combinesmall p.proj_arg (ind_user_hash p.proj_ind)
    end

    let compare a b =
      let c = ind_ord a.proj_ind b.proj_ind in
      if c == 0 then Int.compare a.proj_arg b.proj_arg
      else c

    module Self_Hashcons = struct
      type nonrec t = t
      type u = (inductive -> inductive) * (Id.t -> Id.t)
      let hashcons (hind,hid) p =
        { proj_ind = hind p.proj_ind;
          proj_npars = p.proj_npars;
          proj_arg = p.proj_arg;
          proj_name = hid p.proj_name }
      let eq p p' =
        p == p' || (p.proj_ind == p'.proj_ind && p.proj_npars == p'.proj_npars && p.proj_arg == p'.proj_arg && p.proj_name == p'.proj_name)
      let hash = hash
    end
    module HashRepr = Hashcons.Make(Self_Hashcons)
    let hcons = Hashcons.simple_hcons HashRepr.generate HashRepr.hcons (hcons_ind,Id.hcons)

    let map_npars f p =
      let ind = fst p.proj_ind in
      let npars = p.proj_npars in
      let ind', npars' = f ind npars in
      if ind == ind' && npars == npars' then p
      else {p with proj_ind = (ind',snd p.proj_ind); proj_npars = npars'}

    let map f p = map_npars (fun mind n -> f mind, n) p

    let to_string p = Constant.to_string (constant p)
    let print p = Constant.print (constant p)
  end

  type t = Repr.t * bool

  let make c b = (c, b)

  let mind (c,_) = Repr.mind c
  let inductive (c,_) = Repr.inductive c
  let npars (c,_) = Repr.npars c
  let arg (c,_) = Repr.arg c
  let constant (c,_) = Repr.constant c
  let label (c,_) = Repr.label c
  let repr = fst
  let unfolded = snd
  let unfold (c, b as p) = if b then p else (c, true)

  let equal (c, b) (c', b') = Repr.equal c c' && b == b'

  let hash (c, b) = (if b then 0 else 1) + Repr.hash c

  module SyntacticOrd = struct
    let compare (c, b) (c', b') =
      if b = b' then Repr.SyntacticOrd.compare c c' else -1
    let equal (c, b as x) (c', b' as x') =
      x == x' || b = b' && Repr.SyntacticOrd.equal c c'
    let hash (c, b) = (if b then 0 else 1) + Repr.SyntacticOrd.hash c
  end
  module CanOrd = struct
    let compare (c, b) (c', b') =
      if b = b' then Repr.CanOrd.compare c c' else -1
    let equal (c, b as x) (c', b' as x') =
      x == x' || b = b' && Repr.CanOrd.equal c c'
    let hash (c, b) = (if b then 0 else 1) + Repr.CanOrd.hash c
  end

  module Self_Hashcons =
    struct
      type nonrec t = t
      type u = Repr.t -> Repr.t
      let hashcons hc (c,b) = (hc c,b)
      let eq ((c,b) as x) ((c',b') as y) =
        x == y || (c == c' && b == b')
      let hash = hash
    end

  module HashProjection = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons HashProjection.generate HashProjection.hcons Repr.hcons

  let compare (c, b) (c', b') =
    if b == b' then Repr.compare c c'
    else if b then 1 else -1

  let map f (c, b as x) =
    let c' = Repr.map f c in
    if c' == c then x else (c', b)

  let map_npars f (c, b as x) =
    let c' = Repr.map_npars f c in
    if c' == c then x else (c', b)

  let to_string p = Constant.to_string (constant p)
  let print p = Constant.print (constant p)

end

type projection = Projection.t

module GlobRef = struct

  type t =
    | VarRef of variable           (** A reference to the section-context. *)
    | ConstRef of Constant.t       (** A reference to the environment. *)
    | IndRef of inductive          (** A reference to an inductive type. *)
    | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)

  let equal gr1 gr2 =
    gr1 == gr2 || match gr1,gr2 with
    | ConstRef con1, ConstRef con2 -> Constant.equal con1 con2
    | IndRef kn1, IndRef kn2 -> eq_ind kn1 kn2
    | ConstructRef kn1, ConstructRef kn2 -> eq_constructor kn1 kn2
    | VarRef v1, VarRef v2 -> Id.equal v1 v2
    | (ConstRef _ | IndRef _ | ConstructRef _ | VarRef _), _ -> false

end

type global_reference = GlobRef.t
[@@ocaml.deprecated "Alias for [GlobRef.t]"]

type evaluable_global_reference =
  | EvalVarRef of Id.t
  | EvalConstRef of Constant.t

(* Better to have it here that in closure, since used in grammar.cma *)
let eq_egr e1 e2 = match e1, e2 with
    EvalConstRef con1, EvalConstRef con2 -> Constant.equal con1 con2
  | EvalVarRef id1, EvalVarRef id2 -> Id.equal id1 id2
  | _, _ -> false

(** Located identifiers and objects with syntax. *)

type lident = Id.t CAst.t
type lname = Name.t CAst.t
type lstring = string CAst.t
