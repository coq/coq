(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

  let is_valid_ident_part s = match Unicode.ident_refutation ("x"^s) with
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

  module Set = CString.Set
  module Map = CString.Map
  module Pred = CString.Pred

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
    Stdlib.A.B is ["B";"A";"Stdlib"] *)

let dummy_module_name = "If you see this, it's a bug"

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

  let dummy = [dummy_module_name]

  module Hdir = Hashcons.Hlist(Id)

  let hcons = Hashcons.simple_hcons Hdir.generate Hdir.hcons Id.hcons

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

  let to_string (_i, s, p) =
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

  let print mp = str (to_string mp)

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

  let dummy = MPfile DirPath.dummy

  let rec dp = function
  | MPfile sl -> sl
  | MPbound (_,_,dp) -> dp
  | MPdot (mp,_l) -> dp mp

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

module DPset = Set.Make(DirPath)
module DPmap = Map.Make(DirPath)

module MPset = Set.Make(ModPath)
module MPmap = CMap.Make(ModPath)

(** {6 Kernel names } *)

module KerName = struct

  type t = {
    modpath : ModPath.t;
    knlabel : Label.t;
    refhash : int;
    (** Lazily computed hash. If unset, it is set to negative values. *)
  }

  type kernel_name = t

  let make modpath knlabel =
    let open Hashset.Combine in
    let refhash = combine (ModPath.hash modpath) (Label.hash knlabel) in
    (* Truncate for backwards compatibility w.r.t. ordering *)
    let refhash = refhash land 0x3FFFFFFF in
    { modpath; knlabel; refhash; }

  let repr kn = (kn.modpath, kn.knlabel)

  let modpath kn = kn.modpath
  let label kn = kn.knlabel

  let to_string_gen mp_to_string kn =
    mp_to_string kn.modpath ^ "." ^ Label.to_string kn.knlabel

  let to_string kn = to_string_gen ModPath.to_string kn

  let debug_to_string kn = to_string_gen ModPath.debug_to_string kn

  let print kn = str (to_string kn)

  let debug_print kn = str (debug_to_string kn)

  let compare (kn1 : kernel_name) (kn2 : kernel_name) =
    if kn1 == kn2 then 0
    else
      let c = String.compare kn1.knlabel kn2.knlabel in
      if not (Int.equal c 0) then c
      else
        ModPath.compare kn1.modpath kn2.modpath

  let equal kn1 kn2 =
    let h1 = kn1.refhash in
    let h2 = kn2.refhash in
    if 0 <= h1 && 0 <= h2 && not (Int.equal h1 h2) then false
    else
      Label.equal kn1.knlabel kn2.knlabel &&
      ModPath.equal kn1.modpath kn2.modpath

  let hash kn = kn.refhash

  module Self_Hashcons = struct
    type t = kernel_name
    type u = (ModPath.t -> ModPath.t) * (DirPath.t -> DirPath.t)
        * (string -> string)
    let hashcons (hmod,_hdir,hstr) kn =
      let { modpath = mp; knlabel = l; refhash; } = kn in
      { modpath = hmod mp; knlabel = hstr l; refhash; }
    let eq kn1 kn2 =
      kn1.modpath == kn2.modpath && kn1.knlabel == kn2.knlabel
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

module type EqType =
sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module type QNameS =
sig
  type t
  module CanOrd : EqType with type t = t
  module UserOrd : EqType with type t = t
  module SyntacticOrd : EqType with type t = t
  val canonize : t -> t
end

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

  let canonize kp = match kp with
  | Same _ -> kp
  | Dual (_, kn) -> Same kn

  let same kn = Same kn
  let make knu knc = if KerName.equal knu knc then Same knc else Dual (knu,knc)

  let make1 = same
  let make2 mp l = same (KerName.make mp l)
  let label kp = KerName.label (user kp)
  let modpath kp = KerName.modpath (user kp)

  let change_label kp lbl =
    let (mp1,l1) = KerName.repr (user kp)
    and (mp2,l2) = KerName.repr (canonical kp) in
    assert (String.equal l1 l2);
    if String.equal lbl l1 then kp
    else
      let kn = KerName.make mp1 lbl in
      if mp1 == mp2 then same kn
      else make kn (KerName.make mp2 lbl)

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
    type t = kernel_pair
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

  let hcons = Hashcons.simple_hcons HashKP.generate HashKP.hcons KerName.hcons

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

module Ind =
struct
  (** Designation of a (particular) inductive type. *)
  type t = MutInd.t      (* the name of the inductive type *)
        * int           (* the position of this inductive type
                                    within the block of mutually-recursive inductive types.
                                    BEWARE: indexing starts from 0. *)
  let modpath (mind, _) = MutInd.modpath mind

  module CanOrd =
  struct
    type nonrec t = t
    let equal (m1, i1) (m2, i2) = Int.equal i1 i2 && MutInd.CanOrd.equal m1 m2
    let compare (m1, i1) (m2, i2) =
      let c = Int.compare i1 i2 in
      if Int.equal c 0 then MutInd.CanOrd.compare m1 m2 else c
    let hash (m, i) =
      Hashset.Combine.combine (MutInd.CanOrd.hash m) (Int.hash i)
  end

  module UserOrd =
  struct
    type nonrec t = t
    let equal (m1, i1) (m2, i2) =
      Int.equal i1 i2 && MutInd.UserOrd.equal m1 m2
    let compare (m1, i1) (m2, i2) =
      let c = Int.compare i1 i2 in
      if Int.equal c 0 then MutInd.UserOrd.compare m1 m2 else c
    let hash (m, i) =
      Hashset.Combine.combine (MutInd.UserOrd.hash m) (Int.hash i)
  end

  module SyntacticOrd =
  struct
    type nonrec t = t
    let equal (m1, i1) (m2, i2) =
      Int.equal i1 i2 && MutInd.SyntacticOrd.equal m1 m2

    let compare (m1, i1) (m2, i2) =
      let c = Int.compare i1 i2 in
      if Int.equal c 0 then MutInd.SyntacticOrd.compare m1 m2 else c

    let hash (m, i) =
      Hashset.Combine.combine (MutInd.SyntacticOrd.hash m) (Int.hash i)
  end

  let canonize ((mind, i) as ind) =
    let mind' = MutInd.canonize mind in
    if mind' == mind then ind else (mind', i)

end

module Construct =
struct
  (** Designation of a (particular) constructor of a (particular) inductive type. *)
  type t = Ind.t (* designates the inductive type *)
         * int   (* the index of the constructor
                                    BEWARE: indexing starts from 1. *)

  let modpath (ind, _) = Ind.modpath ind

  module CanOrd =
  struct
    type nonrec t = t
    let equal (ind1, j1) (ind2, j2) = Int.equal j1 j2 && Ind.CanOrd.equal ind1 ind2
    let compare (ind1, j1) (ind2, j2) =
      let c = Int.compare j1 j2 in
      if Int.equal c 0 then Ind.CanOrd.compare ind1 ind2 else c
    let hash (ind, i) =
      Hashset.Combine.combine (Ind.CanOrd.hash ind) (Int.hash i)
  end

  module UserOrd =
  struct
    type nonrec t = t
    let equal (ind1, j1) (ind2, j2) =
      Int.equal j1 j2 && Ind.UserOrd.equal ind1 ind2
    let compare (ind1, j1) (ind2, j2) =
      let c = Int.compare j1 j2 in
      if Int.equal c 0 then Ind.UserOrd.compare ind1 ind2 else c
    let hash (ind, i) =
      Hashset.Combine.combine (Ind.UserOrd.hash ind) (Int.hash i)
  end

  module SyntacticOrd =
  struct
    type nonrec t = t
    let equal (ind1, j1) (ind2, j2) =
      Int.equal j1 j2 && Ind.SyntacticOrd.equal ind1 ind2
    let compare (ind1, j1) (ind2, j2) =
      let c = Int.compare j1 j2 in
      if Int.equal c 0 then Ind.SyntacticOrd.compare ind1 ind2 else c
    let hash (ind, i) =
      Hashset.Combine.combine (Ind.SyntacticOrd.hash ind) (Int.hash i)
  end

  let canonize ((ind, i) as cstr) =
    let ind' = Ind.canonize ind in
    if ind' == ind then cstr else (ind', i)

end

(** Designation of a (particular) inductive type. *)
type inductive = Ind.t

(** Designation of a (particular) constructor of a (particular) inductive type. *)
type constructor = Construct.t

let ith_mutual_inductive (mind, _) i = (mind, i)
let ith_constructor_of_inductive ind i = (ind, i)
let inductive_of_constructor (ind, _i) = ind
let index_of_constructor (_ind, i) = i

module Indset = Set.Make(Ind.CanOrd)
module Indset_env = Set.Make(Ind.UserOrd)
module Indmap = Map.Make(Ind.CanOrd)
module Indmap_env = Map.Make(Ind.UserOrd)

module Constrset = Set.Make(Construct.CanOrd)
module Constrset_env = Set.Make(Construct.UserOrd)
module Constrmap = Map.Make(Construct.CanOrd)
module Constrmap_env = Map.Make(Construct.UserOrd)

(** {6 Hash-consing of name objects } *)

module Hind = Hashcons.Make(
  struct
    type t = inductive
    type u = MutInd.t -> MutInd.t
    let hashcons hmind (mind, i) = (hmind mind, i)
    let eq (mind1,i1) (mind2,i2) = mind1 == mind2 && Int.equal i1 i2
    let hash = Ind.CanOrd.hash
  end)

module Hconstruct = Hashcons.Make(
  struct
    type t = constructor
    type u = inductive -> inductive
    let hashcons hind (ind, j) = (hind ind, j)
    let eq (ind1, j1) (ind2, j2) = ind1 == ind2 && Int.equal j1 j2
    let hash = Construct.CanOrd.hash
  end)

let hcons_con = Constant.hcons
let hcons_mind = MutInd.hcons
let hcons_ind = Hashcons.simple_hcons Hind.generate Hind.hcons hcons_mind
let hcons_construct = Hashcons.simple_hcons Hconstruct.generate Hconstruct.hcons hcons_ind

(*****************)

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

let hash_table_key f ik =
  let open Hashset.Combine in
  match ik with
  | ConstKey c -> combinesmall 1 (f c)
  | VarKey id -> combinesmall 2 (Id.hash id)
  | RelKey i -> combinesmall 3 (Int.hash i)

let eq_mind_chk = MutInd.UserOrd.equal
let eq_ind_chk (kn1,i1) (kn2,i2) = Int.equal i1 i2 && eq_mind_chk kn1 kn2

(*******************************************************************)
(** Compatibility layers *)

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
        proj_name : Constant.t;
        (** The only relevant data is the label, the rest is canonically derived
            from proj_ind. *)
      }

    let make proj_ind ~proj_npars ~proj_arg proj_name =
      let proj_name = KerPair.change_label (fst proj_ind) proj_name in
      {proj_ind;proj_npars;proj_arg;proj_name}

    let inductive c = c.proj_ind

    let mind c = fst c.proj_ind

    let constant c = c.proj_name

    let label c = Constant.label c.proj_name

    let npars c = c.proj_npars

    let arg c = c.proj_arg

    let hash p =
      Hashset.Combine.combinesmall p.proj_arg (Ind.CanOrd.hash p.proj_ind)

    let compare_gen a b =
      let c = Int.compare a.proj_arg b.proj_arg in
      if c <> 0 then c
      else
        let c = Int.compare a.proj_npars b.proj_npars in
        if c <> 0 then c
        else
          Label.compare (Constant.label a.proj_name) (Constant.label b.proj_name)

    module SyntacticOrd = struct
      type nonrec t = t

      let compare a b =
        let c = Ind.SyntacticOrd.compare a.proj_ind b.proj_ind in
        if c <> 0 then c
        else compare_gen a b

      let equal a b = compare a b == 0

      let hash p =
        Hashset.Combine.combinesmall p.proj_arg (Ind.CanOrd.hash p.proj_ind)
    end
    module CanOrd = struct
      type nonrec t = t

      let compare a b =
        let c = Ind.CanOrd.compare a.proj_ind b.proj_ind in
        if c <> 0 then c
        else compare_gen a b

      let equal a b = compare a b == 0

      let hash p =
        Hashset.Combine.combinesmall p.proj_arg (Ind.CanOrd.hash p.proj_ind)
    end
    module UserOrd = struct
      type nonrec t = t

      let compare a b =
        let c = Ind.UserOrd.compare a.proj_ind b.proj_ind in
        if c <> 0 then c
        else compare_gen a b

      let equal a b = compare a b == 0

      let hash p =
        Hashset.Combine.combinesmall p.proj_arg (Ind.UserOrd.hash p.proj_ind)
    end

    let equal = CanOrd.equal
    let compare = CanOrd.compare

    let canonize p =
      let { proj_ind; proj_npars; proj_arg; proj_name } = p in
      let proj_ind' = Ind.canonize proj_ind in
      let proj_name' = Constant.canonize proj_name in
      if proj_ind' == proj_ind && proj_name' == proj_name then p
      else { proj_ind = proj_ind'; proj_name = proj_name'; proj_npars; proj_arg }

    module Self_Hashcons = struct
      type nonrec t = t
      type u = (inductive -> inductive) * (Constant.t -> Constant.t)
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
    let hcons = Hashcons.simple_hcons HashRepr.generate HashRepr.hcons (hcons_ind,Constant.hcons)

    let map_npars f p =
      let npars = p.proj_npars in
      let npars' = f npars in
      if npars == npars' then p
      else {p with proj_npars = npars'}

    let map f p =
      let ind = fst p.proj_ind in
      let ind' = f ind in
      if ind == ind' then p
      else
        let proj_name = KerPair.change_label ind' (label p) in
        {p with proj_ind = (ind',snd p.proj_ind); proj_name}

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

  let repr_equal p p' = Repr.equal (repr p) (repr p')

  let hash (c, b) = (if b then 0 else 1) + Repr.hash c

  module SyntacticOrd = struct
    type nonrec t = t
    let compare (p, b) (p', b') =
      let c = Bool.compare b b' in
      if c <> 0 then c else Repr.SyntacticOrd.compare p p'
    let equal (c, b as x) (c', b' as x') =
      x == x' || b = b' && Repr.SyntacticOrd.equal c c'
    let hash (c, b) = (if b then 0 else 1) + Repr.SyntacticOrd.hash c
  end
  module CanOrd = struct
    type nonrec t = t
    let compare (p, b) (p', b') =
      let c = Bool.compare b b' in
      if c <> 0 then c else Repr.CanOrd.compare p p'
    let equal (c, b as x) (c', b' as x') =
      x == x' || b = b' && Repr.CanOrd.equal c c'
    let hash (c, b) = (if b then 0 else 1) + Repr.CanOrd.hash c
  end
  module UserOrd = struct
    type nonrec t = t
    let compare (p, b) (p', b') =
      let c = Bool.compare b b' in
      if c <> 0 then c else Repr.UserOrd.compare p p'
    let equal (c, b as x) (c', b' as x') =
      x == x' || b = b' && Repr.UserOrd.equal c c'
    let hash (c, b) = (if b then 0 else 1) + Repr.UserOrd.hash c
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

  let canonize ((r, u) as p) =
    let r' = Repr.canonize r in
    if r' == r then p else (r',  u)

  module HashProjection = Hashcons.Make(Self_Hashcons)

  let hcons = Hashcons.simple_hcons HashProjection.generate HashProjection.hcons Repr.hcons

  let compare (p, b) (p', b') =
    let c = Bool.compare b b' in
    if c <> 0 then c else Repr.compare p p'

  let map f (c, b as x) =
    let c' = Repr.map f c in
    if c' == c then x else (c', b)

  let map_npars f (c, b as x) =
    let c' = Repr.map_npars f c in
    if c' == c then x else (c', b)

  let to_string p = Constant.to_string (constant p)
  let print p = Constant.print (constant p)

  let debug_to_string p =
    (if unfolded p then "unfolded(" else "") ^
    Constant.debug_to_string (constant p) ^
    (if unfolded p then ")" else "")
  let debug_print p = str (debug_to_string p)

end

module PRmap = HMap.Make(Projection.Repr.CanOrd)
module PRset = PRmap.Set
module PRpred = Predicate.Make(Projection.Repr.CanOrd)

module GlobRefInternal = struct

  type t =
    | VarRef of variable           (** A reference to the section-context. *)
    | ConstRef of Constant.t       (** A reference to the environment. *)
    | IndRef of inductive          (** A reference to an inductive type. *)
    | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)

  let equal gr1 gr2 =
    gr1 == gr2 || match gr1,gr2 with
    | ConstRef con1, ConstRef con2 -> Constant.equal con1 con2
    | IndRef kn1, IndRef kn2 -> Ind.CanOrd.equal kn1 kn2
    | ConstructRef kn1, ConstructRef kn2 -> Construct.CanOrd.equal kn1 kn2
    | VarRef v1, VarRef v2 -> Id.equal v1 v2
    | (ConstRef _ | IndRef _ | ConstructRef _ | VarRef _), _ -> false

  let global_eq_gen eq_cst eq_ind eq_cons x y =
    x == y ||
    match x, y with
    | ConstRef cx, ConstRef cy -> eq_cst cx cy
    | IndRef indx, IndRef indy -> eq_ind indx indy
    | ConstructRef consx, ConstructRef consy -> eq_cons consx consy
    | VarRef v1, VarRef v2 -> Id.equal v1 v2
    | (VarRef _ | ConstRef _ | IndRef _ | ConstructRef _), _ -> false

  let global_ord_gen ord_cst ord_ind ord_cons x y =
    if x == y then 0
    else match x, y with
    | VarRef v1, VarRef v2 -> Id.compare v1 v2
    | VarRef _, _ -> -1
    | _, VarRef _ -> 1
    | ConstRef cx, ConstRef cy -> ord_cst cx cy
    | ConstRef _, _ -> -1
    | _, ConstRef _ -> 1
    | IndRef indx, IndRef indy -> ord_ind indx indy
    | IndRef _, _ -> -1
    | _ , IndRef _ -> 1
    | ConstructRef consx, ConstructRef consy -> ord_cons consx consy

  let global_hash_gen hash_cst hash_ind hash_cons gr =
    let open Hashset.Combine in
    match gr with
    | ConstRef c -> combinesmall 1 (hash_cst c)
    | IndRef i -> combinesmall 2 (hash_ind i)
    | ConstructRef c -> combinesmall 3 (hash_cons c)
    | VarRef id -> combinesmall 4 (Id.hash id)

end

module GlobRef = struct

  type t = GlobRefInternal.t =
    | VarRef of variable           (** A reference to the section-context. *)
    | ConstRef of Constant.t       (** A reference to the environment. *)
    | IndRef of inductive          (** A reference to an inductive type. *)
    | ConstructRef of constructor  (** A reference to a constructor of an inductive type. *)

  let equal = GlobRefInternal.equal

  (* By default, [global_reference] are ordered on their canonical part *)

  module CanOrd = struct
    type t = GlobRefInternal.t
    let compare gr1 gr2 =
      GlobRefInternal.global_ord_gen Constant.CanOrd.compare Ind.CanOrd.compare Construct.CanOrd.compare gr1 gr2
    let equal gr1 gr2 = GlobRefInternal.global_eq_gen Constant.CanOrd.equal Ind.CanOrd.equal Construct.CanOrd.equal gr1 gr2
    let hash gr = GlobRefInternal.global_hash_gen Constant.CanOrd.hash Ind.CanOrd.hash Construct.CanOrd.hash gr
  end

  module UserOrd = struct
    type t = GlobRefInternal.t
    let compare gr1 gr2 =
      GlobRefInternal.global_ord_gen Constant.UserOrd.compare Ind.UserOrd.compare Construct.UserOrd.compare gr1 gr2
    let equal gr1 gr2 = GlobRefInternal.global_eq_gen Constant.UserOrd.equal Ind.UserOrd.equal Construct.UserOrd.equal gr1 gr2
    let hash gr = GlobRefInternal.global_hash_gen Constant.UserOrd.hash Ind.UserOrd.hash Construct.UserOrd.hash gr
  end

  module SyntacticOrd = struct
    type t = GlobRefInternal.t
    let compare gr1 gr2 =
      GlobRefInternal.global_ord_gen Constant.SyntacticOrd.compare Ind.SyntacticOrd.compare Construct.SyntacticOrd.compare gr1 gr2
    let equal gr1 gr2 = GlobRefInternal.global_eq_gen Constant.SyntacticOrd.equal Ind.SyntacticOrd.equal Construct.SyntacticOrd.equal gr1 gr2
    let hash gr = GlobRefInternal.global_hash_gen Constant.SyntacticOrd.hash Ind.SyntacticOrd.hash Construct.SyntacticOrd.hash gr
  end

  let canonize gr = match gr with
  | VarRef _ -> gr
  | ConstRef c ->
    let c' = Constant.canonize c in
    if c' == c then gr else ConstRef c'
  | IndRef ind ->
    let ind' = Ind.canonize ind in
    if ind' == ind then gr else IndRef ind'
  | ConstructRef c ->
    let c' = Construct.canonize c in
    if c' == c then gr else ConstructRef c'

  let is_bound = function
  | VarRef _ -> false
  | ConstRef cst -> ModPath.is_bound (Constant.modpath cst)
  | IndRef (ind,_) | ConstructRef ((ind,_),_) -> ModPath.is_bound (MutInd.modpath ind)

  module Map = HMap.Make(CanOrd)
  module Set = Map.Set

  (* Alternative sets and maps indexed by the user part of the kernel names *)

  module Map_env = HMap.Make(UserOrd)
  module Set_env = Map_env.Set

  let print = function
    | VarRef x -> Id.print x
    | ConstRef x -> Constant.print x
    | IndRef (m,i) -> surround (MutInd.print m ++ strbrk ", " ++ int i )
    | ConstructRef ((m,i),j) -> surround (MutInd.print m ++ strbrk ", " ++ int i ++ strbrk ", " ++ int j)

end

(** Located identifiers and objects with syntax. *)

type lident = Id.t CAst.t
type lname = Name.t CAst.t
type lstring = string CAst.t

let lident_eq = CAst.eq Id.equal
