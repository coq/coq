(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames
open Globnames

(* to this type are mapped DirPath.t's in the nametab *)
module GlobDirRef = struct
  type t =
    | DirOpenModule of ModPath.t
    | DirOpenModtype of ModPath.t
    | DirOpenSection of full_path

  let equal r1 r2 = match r1, r2 with
    | DirOpenModule op1, DirOpenModule op2 -> ModPath.equal op1 op2
    | DirOpenModtype op1, DirOpenModtype op2 -> ModPath.equal op1 op2
    | DirOpenSection op1, DirOpenSection op2 -> eq_full_path op1 op2
    | (DirOpenModule _ | DirOpenModtype _ | DirOpenSection _), _ -> false

  let compare r1 r2 = match r1, r2 with
    | DirOpenModule op1, DirOpenModule op2 -> ModPath.compare op1 op2
    | DirOpenModule _, _ -> -1
    | _, DirOpenModule _ -> 1
    | DirOpenModtype op1, DirOpenModtype op2 -> ModPath.compare op1 op2
    | DirOpenModtype _, _ -> -1
    | _, DirOpenModtype _ -> 1
    | DirOpenSection op1, DirOpenSection op2 -> compare_full_path op1 op2

end

exception GlobalizationError of qualid

let error_global_not_found ~info qid =
  let info = Option.cata (Loc.add_loc info) info qid.CAst.loc in
  Exninfo.iraise (GlobalizationError qid, info)

(* The visibility can be registered either
   - for all suffixes not shorter then a given int - when the object
     is loaded inside a module
   or
   - for a precise suffix, when the module containing (the module
     containing ...) the object is open (imported)
*)
type visibility = Until of int | Exactly of int

let map_visibility f = function
  | Until i -> Until (f i)
  | Exactly i -> Exactly (f i)

(* Data structure for nametabs *******************************************)

module type EqualityType =
sig
  type t
  val equal : t -> t -> bool
end

(* A ['a t] is a map from [user_name] to ['a], with possible lookup by
   partially qualified names of type [qualid]. The mapping of
   partially qualified names to ['a] is determined by the [visibility]
   parameter of [push].

   The [shortest_qualid] function given a user_name Mylib.A.B.x, tries
   to find the shortest among x, B.x, A.B.x and Mylib.A.B.x that denotes
   the same object.
*)
module type NAMETREE = sig
  type elt
  type t

  val empty : t
  val push : visibility -> full_path -> elt -> t -> t
  val locate : qualid -> t -> elt
  val find : full_path -> t -> elt
  val remove : full_path -> t -> t
  val exists : full_path -> t -> bool
  val full_path : qualid -> t -> full_path
  val shortest_qualid_gen : ?loc:Loc.t -> (Id.t -> bool) -> full_path -> t -> qualid
  val shortest_qualid : ?loc:Loc.t -> Id.Set.t -> full_path -> t -> qualid
  val find_prefixes : qualid -> t -> elt list

  (** Matches a prefix of [qualid], useful for completion *)
  val match_prefixes : qualid -> t -> elt list
end

let masking_absolute = CWarnings.create_warning
    ~from:[Deprecation.Version.v8_8] ~name:"masking-absolute-name" ()

let coq_id = Id.of_string "Coq"
let stdlib_id = Id.of_string "Stdlib"
let init_id = Id.of_string "Corelib"

let warn_deprecated_dirpath_Coq =
  CWarnings.create_with_quickfix ~name:"deprecated-dirpath-Coq"
    ~category:Deprecation.Version.v9_0
    (fun (old_id, new_id) ->
      Pp.(old_id ++ spc () ++ str "has been replaced by" ++ spc () ++ new_id ++ str "."))

(* We shadow as to create the quickfix and message at the same time *)
let fix_coq_id coq_repl l =
  (match l with
   | _coq_id :: l -> coq_repl :: l
   | _ -> l)

(* [l] is reversed, thus [Corelib.ssr.bool] for example *)
let warn_deprecated_dirpath_Coq ?loc (coq_repl, l, id) =
  let dp l = DirPath.make (List.rev l) in
  let old_id = pr_qualid @@ Libnames.make_qualid (DirPath.make l) id in
  let new_id = pr_qualid @@ Libnames.make_qualid (dp @@ fix_coq_id coq_repl (List.rev l)) id in
  let quickfix = Option.map (fun loc -> [ Quickfix.make ~loc new_id ]) loc in
  warn_deprecated_dirpath_Coq ?loc ?quickfix (old_id, new_id)

module Make (E : EqualityType) : NAMETREE
  with type elt = E.t =
struct
  type elt = E.t

  (* A name became inaccessible, even with absolute qualification.
     Example:
     Module F (X : S). Module X.
     The argument X of the functor F is masked by the inner module X.
   *)
  let warn_masking_absolute =
    CWarnings.create_in masking_absolute
      Pp.(fun n -> str "Trying to mask the absolute name \"" ++ pr_path n  ++ str "\"!")

  type path_status =
    | Relative of full_path * elt
    | Absolute of full_path * elt

  let eq_path_status p q = match p, q with
  | Relative (u1, o1), Relative (u2, o2) -> eq_full_path u1 u2 && E.equal o1 o2
  | Absolute (u1, o1), Absolute (u2, o2) -> eq_full_path u1 u2 && E.equal o1 o2
  | (Absolute _ | Relative _), _ -> false

  (* Dictionaries of short names *)
  type nametree =
      { path : path_status list;
        map : nametree Id.Map.t }

  let push_path arg path = match path with
  | [] -> [arg]
  | arg' :: _ -> if eq_path_status arg arg' then path else arg :: path

  let mktree p m = { path=p; map=m }
  let empty_tree = mktree [] Id.Map.empty
  let is_empty_tree tree = tree.path = [] && Id.Map.is_empty tree.map

  type t = nametree Id.Map.t

  let empty = Id.Map.empty

  (* [push_until] is used to register [Until vis] visibility.

     Example: [push_until Top.X.Y.t o (Until 1) tree [Y;X;Top]] adds the
     value [Relative (Top.X.Y.t,o)] to occurrences [Y] and [Y.X] of
     the tree, and [Absolute (Top.X.Y.t,o)] to occurrence [Y.X.Top] of
     the tree. In particular, the tree now includes the following shape:
     { map := Y |-> {map := X |-> {map := Top |-> {map := ...;
                                                   path := Absolute (Top.X.Y.t,o)::...}
                                          ...;
                                   path := Relative (Top.X.Y.t,o)::...}
                             ...;
                     path := Relative (Top.X.Y.t,o)::...}
               ...;
       path := ...}
     where ... denotes what was there before.

     [push_exactly] is to register [Exactly vis] and [push] chooses
     the right one *)

  let rec push_until uname o level tree = function
    | modid :: path ->
        let modify _ mc = push_until uname o (level-1) mc path in
        let map =
          try Id.Map.modify modid modify tree.map
          with Not_found ->
            let ptab = modify () empty_tree in
            Id.Map.add modid ptab tree.map
        in
        let this =
          if level <= 0 then
            match tree.path with
              | Absolute (n,_)::_ ->
                  (* This is an absolute name, we must keep it
                     otherwise it may become unaccessible forever *)
                warn_masking_absolute n; tree.path
              | current -> push_path (Relative (uname, o)) current
          else tree.path
        in
        if this == tree.path && map == tree.map then tree
        else mktree this map
    | [] ->
        match tree.path with
          | Absolute (uname',o') :: _ ->
              if E.equal o' o then begin
                assert (eq_full_path uname uname');
                tree
                  (* we are putting the same thing for the second time :) *)
              end
              else
                (* This is an absolute name, we must keep it otherwise it may
                   become unaccessible forever *)
                (* But ours is also absolute! This is an error! *)
                CErrors.user_err
                  Pp.(str "Cannot mask the absolute name \"" ++ pr_path uname' ++ str "\"!")
          | current ->
            let this = push_path (Absolute (uname, o)) current in
            if this == tree.path then tree
            else mktree this tree.map

let rec push_exactly uname o level tree = function
| [] ->
  CErrors.anomaly (Pp.str "Prefix longer than path! Impossible!")
| modid :: path ->
  if Int.equal level 0 then
    let this =
      match tree.path with
        | Absolute (n,_) :: _ ->
            (* This is an absolute name, we must keep it
                otherwise it may become unaccessible forever *)
            warn_masking_absolute n; tree.path
        | current -> push_path (Relative (uname, o)) current
    in
    if this == tree.path then tree
    else mktree this tree.map
  else (* not right level *)
    let modify _ mc = push_exactly uname o (level-1) mc path in
    let map =
      try Id.Map.modify modid modify tree.map
      with Not_found ->
        let ptab = modify () empty_tree in
        Id.Map.add modid ptab tree.map
    in
    if map == tree.map then tree
    else mktree tree.path map

let push visibility uname o tab =
  let dir,id = repr_path uname in
  let dir = DirPath.repr dir in
  let modify _ ptab = match visibility with
    | Until i -> push_until uname o (i-1) ptab dir
    | Exactly i -> push_exactly uname o (i-1) ptab dir
  in
  try Id.Map.modify id modify tab
  with Not_found ->
    let ptab = modify () empty_tree in
    Id.Map.add id ptab tab

(** [remove_path uname tree dir] removes all bindings pointing to
    [uname] along the path [dir] in [tree] (i.e. all such bindings are
    assumed to be on this path) *)

let rec remove_path uname tree = function
  | modid :: path ->
      let update = function
        | None -> (* The name was actually not here *) None
        | Some mc ->
          let mc = remove_path uname mc path in
          if is_empty_tree mc then None else Some mc
      in
      let map = Id.Map.update modid update tree.map in
      let this =
        let test = function Relative (uname',_) -> not (eq_full_path uname uname') | _ -> true in
        List.filter test tree.path
      in
      mktree this map
  | [] ->
      let this =
        let test = function Absolute (uname',_) -> not (eq_full_path uname uname') | _ -> true in
        List.filter test tree.path
      in
      mktree this tree.map

(** Remove all bindings pointing to [uname] in [tab] *)

let remove uname tab =
  let dir,id = repr_path uname in
  let dir = DirPath.repr dir in
  let modify _ ptab = remove_path uname ptab dir in
  try Id.Map.modify id modify tab
  with Not_found -> tab

let rec search coq_repl tree = function
  | [modid] when Id.equal modid coq_id ->
     let _warn, p =
       match Id.Map.find_opt coq_repl tree.map with
       | None -> None, None
       | Some modid -> search coq_repl modid [] in
     Some coq_repl, p
  | modid :: path ->
     begin match Id.Map.find_opt modid tree.map with
     | None -> None, None
     | Some modid -> search coq_repl modid path end
  | [] -> None, Some tree.path

let search ?loc id tree dir =
  let warn, p = search stdlib_id tree dir in
  let warn, p =
    match p with Some _ -> warn, p | None -> search init_id tree dir in
  begin match warn with None -> () | Some coq_repl ->
    warn_deprecated_dirpath_Coq ?loc (coq_repl, dir, id) end;
  match p with Some p -> p | None -> raise Not_found

let find_node qid tab =
  let loc = qid.CAst.loc in
  let (dir,id) = repr_qualid qid in
  search ?loc id (Id.Map.find id tab) (DirPath.repr dir)

let locate qid tab =
  let o = match find_node qid tab with
    | (Absolute (uname,o) | Relative (uname,o)) :: _ -> o
    | [] -> raise Not_found
  in
    o

let full_path qid tab =
  let uname = match find_node qid tab with
    | (Absolute (uname,o) | Relative (uname,o)) :: _ -> uname
    | [] -> raise Not_found
  in
    uname

let find uname tab =
  let l,id = repr_path uname in
  let l = DirPath.repr l in
  match search id (Id.Map.find id tab) l with
  | Absolute (_,o) :: _ -> o
  | _ -> raise Not_found

let exists uname tab =
  try
    let _ = find uname tab in
      true
  with
      Not_found -> false

let shortest_qualid_gen ?loc hidden uname tab =
  let dir,id = repr_path uname in
  let dir = DirPath.repr dir in
  let hidden = hidden id in
  let rec find_uname pos dir tree =
    let is_empty = match pos with [] -> true | _ -> false in
    match tree.path with
    | (Absolute (u,_) | Relative (u,_)) :: _
          when eq_full_path u uname && not (is_empty && hidden) -> List.rev pos
    | _ ->
        match dir with
            [] -> raise Not_found
          | id::dir -> find_uname (id::pos) dir (Id.Map.find id tree.map)
  in
  let ptab = Id.Map.find id tab in
  let found_dir = find_uname [] dir ptab in
    make_qualid ?loc (DirPath.make found_dir) id

let shortest_qualid ?loc ctx uname tab =
  shortest_qualid_gen ?loc (fun id -> Id.Set.mem id ctx) uname tab

let push_node node l =
  match node with
  | (Absolute (_,o) | Relative (_,o)) :: _
    when not (Util.List.mem_f E.equal o l) -> o::l
  | _ -> l

let rec flatten_tree tree l =
  let f _ tree l = flatten_tree tree l in
  Id.Map.fold f tree.map (push_node tree.path l)

let rec search_prefixes tree = function
  | modid :: path -> search_prefixes (Id.Map.find modid tree.map) path
  | [] -> List.rev (flatten_tree tree [])

let find_prefixes qid tab =
  try
    let (dir,id) = repr_qualid qid in
    search_prefixes (Id.Map.find id tab) (DirPath.repr dir)
  with Not_found -> []

let match_prefixes =
  let cprefix x y = CString.(compare x (sub y 0 (min (length x) (length y)))) in
  fun qid tab ->
    try
      let (dir,id) = repr_qualid qid in
      let id_prefix = cprefix Id.(to_string id) in
      let matches = Id.Map.filter_range (fun x -> id_prefix Id.(to_string x)) tab in
      let matches = Id.Map.mapi (fun _key tab -> search_prefixes tab (DirPath.repr dir)) matches in
      (* Rocq's flatten is "magical", so this is not so bad perf-wise *)
      CList.flatten @@ Id.Map.(fold (fun _ r l -> r :: l) matches [])
    with Not_found -> []

end

module type NAMETAB = sig
  type 'a read_tab
  type write_tab

  type elt

  val push : ?user_warns:elt UserWarn.with_qf -> visibility -> full_path -> elt -> write_tab

  val remove : full_path -> elt -> write_tab

  val shortest_qualid_gen : ?loc:Loc.t -> (Id.t -> bool) -> elt -> qualid read_tab

  val shortest_qualid : ?loc:Loc.t -> Id.Set.t -> elt -> qualid read_tab

  val is_warned : elt -> elt UserWarn.with_qf option read_tab

  val warn : ?loc:Loc.t -> elt UserWarn.with_qf -> elt -> unit read_tab

  val locate : ?nowarn:bool -> qualid -> elt read_tab

  (* NB doesn't warn *)
  val locate_all : qualid -> elt list read_tab

  val completion_candidates : qualid -> elt list read_tab

  val to_path : elt -> full_path read_tab

  val of_path : full_path -> elt read_tab

  val exists : full_path -> bool read_tab

  (* XXX add src_loc table? *)
end

module type ValueType = sig
  include EqualityType

  val is_var : t -> Id.t option

  module Map : CSig.UMapS with type key = t
end

module type WarnInfo = sig
  type elt

  val create_warnings : (elt -> 'tab -> Pp.t) -> unit ->
    (?loc:Loc.t -> elt UserWarn.with_qf -> elt -> 'tab -> unit)
end

module type SimpleWarnS = sig
  type t

  val object_name : string
  val warning_name_base : string
end

module NoWarn (X:sig type t end) : WarnInfo with type elt = X.t = struct
  type elt = X.t

  let create_warnings _ () =
    fun ?loc _ _ _ -> assert false
end

module SimpleWarn (X:SimpleWarnS) : WarnInfo with type elt = X.t = struct
  type elt = X.t

  let create_warnings pp () =
    let open X in
    let pp (v,tabs) = pp v tabs in
    let warn = UserWarn.create_depr_and_user_warnings_qf ~object_name ~warning_name_base
        ~pp_qf:pp pp ()
    in
    fun ?loc w v tabs ->
      warn ?loc (v,tabs) (UserWarn.map_qf (fun q -> q, tabs) w)

end

module type Functional_NAMETAB = sig
  type t
  val empty : t
  include NAMETAB with type 'a read_tab := t -> 'a and type write_tab := t -> t
end

module MakeTab (E:ValueType) (W:WarnInfo with type elt = E.t)
    () (* effectful: calls create_warnings *)
  : Functional_NAMETAB with type elt = E.t
= struct
  type elt = E.t

  module Tab = Make(E)

  type t = {
    tab : Tab.t;
    revtab : full_path E.Map.t;
    warntab : elt UserWarn.with_qf E.Map.t;
  }

  let empty = {
    tab = Tab.empty;
    revtab = E.Map.empty;
    warntab = E.Map.empty;
  }

  let push ?user_warns vis sp v { tab; revtab; warntab } =
    match vis with
    | Until _ ->
      let user_warns = match user_warns with
      | None -> None
      | Some w -> if UserWarn.is_empty_qf w then None else user_warns
      in
      {
        tab = Tab.push vis sp v tab;
        revtab = E.Map.add v sp revtab;
        warntab = Option.fold_left (fun warntab warn -> E.Map.add v warn warntab) warntab user_warns;
      }
    | Exactly _ ->
      begin
        assert (Option.is_empty user_warns);
        { tab = Tab.push vis sp v tab;
          revtab; warntab }
      end

  let remove sp v { tab; revtab; warntab } =
    { tab = Tab.remove sp tab;
      revtab = E.Map.remove v revtab;
      warntab = E.Map.remove v warntab; }

  let shortest_qualid_gen ?loc avoid v { tab; revtab } =
    match E.is_var v with
    | Some id -> make_qualid ?loc DirPath.empty id
    | None ->
      let sp = E.Map.find v revtab in
      Tab.shortest_qualid_gen ?loc avoid sp tab

  let shortest_qualid ?loc avoid v tabs =
    shortest_qualid_gen ?loc (fun id -> Id.Set.mem id avoid) v tabs

  let is_warned v { warntab } = E.Map.find_opt v warntab

  let pr v tab = pr_qualid (shortest_qualid Id.Set.empty v tab)

  let warn = W.create_warnings pr ()

  let locate ?(nowarn=false) qid ({ tab } as tabs) =
    let v = Tab.locate qid tab in
    let () = if nowarn then ()
      else
        let w = is_warned v tabs in
        w |> Option.iter (fun w -> warn ?loc:qid.loc w v tabs)
    in
    v

  let locate_all qid { tab } = Tab.find_prefixes qid tab

  let completion_candidates qid { tab } = Tab.match_prefixes qid tab

  let to_path v { revtab } = match E.is_var v with
    | Some id -> make_path DirPath.empty id
    | None -> E.Map.find v revtab

  let of_path sp { tab } = Tab.find sp tab

  let exists sp { tab } = Tab.exists sp tab

end

module type Imperative_NAMETAB = NAMETAB with type 'a read_tab := 'a and type write_tab := unit

module type StateInfo = sig
  val stage : Summary.Stage.t
  val summary_name : string
end

module MakeImperative (Tab:Functional_NAMETAB) (SI:StateInfo) ()
    : Imperative_NAMETAB with type elt = Tab.elt
= struct
  type elt = Tab.elt

  let the_tab = Summary.ref ~stage:SI.stage ~name:SI.summary_name Tab.empty

  let push ?user_warns vis sp v = the_tab := Tab.push ?user_warns vis sp v !the_tab

  let remove sp v = the_tab := Tab.remove sp v !the_tab

  let shortest_qualid_gen ?loc f v = Tab.shortest_qualid_gen ?loc f v !the_tab

  let shortest_qualid ?loc avoid v = Tab.shortest_qualid ?loc avoid v !the_tab

  let is_warned v = Tab.is_warned v !the_tab

  let warn ?loc qf v = Tab.warn ?loc qf v !the_tab

  let locate ?nowarn qid = Tab.locate ?nowarn qid !the_tab

  let locate_all qid = Tab.locate_all qid !the_tab

  let completion_candidates qid = Tab.completion_candidates qid !the_tab

  let to_path v = Tab.to_path v !the_tab

  let of_path v = Tab.of_path v !the_tab

  let exists v = Tab.exists v !the_tab
end

module EasyNoWarn (M:sig include ValueType include StateInfo end) () =
  MakeImperative(MakeTab(M)(NoWarn(M))())(M)()

module Easy (M:sig include ValueType include StateInfo include SimpleWarnS with type t := t end) () =
  MakeImperative(MakeTab(M)(SimpleWarn(M))())(M)()

(* Global name tables *************************************************)

module XRefWarn : WarnInfo with type elt = extended_global_reference = struct
  type elt = extended_global_reference

  let create_warnings pp () =
    let pp (v,tab) = pp v tab in
    let depr_ref = Deprecation.create_warning_with_qf ~object_name:"Reference" ~warning_name_if_no_since:"deprecated-reference" ~pp_qf:pp pp in
    let depr_abbrev = Deprecation.create_warning_with_qf ~object_name:"Notation" ~warning_name_if_no_since:"deprecated-syntactic-definition" ~pp_qf:pp pp in
    let user_warn = UserWarn.create_warning ~warning_name_if_no_cats:"warn-reference" () in

    let depr_xref ?loc depr xref tabs =
      let depr = Deprecation.map_qf (fun qf -> qf,tabs) depr in
      match xref with
      | TrueGlobal _ -> depr_ref ?loc ((xref,tabs),depr)
      | Abbrev _ -> depr_abbrev ?loc ((xref,tabs),depr)
    in

    fun ?loc uwarns xref tabs ->
      uwarns.UserWarn.depr_qf |> Option.iter (fun depr -> depr_xref ?loc depr xref tabs);
      uwarns.UserWarn.warn_qf |> List.iter (user_warn ?loc)
end

module XRefV = struct
  include ExtRefOrdered
  let is_var = function
    | TrueGlobal (VarRef id) -> Some id
    | _ -> None

  module Map = ExtRefMap
end
module XRefSI = struct
  let stage = Summary.Stage.Interp
  let summary_name = "xreftab"
end
module XRefTab = MakeTab(XRefV)(XRefWarn) ()
module XRefs = MakeImperative(XRefTab)(XRefSI) ()

module UnivsV = struct
  include Univ.UGlobal
  let is_var _ = None
  module Map = HMap.Make(Univ.UGlobal)
  let stage = Summary.Stage.Interp
  let summary_name = "univtab"
end
module Univs = EasyNoWarn(UnivsV)()

module ModTypeV = struct
  include ModPath
  let is_var _ = None
  module Map = MPmap
  let stage = Summary.Stage.Synterp
  let summary_name = "modtypetab"
end
module ModTypes = EasyNoWarn(ModTypeV)()

module ModuleV = struct
  include ModPath
  let is_var _ = None
  module Map = MPmap
  let stage = Summary.Stage.Synterp
  let summary_name = "moduletab"
end
module Modules = EasyNoWarn(ModuleV)()

module OpenModV = struct
  include GlobDirRef
  let is_var _ = None
  module Map = Map.Make(GlobDirRef)
  let stage = Summary.Stage.Synterp
  let summary_name = "openmodtab"
end
module OpenMods = EasyNoWarn(OpenModV)()

(* Push functions *********************************************************)

let push_abbreviation ?user_warns visibility sp kn =
  XRefs.push ?user_warns visibility sp (Abbrev kn)

let remove_abbreviation sp kn =
  XRefs.remove sp (Abbrev kn)

let push ?user_warns vis sp kn = XRefs.push ?user_warns vis sp (TrueGlobal kn)

let push_modtype vis sp kn = ModTypes.push vis sp kn

let push_module vis dir mp = Modules.push vis dir mp

let push_dir vis dir dir_ref = OpenMods.push vis dir dir_ref

let push_universe vis sp univ = Univs.push vis sp univ

(* Reverse locate functions ***********************************************)

let path_of_global ref = XRefs.to_path (TrueGlobal ref)

let dirpath_of_global ref =
  fst (repr_path (path_of_global ref))

let basename_of_global ref =
  snd (repr_path (path_of_global ref))

let path_of_abbreviation kn = XRefs.to_path (Abbrev kn)

let path_of_module mp = Modules.to_path mp

let path_of_modtype mp = ModTypes.to_path mp

let path_of_universe mp = Univs.to_path mp

(* Shortest qualid functions **********************************************)

let shortest_qualid_of_global ?loc ctx ref = XRefs.shortest_qualid ?loc ctx (TrueGlobal ref)

let shortest_qualid_of_abbreviation ?loc ctx kn = XRefs.shortest_qualid ?loc ctx (Abbrev kn)

let shortest_qualid_of_module ?loc mp = Modules.shortest_qualid ?loc Id.Set.empty mp

let shortest_qualid_of_modtype ?loc kn = ModTypes.shortest_qualid ?loc Id.Set.empty kn

let shortest_qualid_of_dir ?loc sp = OpenMods.shortest_qualid ?loc Id.Set.empty sp

let shortest_qualid_of_universe ?loc avoid u =
  Univs.shortest_qualid_gen ?loc (fun id -> Id.Map.mem id avoid) u

let pr_global_env env ref =
  try pr_qualid (shortest_qualid_of_global env ref)
  with Not_found as exn ->
    let exn, info = Exninfo.capture exn in
    if !Flags.in_debugger then GlobRef.print ref
    else begin
      let () = if CDebug.(get_flag misc)
        then Feedback.msg_debug (Pp.str "pr_global_env not found")
      in
      Exninfo.iraise (exn, info)
    end

let is_warned_xref = XRefs.is_warned

let warn_user_warn_xref = XRefs.warn

let locate_extended_nowarn qid = XRefs.locate ~nowarn:true qid

let locate_extended qid = XRefs.locate qid

let locate qid = match locate_extended qid with
  | TrueGlobal ref -> ref
  | Abbrev _ -> raise Not_found

let locate_abbreviation qid = match locate_extended qid with
  | TrueGlobal _ -> raise Not_found
  | Abbrev kn -> kn

let locate_modtype qid = ModTypes.locate qid
let full_name_modtype qid = ModTypes.to_path (locate_modtype qid)

let locate_universe qid = Univs.locate qid

let locate_dir qid = OpenMods.locate qid

let locate_module qid = Modules.locate qid

let full_name_module qid = Modules.to_path (locate_module qid)

let locate_section qid =
  match locate_dir qid with
    | GlobDirRef.DirOpenSection dir -> dir
    | _ -> raise Not_found

let locate_extended_all qid = XRefs.locate_all qid

let locate_all qid =
  let l = locate_extended_all qid in
  CList.filter_map (function TrueGlobal a -> Some a | Abbrev _ -> None) l

let locate_extended_all_dir qid = OpenMods.locate_all qid

let locate_extended_all_modtype qid = ModTypes.locate_all qid

let locate_extended_all_module qid = Modules.locate_all qid

(* Completion *)
let completion_canditates qualid = XRefs.completion_candidates qualid

(* Derived functions *)

let locate_constant qid =
  let open GlobRef in
  match locate_extended qid with
    | TrueGlobal (ConstRef kn) -> kn
    | _ -> raise Not_found

let global_of_path sp =
  match XRefs.of_path sp with
  | TrueGlobal ref -> ref
  | _ -> raise Not_found

let extended_global_of_path = XRefs.of_path

let global qid =
  try match locate_extended qid with
    | TrueGlobal ref -> ref
    | Abbrev _ ->
        CErrors.user_err ?loc:qid.CAst.loc
          Pp.(str "Unexpected reference to a notation: " ++
           pr_qualid qid ++ str ".")
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    error_global_not_found ~info qid

let global_inductive qid =
  let open GlobRef in
  match global qid with
  | IndRef ind -> ind
  | ref ->
      CErrors.user_err ?loc:qid.CAst.loc
        Pp.(pr_qualid qid ++ spc () ++ str "is not an inductive type.")

(* Exists functions ********************************************************)

let exists_cci = XRefs.exists

let exists_dir = OpenMods.exists

let exists_module = Modules.exists

let exists_modtype = ModTypes.exists

let exists_universe = Univs.exists

(* Source locations *)

open Globnames

let cci_loc_table : Loc.t ExtRefMap.t ref = Summary.ref ~name:"constant-loc-table" ExtRefMap.empty

let set_cci_src_loc kn loc = cci_loc_table := ExtRefMap.add kn loc !cci_loc_table

let cci_src_loc kn = ExtRefMap.find_opt kn !cci_loc_table
