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
open Nameops

(** This file contains methods for manipulating qualified evar names. *)

module EvSet = Evar.Set
module EvMap = Evar.Map

(** If true, this option enables automatic generation of goal names. *)
let { Goptions.get = generate_goal_names } =
  Goptions.declare_bool_option_and_ref
    ~key:["Generate";"Goal";"Names"]
    ~value:false
    ()

(** Internal representation of qualified evar names.

    Example: "x.y.z" is represented as [{ basename: "z"; path: ["y"; "x"] }] *)
module EvarQualid :
sig
  type t =
    { basename: Id.t;
      path: Id.t list }
  val make : Libnames.qualid -> t
  val repr : t -> Libnames.full_path
end =
struct
  type t =
    { basename: Id.t;
      path: Id.t list }

  let make path =
    let (dp, id) = Libnames.repr_qualid_noabs path in
    { basename = id; path = DirPath.repr dp }

  let repr { basename; path } =
    Libnames.make_path (DirPath.make path) basename

end

(** Module for evar name resolution, using a reversed trie.

    Example: given evars "true.A" (?X1), "true.A" (?X2) and "false.A" (?X3), we
    have the following trie:

    [
    {
      A -> {
        true (?X1, ?X2),
        false (?X3)
      }
    }
    ]

    In this representation, determining whether a qualified name is unambiguous
    amounts to checking whether the node has a single value. For example, "A"
    does not resolve to an evar, "true.A" is ambiguous (?X1, ?X2), while
    "false.A" (?X3) is unambiguous.
 *)
module NameResolution :
sig
  type t

  (** Returns an empty trie. *)
  val empty : t

  (** Adds a new binding for the evar at the shortest unambiguous suffix of the
      given qualified name, if possible. If there is no such suffix, creates an
      ambiguous node. *)
  val add : EvarQualid.t -> Evar.t -> t -> t

  (** Transfers the qualified name of the first evar to the second evar. *)
  val transfer : EvarQualid.t -> Evar.t -> Evar.t -> t -> t

  (** Removes the qualified name of the given evar from name resolution. *)
  val remove : EvarQualid.t -> Evar.t -> t -> t

  (** Returns the shortest unambiguous name of the given qualified name.
      Raises [Not_found] if the evar is not present at a suffix of the qualified
      name. *)
  val shortest_name : EvarQualid.t -> Evar.t -> t -> EvarQualid.t

  (** Returns the list of bindings for the given qualified name. *)
  val find : EvarQualid.t -> t -> Evar.Set.t

  (** Returns true if there exists a binding that has the given basename. *)
  val mem_basename : Id.t -> t -> bool
end =
struct
  (** Represents a trie node. For code deduplication reasons, the root is also a node
      with an empty value. *)
  type t =
    { value: Evar.Set.t;
      children: t Id.Map.t }

  open EvarQualid

  let empty =
    { value = Evar.Set.empty; children = Id.Map.empty }

  let is_empty { value; children } =
    Evar.Set.is_empty value && Id.Map.is_empty children

  let rec add path ev node =
    match path with
    | segment :: rest ->
       let update = function
         | Some child -> Some (add rest ev child)
         | None -> Some { value = Evar.Set.singleton ev; children = Id.Map.empty }
       in
       { node with children = Id.Map.update segment update node.children }
    | [] ->
       { node with value = Evar.Set.add ev node.value }

  let add { basename; path } ev trie = add (basename :: path) ev trie

  let rec transfer path ev ev' node =
    match path with
    | segment :: rest ->
       { node with children = Id.Map.modify segment (fun _ child -> transfer rest ev ev' child) node.children }
    | [] ->
       { node with value = Evar.Set.add ev' (Evar.Set.remove ev node.value) }

  let transfer { basename; path } ev ev' trie = transfer (basename :: path) ev ev' trie

  let[@tail_mod_cons] rec shortest_name path ev node =
    if Evar.Set.mem ev node.value then []
    else
      match path with
      | segment :: rest -> segment :: shortest_name rest ev (Id.Map.find segment node.children)
      | [] -> raise Not_found

  let shortest_name { basename; path } ev trie =
    match shortest_name (basename :: path) ev trie with
    | basename :: path -> { basename; path }
    | [] -> assert false

  let rec find path node =
    match path with
    | segment :: rest ->
       begin match Id.Map.find_opt segment node.children with
       | Some segment -> find rest segment
       | None -> Evar.Set.empty
       end
    | [] -> node.value

  let find { basename; path } trie = find (basename :: path) trie

  let rec remove path ev node =
    match path with
    | segment :: rest ->
       let update_child = function
         | Some child -> remove rest ev child
         | None -> None
       in
       let node = { node with children = Id.Map.update segment update_child node.children } in
       (* Prune empty nodes. *)
       if is_empty node then None else Some node
    | [] ->
       let node = { node with value = Evar.Set.remove ev node.value } in
       if is_empty node then None else Some node

  let remove { basename; path } ev trie =
    match remove (basename :: path) ev trie with
    | Some trie -> trie
    | None -> empty

  let mem_basename basename trie =
    Id.Map.mem basename trie.children
end

type t =
  { basename_map : Id.t EvMap.t;
    (** Map from evar to basename. *)

    name_resolution : NameResolution.t;
    (** Trie for resolving qualified names to evars. *)

    fresh_gen : Fresh.t;
    (** Fresh basename generator (to support [refine ?[?A]]) *)

    parent_map : Evar.t EvMap.t;
    (** Map from evar to its parent, if any. *)

    children_map : EvSet.t EvMap.t;
    (** Map from an evar to its children that are pending. Essentially the
        reverse of [parent_map]. *)

    removed_evars : EvSet.t;
    (** Set of evars marked for removal, and thus unfocusable, whose names are still used as
        the parent of an open goal. *)
  }

let empty =
  { basename_map = EvMap.empty;
    name_resolution = NameResolution.empty;
    fresh_gen = Fresh.empty;
    parent_map = EvMap.empty;
    children_map = EvMap.empty;
    removed_evars = EvSet.empty
  }

(** Returns the absolute path of [ev], obtained by following the [parent_map]. *)
let[@tail_mod_cons] rec path ev evn =
  match EvMap.find_opt ev evn.parent_map with
  | Some parent ->
     begin match EvMap.find_opt parent evn.basename_map with
     | Some parent_name -> parent_name :: path parent evn
     | None -> []
     end
  | None -> []

(** Return the absolute qualified name of [ev]. *)
let absolute_name ev evn =
  match EvMap.find_opt ev evn.basename_map with
  | Some basename -> Some EvarQualid.{ basename; path = path ev evn }
  | None -> None

(** Returns the shortest name that resolves to [ev], or [None] if [ev] does not
    resolve to a name. *)
let shortest_name ev evn =
  match absolute_name ev evn with
  | Some name -> Some (NameResolution.shortest_name name ev evn.name_resolution)
  | None -> None

(* Returns the set of focusable evars that have the given qualid as name.  *)
let get_matching_evars qualid evn =
  let evs = NameResolution.find qualid evn.name_resolution in
  (* Do not consider removed evars as conflicts for name resolution purposes *)
  Evar.Set.diff evs evn.removed_evars

let register_parent ev parent evn =
  let add_child = function
    | Some children -> Some (EvSet.add ev children)
    | None -> Some (EvSet.singleton ev)
  in
  { evn with
    parent_map = EvMap.add ev parent evn.parent_map;
    children_map = EvMap.update parent add_child evn.children_map }

let add basename ev ?parent evn =
  let evn =
    match parent with
    | Some parent -> register_parent ev parent evn
    | None -> evn
  in
  let qualid = EvarQualid.{ basename; path = path ev evn } in
  { evn with
    basename_map = EvMap.add ev basename evn.basename_map;
    name_resolution = NameResolution.add qualid ev evn.name_resolution;
    fresh_gen = Fresh.add basename evn.fresh_gen }

let add_fresh basename ev ?parent evn =
  let evn =
    match parent with
    | Some parent -> register_parent ev parent evn
    | None -> evn
  in
  let qualid = EvarQualid.{ basename; path = path ev evn } in
  let conflicts = get_matching_evars qualid evn in
  if Evar.Set.is_empty conflicts then
    (* No need to give the parent since it's already registered *)
    add basename ev evn
  else
    (* Generate a fresh basename and try again. *)
    let basename, fresh_gen = Fresh.fresh basename evn.fresh_gen in
    add basename ev { evn with fresh_gen }

let rec remove ev evn =
  match EvMap.find_opt ev evn.basename_map with
  | None -> evn
  | Some basename ->
    (* When defining an evar and making its name unresolvable, there are two scenarios:
       - The evar has no remaining children, in which case we can safely remove
         it from all maps since it is not used for name resolution. We also try
         to remove recursively its parent, since solving the evar might have
         closed the parent.
       - The evar has some children which might rely on the parent's name for
         name resolution. In that case, we simply add it to [removed_evars] (so
         that [name_of ev] fails), and removal will occur when all children will
         be solved. *)
    let children =
      match EvMap.find_opt ev evn.children_map with
      | Some children -> children
      | None -> EvSet.empty
    in
    if EvSet.is_empty children then
      let parent = EvMap.find_opt ev evn.parent_map in
      let name_resolution =
        match shortest_name ev evn with
        | Some name -> NameResolution.remove name ev evn.name_resolution
        | None -> assert false
      in
      let evn =
        { basename_map = EvMap.remove ev evn.basename_map;
          name_resolution;
          fresh_gen =
            (* If the basename still exists in the new trie, do not remove. *)
            if NameResolution.mem_basename basename name_resolution then evn.fresh_gen
            else Fresh.remove basename evn.fresh_gen;
          children_map = EvMap.remove ev evn.children_map;
          parent_map = EvMap.remove ev evn.parent_map;
          removed_evars = EvSet.remove ev evn.removed_evars;
        }
      in
      (* If there is a parent, try to remove it recursively as well. *)
      match parent with
      | Some parent ->
         let evn = remove parent evn in
         (* Rollback if removal failed. *)
         { evn with removed_evars = EvSet.remove ev evn.removed_evars }
      | None -> evn
    else
      (* Mark [ev] as deleted. *)
      { evn with removed_evars = EvSet.add ev evn.removed_evars }

let transfer_name ev ev' evn =
  (* We assume that [ev] is an open goal, hence undefined and
     has no children. *)

  (* Transfer the name. *)
  let basename_map, name_resolution =
    match shortest_name ev evn with
    | Some name ->
       let basename_map = EvMap.add ev' name.basename (EvMap.remove ev evn.basename_map) in
       let name_resolution = NameResolution.transfer name ev ev' evn.name_resolution in
       basename_map, name_resolution
    | None -> (* [ev] has no name. *)
       evn.basename_map, evn.name_resolution
  in
  (* If [ev] has a parent, we update the parent's children. *)
  let parent_map, children_map =
    match EvMap.find_opt ev evn.parent_map with
    | Some parent ->
       let parent_map = EvMap.add ev' parent (EvMap.remove ev evn.parent_map) in
       let children_map = EvMap.modify parent (fun _ children -> EvSet.add ev' (EvSet.remove ev children)) evn.children_map in
       parent_map, children_map
    | None ->
       evn.parent_map, evn.children_map
  in
  { evn with basename_map; name_resolution; parent_map; children_map }

type set_kind =
| SetEmpty
| SetSingleton of Evar.t
| SetOther

let classify_set s =
  if Evar.Set.is_empty s then SetEmpty
  else
    let evk = Evar.Set.choose s in
    let s = Evar.Set.remove evk s in
    if Evar.Set.is_empty s then SetSingleton evk
    else SetOther

let name_of ev evn =
  match shortest_name ev evn with
  | None -> None
  | Some name ->
    let conflicts = get_matching_evars name evn in
    (* TODO: we should the caller handle the conflict themselves instead of
       generating nonsensical names in linear time. *)
    match classify_set conflicts with
    | SetEmpty | SetSingleton _ -> Some (EvarQualid.repr name)
    | SetOther ->
      let nconflicts = Evar.Set.cardinal conflicts in
      (* If the qualified name is ambiguous, we append a suffix corresponding to the index in the list. *)
      let { EvarQualid.basename; path } = name in
      let i = nconflicts - CList.index Evar.equal ev (Evar.Set.elements conflicts) - 1 in
      let basename =
        if Int.equal i (-1) then basename
        else Id.of_string ((Id.to_string name.basename) ^ (string_of_int i))
      in
      Some (Libnames.make_path (DirPath.make path) basename)

let has_name ev evn =
  not (EvSet.mem ev evn.removed_evars) && EvMap.mem ev evn.basename_map

let has_unambiguous_name ev evn =
  match shortest_name ev evn with
  | None -> false
  | Some name ->
    let matches = get_matching_evars name evn in
    match classify_set matches with
    | SetEmpty | SetOther -> false
    | SetSingleton e -> Evar.equal e ev

let resolve fp evn =
  let qualid = EvarQualid.make fp in
  let evs = get_matching_evars qualid evn in
  let open Pp in
  match classify_set evs with
  | SetEmpty -> raise Not_found
  | SetSingleton ev -> ev
  | SetOther ->
    CErrors.user_err ?loc:fp.loc (str "Ambiguous evar name " ++ Libnames.pr_qualid fp ++ str ".")
