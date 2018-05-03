(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Constr
open Declarations
open Libobject
open Environ
open Pattern
open Libnames
open Globnames
open Nametab

module NamedDecl = Context.Named.Declaration

type filter_function = GlobRef.t -> env -> constr -> bool
type display_function = GlobRef.t -> env -> constr -> unit

(* This option restricts the output of [SearchPattern ...],
[SearchAbout ...], etc. to the names of the symbols matching the
query, separated by a newline. This type of output is useful for
editors (like emacs), to generate a list of completion candidates
without having to parse thorugh the types of all symbols. *)

type glob_search_about_item =
  | GlobSearchSubPattern of constr_pattern
  | GlobSearchString of string

module SearchBlacklist =
  Goptions.MakeStringTable
    (struct
      let key = ["Search";"Blacklist"]
      let title = "Current search blacklist : "
      let member_message s b =
	str "Search blacklist does " ++ (if b then mt () else str "not ") ++ str "include " ++ str s
     end)

(* The functions iter_constructors and iter_declarations implement the behavior
   needed for the Coq searching commands.
   These functions take as first argument the procedure
   that will be called to treat each entry.  This procedure receives the name
   of the object, the assumptions that will make it possible to print its type,
   and the constr term that represent its type. *)

let iter_constructors indsp u fn env nconstr =
  for i = 1 to nconstr do
    let typ = Inductiveops.type_of_constructor env ((indsp, i), u) in
    fn (ConstructRef (indsp, i)) env typ
  done

let iter_named_context_name_type f =
  List.iter (fun decl -> f (NamedDecl.get_id decl) (NamedDecl.get_type decl))

(* General search over hypothesis of a goal *)
let iter_hypothesis glnum (fn : GlobRef.t -> env -> constr -> unit) =
  let env = Global.env () in
  let iter_hyp idh typ = fn (VarRef idh) env typ in
  let evmap,e = Pfedit.get_goal_context glnum in
  let pfctxt = named_context e in
  iter_named_context_name_type iter_hyp pfctxt

(* General search over declarations *)
let iter_declarations (fn : GlobRef.t -> env -> constr -> unit) =
  let env = Global.env () in
  let iter_obj (sp, kn) lobj = match object_tag lobj with
  | "VARIABLE" ->
    begin try
      let decl = Global.lookup_named (basename sp) in
      fn (VarRef (NamedDecl.get_id decl)) env (NamedDecl.get_type decl)
    with Not_found -> (* we are in a section *) () end
  | "CONSTANT" ->
    let cst = Global.constant_of_delta_kn kn in
    let gr = ConstRef cst in
    let (typ, _) = Global.type_of_global_in_context (Global.env ()) gr in
      fn gr env typ
  | "INDUCTIVE" ->
    let mind = Global.mind_of_delta_kn kn in
    let mib = Global.lookup_mind mind in
    let iter_packet i mip =
      let ind = (mind, i) in
      let u = Univ.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
      let i = (ind, u) in
      let typ = Inductiveops.type_of_inductive env i in
      let () = fn (IndRef ind) env typ in
      let len = Array.length mip.mind_user_lc in
      iter_constructors ind u fn env len
    in
    Array.iteri iter_packet mib.mind_packets
  | _ -> ()
  in
  try Declaremods.iter_all_segments iter_obj
  with Not_found -> ()

let generic_search glnumopt fn =
  (match glnumopt with
  | None -> ()
  | Some glnum ->  iter_hypothesis glnum fn);
  iter_declarations fn

(** This module defines a preference on constrs in the form of a
    [compare] function (preferred constr must be big for this
    functions, so preferences such as small constr must use a reversed
    order). This priority will be used to order search results and
    propose first results which are more likely to be relevant to the
    query, this is why the type [t] contains the other elements
    required of a search. *)
module ConstrPriority = struct

  (* The priority is memoised here. Because of the very localised use
     of this module, it is not worth it making a convenient interface. *)
  type t = GlobRef.t * Environ.env * Constr.t * priority
  and priority = int

  module ConstrSet = CSet.Make(Constr)

  (** A measure of the size of a term *)
  let rec size t =
    Constr.fold (fun s t -> 1 + s + size t) 0 t

  (** Set of the "symbols" (definitions, inductives, constructors)
      which appear in a term. *)
  let rec symbols acc t =
    let open Constr in
    match kind t with
    | Const _ | Ind _ | Construct _ -> ConstrSet.add t acc
    | _ -> Constr.fold symbols acc t

  (** The number of distinct "symbols" (see {!symbols}) which appear
      in a term. *)
  let num_symbols t =
    ConstrSet.(cardinal (symbols empty t))

  let priority t : priority =
    -(3*(num_symbols t) + size t)

  let compare (_,_,_,p1) (_,_,_,p2) =
    Pervasives.compare p1 p2
end

module PriorityQueue = Heap.Functional(ConstrPriority)

let rec iter_priority_queue q fn =
  (* use an option to make the function tail recursive. Will be
     obsoleted with Ocaml 4.02 with the [match … with | exception …]
     syntax. *)
  let next = begin
      try Some (PriorityQueue.maximum q)
      with Heap.EmptyHeap -> None
  end in
  match next with
  | Some (gref,env,t,_) ->
    fn gref env t;
    iter_priority_queue (PriorityQueue.remove q) fn
  | None -> ()

let prioritize_search seq fn =
  let acc = ref PriorityQueue.empty in
  let iter gref env t =
    let p = ConstrPriority.priority t in
    acc := PriorityQueue.add (gref,env,t,p) !acc
  in
  let () = seq iter in
  iter_priority_queue !acc fn

(** Filters *)

(** This function tries to see whether the conclusion matches a pattern. *)
(** FIXME: this is quite dummy, we may find a more efficient algorithm. *)
let rec pattern_filter pat ref env sigma typ =
  let typ = Termops.strip_outer_cast sigma typ in
  if Constr_matching.is_matching env sigma pat typ then true
  else match EConstr.kind sigma typ with
  | Prod (_, _, typ)
  | LetIn (_, _, _, typ) -> pattern_filter pat ref env sigma typ
  | _ -> false

let rec head_filter pat ref env sigma typ =
  let typ = Termops.strip_outer_cast sigma typ in
  if Constr_matching.is_matching_head env sigma pat typ then true
  else match EConstr.kind sigma typ with
  | Prod (_, _, typ)
  | LetIn (_, _, _, typ) -> head_filter pat ref env sigma typ
  | _ -> false

let full_name_of_reference ref =
  let (dir,id) = repr_path (path_of_global ref) in
  DirPath.to_string dir ^ "." ^ Id.to_string id

(** Whether a reference is blacklisted *)
let blacklist_filter_aux () =
  let l = SearchBlacklist.elements () in
  fun ref env typ ->
  let name = full_name_of_reference ref in
  let is_not_bl str = not (String.string_contains ~where:name ~what:str) in
  List.for_all is_not_bl l

let module_filter (mods, outside) ref env typ =
  let sp = path_of_global ref in
  let sl = dirpath sp in
  let is_outside md = not (is_dirpath_prefix_of md sl) in
  let is_inside md = is_dirpath_prefix_of md sl in
  if outside then List.for_all is_outside mods
  else List.is_empty mods || List.exists is_inside mods

let name_of_reference ref = Id.to_string (basename_of_global ref)

let search_about_filter query gr env typ = match query with
| GlobSearchSubPattern pat ->
  Constr_matching.is_matching_appsubterm ~closed:false env (Evd.from_env env) pat (EConstr.of_constr typ)
| GlobSearchString s ->
  String.string_contains ~where:(name_of_reference gr) ~what:s


(** SearchPattern *)

let search_pattern gopt pat mods pr_search =
  let blacklist_filter = blacklist_filter_aux () in
  let filter ref env typ =
    module_filter mods ref env typ &&
    pattern_filter pat ref env (Evd.from_env env) (* FIXME *) (EConstr.of_constr typ) &&
    blacklist_filter ref env typ
  in
  let iter ref env typ =
    if filter ref env typ then pr_search ref env typ
  in
  generic_search gopt iter

(** SearchRewrite *)

let eq = Coqlib.glob_eq

let rewrite_pat1 pat =
  PApp (PRef eq, [| PMeta None; pat; PMeta None |])

let rewrite_pat2 pat =
  PApp (PRef eq, [| PMeta None; PMeta None; pat |])

let search_rewrite gopt pat mods pr_search =
  let pat1 = rewrite_pat1 pat in
  let pat2 = rewrite_pat2 pat in
  let blacklist_filter = blacklist_filter_aux () in
  let filter ref env typ =
    module_filter mods ref env typ &&
    (pattern_filter pat1 ref env (Evd.from_env env) (* FIXME *) (EConstr.of_constr typ) ||
       pattern_filter pat2 ref env (Evd.from_env env) (EConstr.of_constr typ)) &&
    blacklist_filter ref env typ
  in
  let iter ref env typ =
    if filter ref env typ then pr_search ref env typ
  in
  generic_search gopt iter

(** Search *)

let search_by_head gopt pat mods pr_search =
  let blacklist_filter = blacklist_filter_aux () in
  let filter ref env typ =
    module_filter mods ref env typ &&
    head_filter pat ref env (Evd.from_env env) (* FIXME *) (EConstr.of_constr typ) &&
    blacklist_filter ref env typ
  in
  let iter ref env typ =
    if filter ref env typ then pr_search ref env typ
  in
  generic_search gopt iter

(** SearchAbout *)

let search_about gopt items mods pr_search =
  let blacklist_filter = blacklist_filter_aux () in
  let filter ref env typ =
    let eqb b1 b2 = if b1 then b2 else not b2 in
    module_filter mods ref env typ &&
    List.for_all
      (fun (b,i) -> eqb b (search_about_filter i ref env typ)) items &&
    blacklist_filter ref env typ
  in
  let iter ref env typ =
    if filter ref env typ then pr_search ref env typ
  in
  generic_search gopt iter

type search_constraint =
  | Name_Pattern of Str.regexp
  | Type_Pattern of Pattern.constr_pattern
  | SubType_Pattern of Pattern.constr_pattern
  | In_Module of Names.DirPath.t
  | Include_Blacklist

type 'a coq_object = {
  coq_object_prefix : string list;
  coq_object_qualid : string list;
  coq_object_object : 'a;
}

let interface_search =
  let rec extract_flags name tpe subtpe mods blacklist = function
  | [] -> (name, tpe, subtpe, mods, blacklist)
  | (Name_Pattern regexp, b) :: l ->
    extract_flags ((regexp, b) :: name) tpe subtpe mods blacklist l
  | (Type_Pattern pat, b) :: l ->
    extract_flags name ((pat, b) :: tpe) subtpe mods blacklist l
  | (SubType_Pattern pat, b) :: l ->
    extract_flags name tpe ((pat, b) :: subtpe) mods blacklist l
  | (In_Module id, b) :: l ->
    extract_flags name tpe subtpe ((id, b) :: mods) blacklist l
  | (Include_Blacklist, b) :: l ->
    extract_flags name tpe subtpe mods b l
  in
  fun ?glnum flags ->
  let (name, tpe, subtpe, mods, blacklist) =
    extract_flags [] [] [] [] false flags
  in
  let blacklist_filter = blacklist_filter_aux () in
  let filter_function ref env constr =
    let id = Names.Id.to_string (Nametab.basename_of_global ref) in
    let path = Libnames.dirpath (Nametab.path_of_global ref) in
    let toggle x b = if x then b else not b in
    let match_name (regexp, flag) =
      toggle (Str.string_match regexp id 0) flag
    in
    let match_type (pat, flag) =
      toggle (Constr_matching.is_matching env (Evd.from_env env) pat (EConstr.of_constr constr)) flag
    in
    let match_subtype (pat, flag) =
      toggle
        (Constr_matching.is_matching_appsubterm ~closed:false 
           env (Evd.from_env env) pat (EConstr.of_constr constr)) flag
    in
    let match_module (mdl, flag) =
      toggle (Libnames.is_dirpath_prefix_of mdl path) flag
    in
    List.for_all match_name name &&
    List.for_all match_type tpe &&
    List.for_all match_subtype subtpe &&
    List.for_all match_module mods &&
    (blacklist || blacklist_filter ref env constr)
  in
  let ans = ref [] in
  let print_function ref env constr =
    let fullpath = DirPath.repr (Nametab.dirpath_of_global ref) in
    let qualid = Nametab.shortest_qualid_of_global Id.Set.empty ref in
    let (shortpath, basename) = Libnames.repr_qualid qualid in
    let shortpath = DirPath.repr shortpath in
    (* [shortpath] is a suffix of [fullpath] and we're looking for the missing
       prefix *)
    let rec prefix full short accu = match full, short with
    | _, [] ->
      let full = List.rev_map Id.to_string full in
      (full, accu)
    | _ :: full, m :: short ->
      prefix full short (Id.to_string m :: accu)
    | _ -> assert false
    in
    let (prefix, qualid) = prefix fullpath shortpath [Id.to_string basename] in
    let answer = {
      coq_object_prefix = prefix;
      coq_object_qualid = qualid;
      coq_object_object = constr;
    } in
    ans := answer :: !ans;
  in
  let iter ref env typ =
    if filter_function ref env typ then print_function ref env typ
  in
  let () = generic_search glnum iter in
  !ans

let blacklist_filter ref env typ =
  blacklist_filter_aux () ref env typ
