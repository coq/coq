(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Vernacexpr

module NamedDecl = Context.Named.Declaration

type filter_function =
  GlobRef.t -> Decls.logical_kind option -> env -> Evd.evar_map -> constr -> bool
type display_function =
  GlobRef.t -> Decls.logical_kind option -> env -> Evd.evar_map -> constr -> unit

(* This option restricts the output of [SearchPattern ...], etc.
to the names of the symbols matching the
query, separated by a newline. This type of output is useful for
editors (like emacs), to generate a list of completion candidates
without having to parse through the types of all symbols. *)

type glob_search_item =
  | GlobSearchSubPattern of glob_search_where * bool * constr_pattern
  | GlobSearchString of string
  | GlobSearchKind of Decls.logical_kind
  | GlobSearchFilter of (GlobRef.t -> bool)

type glob_search_request =
  | GlobSearchLiteral of glob_search_item
  | GlobSearchDisjConj of (bool * glob_search_request) list list

module SearchBlacklist =
  Goptions.MakeStringTable
    (struct
      let key = ["Search";"Blacklist"]
      let title = "Current search blacklist : "
      let member_message s b =
        str "Search blacklist does " ++ (if b then mt () else str "not ") ++ str "include " ++ str s
     end)

(* The functions iter_constructors and iter_declarations implement the behavior
   needed for the Rocq searching commands.
   These functions take as first argument the procedure
   that will be called to treat each entry.  This procedure receives the name
   of the object, the assumptions that will make it possible to print its type,
   and the constr term that represent its type. *)

let iter_constructors indsp u fn env sigma nconstr =
  for i = 1 to nconstr do
    let typ = Inductive.type_of_constructor ((indsp, i), u) (Inductive.lookup_mind_specif env indsp) in
    fn (GlobRef.ConstructRef (indsp, i)) None env sigma typ
  done

(* FIXME: this is a Libobject hack that should be replaced with a proper
   registration mechanism. *)
module DynHandle = Libobject.Dyn.Map(struct type 'a t = 'a -> unit end)

let handle h (Libobject.Dyn.Dyn (tag, o)) = match DynHandle.find tag h with
| f -> f o
| exception Not_found -> ()

(* General search over declarations *)
let generic_search env sigma (fn : GlobRef.t -> Decls.logical_kind option -> env -> Evd.evar_map -> constr -> unit) =
  List.iter (fun d -> fn (GlobRef.VarRef (NamedDecl.get_id d)) None env sigma (NamedDecl.get_type d))
    (Environ.named_context env);
  let iter_obj prefix lobj = match lobj with
    | AtomicObject o ->
      let handler =
        DynHandle.add Declare.Internal.Constant.tag begin fun (id,obj) ->
          let kn = KerName.make prefix.Nametab.obj_mp (Label.of_id id) in
          let cst = Global.constant_of_delta_kn kn in
          let gr = GlobRef.ConstRef cst in
          let (typ, _) = Typeops.type_of_global_in_context (Global.env ()) gr in
          let kind = Declare.Internal.Constant.kind obj in
          fn gr (Some kind) env sigma typ
        end @@
        DynHandle.add DeclareInd.Internal.objInductive begin fun (id,_) ->
          let kn = KerName.make prefix.Nametab.obj_mp (Label.of_id id) in
          let mind = Global.mind_of_delta_kn kn in
          let mib = Global.lookup_mind mind in
          let iter_packet i mip =
            let ind = (mind, i) in
            let u = UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
            let typ = Inductive.type_of_inductive (Inductive.lookup_mind_specif env ind, u) in
            let () = fn (GlobRef.IndRef ind) None env sigma typ in
            let len = Array.length mip.mind_user_lc in
            iter_constructors ind u fn env sigma len
          in
          Array.iteri iter_packet mib.mind_packets
        end @@
        DynHandle.empty
      in
      handle handler o
    | _ -> ()
  in
  try Declaremods.iter_all_interp_segments iter_obj
  with Not_found -> ()

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
  type t = GlobRef.t * Decls.logical_kind option * Environ.env * Evd.evar_map * Constr.t * priority
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

  let priority gref t : priority =
    -(3*(num_symbols t) + size t)

  let compare (_,_,_,_,_,p1) (_,_,_,_,_,p2) =
    Stdlib.compare p1 p2
end

module PriorityQueue = Heap.Functional(ConstrPriority)

let rec iter_priority_queue q fn =
  (* Tail-rec! *)
  match PriorityQueue.maximum q with
  | (gref,kind,env,sigma,t,_) ->
    fn gref kind env sigma t;
    iter_priority_queue (PriorityQueue.remove q) fn
  | exception Heap.EmptyHeap -> ()

let prioritize_search seq fn =
  let acc = ref PriorityQueue.empty in
  let iter gref kind env sigma t =
    let p = ConstrPriority.priority gref t in
    acc := PriorityQueue.add (gref,kind,env,sigma,t,p) !acc
  in
  let () = seq iter in
  iter_priority_queue !acc fn

(** Filters *)

(** This function tries to see whether the conclusion matches a pattern.
    FIXME: this is quite dummy, we may find a more efficient algorithm. *)
let rec pattern_filter pat ref env sigma typ =
  let typ = Termops.strip_outer_cast sigma typ in
  if Constr_matching.is_matching env sigma pat typ then true
  else match EConstr.kind sigma typ with
  | Prod (_, _, typ)
  | LetIn (_, _, _, typ) -> pattern_filter pat ref env sigma typ
  | _ -> false

let full_name_of_reference ref =
  let (dir,id) = repr_path (Nametab.path_of_global ref) in
  DirPath.to_string dir ^ "." ^ Id.to_string id

(** Whether a reference is blacklisted *)
let blacklist_filter ref kind env sigma typ =
  let name = full_name_of_reference ref in
  let is_not_bl str = not (String.string_contains ~where:name ~what:str) in
  CString.Set.for_all is_not_bl (SearchBlacklist.v ())

let module_filter mods ref kind env sigma typ =
  let sp = Nametab.path_of_global ref in
  let sl = dirpath sp in
  match mods with
  | SearchOutside mods ->
    let is_outside md = not (is_dirpath_prefix_of md sl) in
    List.for_all is_outside mods
  | SearchInside mods ->
    let is_inside md = is_dirpath_prefix_of md sl in
    List.is_empty mods || List.exists is_inside mods

let name_of_reference ref = Id.to_string (Nametab.basename_of_global ref)

let search_filter query gr kind env sigma typ = match query with
| GlobSearchSubPattern (where,head,pat) ->
  let open Context.Rel.Declaration in
  let rec collect env hyps typ =
    match Constr.kind typ with
    | LetIn (na,b,t,c) -> collect (push_rel (LocalDef (na,b,t)) env) ((env,b) :: (env,t) :: hyps) c
    | Prod (na,t,c) -> collect (push_rel (LocalAssum (na,t)) env) ((env,t) :: hyps) c
    | _ -> (hyps,(env,typ)) in
  let typl= match where with
  | InHyp -> fst (collect env [] typ)
  | InConcl -> [snd (collect env [] typ)]
  | Anywhere -> if head then let hyps, ccl = collect env [] typ in ccl :: hyps else [env,typ] in
  List.exists (fun (env,typ) ->
      let f =
        if head then Constr_matching.is_matching_head
        else Constr_matching.is_matching_appsubterm ~closed:false in
      f env sigma pat (EConstr.of_constr typ)) typl
| GlobSearchString s ->
  String.string_contains ~where:(name_of_reference gr) ~what:s
| GlobSearchKind k -> (match kind with None -> false | Some k' -> k = k')
| GlobSearchFilter f -> f gr

(** SearchPattern *)

let search_pattern env sigma pat mods pr_search =
  let filter ref kind env sigma typ =
    module_filter mods ref kind env sigma typ &&
    pattern_filter pat ref env sigma (EConstr.of_constr typ) &&
    blacklist_filter ref kind env sigma typ
  in
  let iter ref kind env sigma typ =
    if filter ref kind env sigma typ then pr_search ref kind env sigma typ
  in
  generic_search env sigma iter

(** SearchRewrite *)

let eq () = Rocqlib.(lib_ref "core.eq.type")

let rewrite_pat1 pat =
  PApp (PRef (eq ()), [| PMeta None; pat; PMeta None |])

let rewrite_pat2 pat =
  PApp (PRef (eq ()), [| PMeta None; PMeta None; pat |])

let search_rewrite env sigma pat mods pr_search =
  let pat1 = rewrite_pat1 pat in
  let pat2 = rewrite_pat2 pat in
  let filter ref kind env sigma typ =
    module_filter mods ref kind env sigma typ &&
    (pattern_filter pat1 ref env sigma (EConstr.of_constr typ) ||
       pattern_filter pat2 ref env sigma (EConstr.of_constr typ)) &&
    blacklist_filter ref kind env sigma typ
  in
  let iter ref kind env sigma typ =
    if filter ref kind env sigma typ then pr_search ref kind env sigma typ
  in
  generic_search env sigma iter

(** Search *)

let search env sigma items mods pr_search =
  let filter ref kind env sigma typ =
    let eqb b1 b2 = if b1 then b2 else not b2 in
    module_filter mods ref kind env sigma typ &&
      let rec aux = function
        | GlobSearchLiteral i -> search_filter i ref kind env sigma typ
        | GlobSearchDisjConj l -> List.exists (List.for_all aux') l
      and aux' (b,s) = eqb b (aux s) in
      List.for_all aux' items && blacklist_filter ref kind env sigma typ
  in
  let iter ref kind env sigma typ =
    if filter ref kind env sigma typ then pr_search ref kind env sigma typ
  in
  generic_search env sigma iter

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

let interface_search env sigma =
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
  fun flags ->
  let (name, tpe, subtpe, mods, blacklist) =
    extract_flags [] [] [] [] false flags
  in
  let filter_function ref env sigma constr =
    let id = Names.Id.to_string (Nametab.basename_of_global ref) in
    let path = Libnames.dirpath (Nametab.path_of_global ref) in
    let toggle x b = if x then b else not b in
    let match_name (regexp, flag) =
      toggle (Str.string_match regexp id 0) flag
    in
    let match_type (pat, flag) =
      toggle (Constr_matching.is_matching env sigma pat (EConstr.of_constr constr)) flag
    in
    let match_subtype (pat, flag) =
      toggle
        (Constr_matching.is_matching_appsubterm ~closed:false
           env sigma pat (EConstr.of_constr constr)) flag
    in
    let match_module (mdl, flag) =
      toggle (Libnames.is_dirpath_prefix_of mdl path) flag
    in
    List.for_all match_name name &&
    List.for_all match_type tpe &&
    List.for_all match_subtype subtpe &&
    List.for_all match_module mods &&
    (blacklist || blacklist_filter ref kind env sigma constr)
  in
  let ans = ref [] in
  let print_function ref env sigma constr =
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
  let iter ref kind env sigma typ =
    if filter_function ref env sigma typ then print_function ref env sigma typ
  in
  let () = generic_search env sigma iter in
  !ans
