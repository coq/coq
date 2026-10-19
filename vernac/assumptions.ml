(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The following definitions are used by the function
   [assumptions] which gives as an output the set of all
   axioms and sections variables on which a given term depends
   in a context (expectingly the Global context) *)

(* Initial author: Arnaud Spiwack
   Module-traversing code: Pierre Letouzey *)

open Util
open Names
open Declarations
open Mod_declarations

module NamedDecl = Context.Named.Declaration

(** For a constant c in a module sealed by an interface (M:T and
    not M<:T), [Global.lookup_constant] may return a [constant_body]
    without body. We fix this by looking in the implementation
    of the module *)

let modcache = ref (ModPath.Map.empty : structure_body ModPath.Map.t)

let rec search_mod_label lab = function
  | [] -> raise Not_found
  | (l, SFBmodule mb) :: _ when Id.equal l lab -> mb
  | _ :: fields -> search_mod_label lab fields

let rec search_cst_label lab = function
  | [] -> raise Not_found
  | (l, SFBconst cb) :: _ when Id.equal l lab -> cb
  | _ :: fields -> search_cst_label lab fields

let rec search_mind_label lab = function
  | [] -> raise Not_found
  | (l, SFBmind mind) :: _ when Id.equal l lab -> mind
  | _ :: fields -> search_mind_label lab fields

(* TODO: using [empty_delta_resolver] below is probably slightly incorrect. But:
    a) I don't see currently what should be used instead
    b) this shouldn't be critical for Print Assumption. At worse some
       constants will have a canonical name which is non-canonical,
       leading to failures in [Global.lookup_constant], but our own
       [lookup_constant] should work.
*)

let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid,_,e) ->
    let open Mod_subst in
    match args with
    | [] -> assert false (* we should only encounter applied functors *)
    | mpa :: args ->
      let subs = join (map_mbid mbid mpa (empty_delta_resolver mpa) (*TODO*)) subs in
      fields_of_functor f subs mp0 args e

let rec lookup_module_in_impl mp =
    match mp with
    | MPfile _ -> Global.lookup_module mp
    | MPbound _ -> Global.lookup_module mp
    | MPdot (mp',lab') ->
      match memoize_fields_of_mp mp' with
      | fields ->
        search_mod_label lab' fields
      | exception Not_found -> Global.lookup_module mp

and memoize_fields_of_mp mp =
  try ModPath.Map.find mp !modcache
  with Not_found ->
    let l = fields_of_mp mp in
    modcache := ModPath.Map.add mp l !modcache;
    l

and fields_of_mp mp =
  let open Mod_subst in
  let mb = lookup_module_in_impl mp in
  let fields,inner_mp,subs = fields_of_mb empty_subst mp mb [] in
  let delta_mb = mod_delta mb in
  let subs =
    (* XXX this code makes little sense, adding a delta_mb to subs if the root
       does not coincide with mp used to be equivalent to a no-op and now fails
       with an assertion failure. More likely than not, this means that we have
       no idea about what we are doing. *)
    if ModPath.equal inner_mp mp then subs
    else if has_root_delta_resolver mp delta_mb then
      add_mp inner_mp mp (of_body_delta_resolver delta_mb) subs
    else
      add_mp inner_mp mp (empty_delta_resolver mp) subs
  in
  Modops.subst_structure subs mp fields

and fields_of_mb subs mp mb args = match Mod_declarations.mod_expr mb with
  | Algebraic expr -> fields_of_expression subs mp args (mod_type mb) expr
  | Struct (_, sign) ->
    let sign = Modops.annotate_struct_body sign (mod_type mb) in
    fields_of_signature subs mp args sign
  | Abstract|FullStruct -> fields_of_signature subs mp args (mod_type mb)

(** The Abstract case above corresponds to [Declare Module] *)

and fields_of_signature x =
  fields_of_functor
    (fun subs mp0 args struc ->
      assert (List.is_empty args);
      (struc, mp0, subs)) x

and fields_of_expr subs mp0 args = function
  | MEident mp ->
    let mp = Mod_subst.subst_mp subs mp in
    let mb = lookup_module_in_impl mp in
    fields_of_mb subs mp mb args
  | MEapply (me1,mp2) -> fields_of_expr subs mp0 (mp2::args) me1
  | MEwith _ -> assert false (* no 'with' in [mod_expr] *)

and fields_of_expression subs mp args mty me =
  let me = Modops.annotate_module_expression me mty in
  fields_of_functor fields_of_expr subs mp args me

let lookup_constant_in_impl cst fallback =
  try
    let mp,lab = KerName.repr (Constant.canonical cst) in
    let fields = memoize_fields_of_mp mp in
    (* A module found this way is necessarily closed, in particular
       our constant cannot be in an opened section : *)
    search_cst_label lab fields
  with Not_found ->
    (* Either:
       - The module part of the constant isn't registered yet :
         we're still in it, so the [constant_body] found earlier
         (if any) was a true axiom.
       - The label has not been found in the structure. This is an error *)
    match fallback with
      | Some cb -> cb
      | None ->
        CErrors.anomaly
          Pp.(str "Print Assumption: unknown constant "
            ++ Constant.print cst ++ str ".")

let lookup_constant cst =
  let env = Global.env() in
  if not (Environ.mem_constant cst env)
  then lookup_constant_in_impl cst None
  else
    let cb = Environ.lookup_constant cst env in
    if Declareops.constant_has_body cb then cb
    else lookup_constant_in_impl cst (Some cb)

let lookup_mind_in_impl mind =
  try
    let mp,lab = KerName.repr (MutInd.canonical mind) in
    let fields = memoize_fields_of_mp mp in
      search_mind_label lab fields
  with Not_found ->
    CErrors.anomaly
      Pp.(str "Print Assumption: unknown inductive "
        ++ MutInd.print mind ++ str ".")

let lookup_mind mind =
  let env = Global.env() in
  if Environ.mem_mind mind env then Environ.lookup_mind mind env
  else lookup_mind_in_impl mind

(** Graph traversal of an object, collecting on the way the dependencies of
    traversed objects *)

let fold_with_full_binders g f n acc c =
  let open Context.Rel.Declaration in
  let open Constr in
  match kind c with
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _  | Int _ | Float _ | String _ -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_,_,c) -> f n acc c
  | Evar _ -> assert false
  | Case (ci, u, pms, p, iv, c, bl) ->
    let mib = lookup_mind (fst ci.ci_ind) in
    let (ci, (p,_), iv, c, bl) = Inductive.expand_case_specif mib (ci, u, pms, p, iv, c, bl) in
    Array.fold_left (f n) (f n (fold_invert (f n) (f n acc p) iv) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | Array(_u,t,def,ty) -> f n (f n (Array.fold_left (f n) acc t) def) ty

(** Reuse of traversals across queries.

    A query walks the body and type of every object it reaches. A file that
    runs many queries in one environment (one per lemma, say) walks the same
    objects again and again, so the walk of an object is recorded and later
    queries replay it.

    Soundness invariant: for every object [o] and environment [E], the entry
    for [o] under [E] is the pair of the [data] value the walk gives [o] and
    the edge set of [o]:
    - for an object with a body, its direct references (its value's set, the
      very set [data] holds);
    - for a constant without a body (axiom, parameter, primitive, symbol,
      [Admitted] lemma), the references in its type, which the walk visits
      but does not keep: the entry stores no set and a replay collects them
      again ([fold_refs_of_type]) from the type that [lookup_constant] finds,
      as the walk does;
    - for a member of a mutual block, the block's direct references plus
      every inductive and constructor of the block.
    An object is never recorded when its walk, including every walk nested in
    it, records an empty-match context in [ax2ty] or meets an opaque body that
    cannot be forced. An entry cannot reproduce the first: it stores no
    [ax2ty], and the empty-match branch marks the axiom visited without
    walking its type, so what the walk adds depends on the order the query
    visits objects in. The second reads the opaque table
    ([Library.access_opaque_table]), state outside the key below; no input is
    known where caching such a walk would change the output, so excluding it
    is a precaution that only costs reuse. A member of a mutual block is
    recorded only together with its whole block. An object is also recorded
    only once each of its edges has an entry, and only while no entry has its
    user name ([user_name_unrecorded]). Entries are never replaced, so every
    edge of every entry keeps an entry until the entries are cleared, and a
    replay can miss only at the object it starts from.

    Replaying [o] writes [o]'s value into the query's [data], then replays
    each edge, stopping at objects already in [data] as the walk does. A
    replay either completes, adding exactly the keys and values the walk of
    [o] adds from the same [data] (the closure of [o] through edges, avoiding
    what [data] holds, whatever the query visited first), or reaches an
    object without an entry and is abandoned, keeping nothing, and [o] is
    walked. A recorded object's walk never touches [ax2ty]. So every query's
    final [data] and [ax2ty] equal those of the walk without reuse, by
    induction over the traversal order, and so does the output of
    {!assumptions}, a fold over them.

    Entries hold for one global environment, compared by physical equality
    of [Global.env ()], and one opaque-proof accessor: the walk reads nothing
    else, and every declaration, [Require], section or module command that
    changes what it reads gives a new environment. Any difference clears
    every entry.

    The entries are also cleared, at the start of a query, when they weigh
    more than [memo_factor] times the heaviest query so far in the
    environment. An entry weighs one plus the size of the set it keeps: none
    for a constant without a body, and a block's set, which all its members
    share, counts once. A query weighs the entries it records plus the
    objects it replays and the sets they push, counted the same way: about
    the size of the [data] it builds.

    What the entries keep is about as much as [data] keeps for the same
    objects: the set of an object with a body is the very set [data] holds
    for it, shared, not copied; a constant without a body keeps nothing,
    where [data] keeps [None]; a block keeps one set for all its members,
    its references plus its members, one more set than [data] holds. So the
    entries a query records weigh at most about twice the [data] it builds,
    whatever the objects are: many constants without a body whose types name
    many objects cost no more than [data] does, where a set per constant
    would have multiplied that. A replay keeps the objects it still has to
    visit in a list, and queues each reference of the types it collects once
    ([queued] in [replay_into]): two references are one element only when
    their user names and their canonical names both agree, as [data] and
    the entries are keyed by user name and [find_entry] also requires the
    canonical name to match, so that list holds
    each object at most once for those references and its length is bounded
    by the objects the replay reaches. When a query starts, the entries weigh
    at most [memo_factor] times the heaviest earlier query, and during the
    query they grow by at most its own weight. Clearing is always sound: it
    only costs reuse. *)

(* Reports each completed replay and each clearing of the entries by the
   weight bound. *)
let debug_cache = CDebug.create ~name:"assumptions-cache" ()

(** The edges of an entry: the objects its walk reaches directly. *)
type memo_edges =
  | Direct of { refs : GlobRef.Set.t; size : int }
      (** a set of references and its cardinal *)
  | Type_of of Constant.t
      (** the references in the type of a constant without a body, collected
          from the type when needed: nothing is stored *)

let edges_size = function
  | Direct { size; _ } -> size
  | Type_of _ -> 0

type memo_entry = {
  memo_obj : GlobRef.t;
  memo_value : GlobRef.Set.t option;
  memo_edges : memo_edges;
}

let memo_key : (Environ.env * Global.indirect_accessor) option ref = ref None

let memo_factor = 2

(** Folds [f] over the references in a type, in the order [traverse] meets
    them: it must collect exactly the objects [traverse] adds to the set of
    references of a type (the [Var], [Const], [Ind] and [Construct] arms of
    [traverse], and the sub-terms [fold_with_full_binders] gives it), for a
    replay of a constant without a body to reach what its walk reached. A
    walk that meets the empty-match arm of [traverse] is never recorded. *)
let rec fold_refs_of_type f acc t =
  let open GlobRef in
  match Constr.kind t with
  | Constr.Var id -> f (VarRef id) acc
  | Constr.Const (kn, _) -> f (ConstRef kn) acc
  | Constr.Ind (ind, _) -> f (IndRef ind) acc
  | Constr.Construct (cst, _) -> f (ConstructRef cst) acc
  | _ -> fold_with_full_binders (fun _ () -> ()) (fun () acc t -> fold_refs_of_type f acc t) () acc t

(** The entries and their weight (see the invariant), in one immutable value
    that is assigned once per update: an interrupted update leaves the entries
    and the weight as they were. [verified] is a table, not part of that
    atomicity: it holds the types of constants without a body whose
    references all have an entry, one key being what {!WalkedTerm.Tbl} says
    (the same references in the same structure). Entries are never replaced,
    so that stays true until the value is replaced by a fresh one
    ([fresh_memo]), which leaves the table of the old value behind. A type is
    entered once, however many equal copies there are, so the table does not
    grow with the copies a sealed functor makes anew in each query. *)
type memo = {
  entries : memo_entry GlobRef.Map.t;
  weight : int;
  verified : unit WalkedTerm.Tbl.t;
}

let fresh_memo () = { entries = GlobRef.Map.empty; weight = 0; verified = WalkedTerm.Tbl.create 16 }

let memo = ref (fresh_memo ())

(** The weight of the heaviest query in the environment before the current
    one, and of the current query. They only decide when the entries are
    cleared, so an interrupted update that leaves them stale costs reuse or
    memory, never output. *)
let memo_heaviest = ref 0
let query_weight = ref 0

(** Counts the traversal steps an entry cannot reproduce: an empty-match
    context recorded in [ax2ty], and an opaque body that cannot be forced (see
    the invariant above for why). A walk during which it changes is not
    recorded. *)
let unreplayable_steps = ref 0

(** [!unreplayable_steps] at the start of each [walk_object] and each
    [walk_inductive] in progress, innermost first. They live here rather
    than in a local of those functions: a local that is live across the
    recursive traversal takes a slot in the frame, and each object on the
    walk path holds one such frame, so stack use per level would grow. *)
let object_marks = ref ([] : int list)
let inductive_marks = ref ([] : int list)

let sync_memo access =
  let env = Global.env () in
  match !memo_key with
  | Some (env', access') when env' == env && access' == access ->
    memo_heaviest := max !memo_heaviest !query_weight;
    query_weight := 0;
    if !memo.weight > memo_factor * !memo_heaviest then begin
      memo := fresh_memo ();
      debug_cache Pp.(fun () -> str "cleared")
    end
  | _ ->
    memo := fresh_memo ();
    memo_heaviest := 0;
    query_weight := 0;
    memo_key := Some (env, access)

(* [Map] compares user names only: the entry is [obj]'s when the
   canonical names agree too, since the value the walk gives a constant with
   no body in the environment is looked up through its canonical name
   ([lookup_constant_in_impl]). Module aliases, functor applications and
   [Include] do reach objects whose canonical names differ under one user
   name, but no input is known where an entry under the other canonical name
   would change the output, so the check is a precaution. It only costs
   reuse: the other canonical name is walked, and is not recorded
   ([user_name_unrecorded]). *)
let find_entry obj =
  match GlobRef.Map.find_opt obj !memo.entries with
  | Some e when GlobRef.CanOrd.equal e.memo_obj obj -> Some e
  | _ -> None

let has_entry obj = Option.has_some (find_entry obj)

(* An object whose user name already has an entry, under another canonical
   name, is not recorded: entries are never replaced until the environment
   changes (see the invariant). Replacing the entry would leave the entries
   that reach it without an entry for that edge; each replay through them
   would go down to it and miss, and the walk that follows would replay every
   level below again, quadratic in the depth of a chain. Unlike [has_entry],
   this compares user names only. *)
let user_name_unrecorded obj = not (GlobRef.Map.mem obj !memo.entries)

(* The entry for [obj] recording [edges], the set the walk found: it keeps the
   set itself, unless [obj] is a constant without a body, where [data] keeps
   nothing and the entry keeps the constant instead (see the invariant). *)
let[@inline never] make_entry value edges obj =
  let memo_edges = match value, obj with
    | None, GlobRef.ConstRef kn -> Type_of kn
    | _ -> Direct { refs = edges; size = GlobRef.Set.cardinal edges }
  in
  { memo_obj = obj; memo_value = value; memo_edges }

(* Inlined into [walk_object]: the call would add a frame at the bottom of the
   deepest walk, under [Map.add], and so shorten the longest chain that
   fits in the stack. *)
let[@inline always] add_entry value edges obj =
  let e = make_entry value edges obj in
  let weight = 1 + edges_size e.memo_edges in
  query_weight := !query_weight + weight;
  let m = !memo in
  memo := { m with entries = GlobRef.Map.add obj e m.entries; weight = m.weight + weight }

(* The members are added to a new map, which is assigned once, with the
   weight: a block recorded in part (a [Timeout] or an interrupt during the
   loop) would keep its other members from ever being recorded
   ([user_name_unrecorded]), and every replay that reaches one of them would
   miss deep in the graph. *)
let record_block mind mib contents =
  let members = Array.fold_left_i (fun n members oib ->
      let ind = (mind, n) in
      Array.fold_left_i (fun k members _ ->
          GlobRef.Set.add (GlobRef.ConstructRef (ind, k+1)) members)
        (GlobRef.Set.add (GlobRef.IndRef ind) members) oib.mind_consnames)
      GlobRef.Set.empty mib.mind_packets
  in
  let cached r = GlobRef.Set.mem r members || has_entry r in
  if GlobRef.Set.for_all user_name_unrecorded members
     && GlobRef.Set.for_all cached contents then
    let edges = GlobRef.Set.union contents members in
    let size = GlobRef.Set.cardinal edges in
    let weight = GlobRef.Set.cardinal members + size in
    query_weight := !query_weight + weight;
    let m = !memo in
    let memo_edges = Direct { refs = edges; size } in
    let entries = GlobRef.Set.fold (fun obj entries ->
        let e = { memo_obj = obj; memo_value = Some contents; memo_edges } in
        GlobRef.Map.add obj e entries) members m.entries
    in
    memo := { m with entries; weight = m.weight + weight }

exception Miss

(** The weight of the replay in progress, counted as in [record_block]. A
    global rather than an argument of [loop], so that the replay at the bottom
    of the deepest walk takes no more stack. *)
let replay_weight = ref 0

(** Sets of references in which two references are one element only when both
    their user names and their canonical names agree: [data] and the walk's
    set of references are keyed by user name, so a reference with the same
    canonical name and another user name (a module alias, [Include], a
    functor application) must be queued too, and one with the same user name
    and another canonical name must still reach [find_entry] and miss. *)
module Queued = Stdlib.Set.Make (struct
    type t = GlobRef.t
    let compare a b =
      let c = GlobRef.UserOrd.compare a b in
      if c <> 0 then c else GlobRef.CanOrd.compare a b
  end)

(* [data0] is the query's [data] before the replay. An object in it is
   skipped, as the walk skips it. Every other object reached needs an entry
   for that very object, canonical name included, even when this replay
   already added an object with the same user name: so the objects a
   completed replay reaches outside [data0] have one canonical name per user
   name, and the order in which it reaches them cannot matter. The objects
   still to visit are kept in a list rather than on the stack: edges are
   followed in hash order, so a recursive replay could go much deeper than
   the walk of the same objects.

   The members of a mutual block share one edge set ([record_block]), which
   holds every member. It is pushed once per replay: pushing it again would
   only revisit objects already visited, and for a block of n members it
   would push n^2 objects. [pushed] holds the blocks whose edges were pushed.
   All the entries of a block come from one [record_block] and are never
   replaced, so every member of a block that a replay reaches has that same
   edge set. *)
let replay_into data0 obj data =
  (* The weight counts the references of a [Direct] set, but not those of the
     type of a constant without a body, which are collected here: [queued]
     holds the references that were queued from types, and one is not queued
     again, so the list holds at most the distinct references of the types
     reached, besides the counted sets. *)
  let queued = ref Queued.empty in
  let push r todo =
    let q = Queued.add r !queued in
    if q == !queued then todo else (queued := q; r :: todo)
  in
  let rec loop pushed data = function
    | [] -> data
    | obj :: todo ->
      if GlobRef.Map.mem obj data0 then loop pushed data todo
      else match find_entry obj with
      | None -> raise Miss
      | Some e ->
        if GlobRef.Map.mem obj data then loop pushed data todo
        else
          let () = incr replay_weight in
          let data = GlobRef.Map.add obj e.memo_value data in
          let block = match obj with
            | GlobRef.IndRef (mind, _) | GlobRef.ConstructRef ((mind, _), _) -> Some mind
            | GlobRef.VarRef _ | GlobRef.ConstRef _ -> None
          in
          match block with
          | Some mind when Mindset.mem mind pushed -> loop pushed data todo
          | _ ->
            let pushed = match block with
              | Some mind -> Mindset.add mind pushed
              | None -> pushed
            in
            match e.memo_edges with
            | Direct { refs; size } ->
              let () = replay_weight := !replay_weight + size in
              loop pushed data (GlobRef.Set.fold (fun r todo -> r :: todo) refs todo)
            | Type_of kn ->
              let typ = (lookup_constant kn).Declarations.const_type in
              loop pushed data (fold_refs_of_type push todo typ)
  in
  loop Mindset.empty data [obj]

(** [Some data'] when every object the replay reaches outside [data] has an
    entry, where [data'] is [data] plus the closure of [obj], stopping at
    objects already in [data], with the values the walk would add; [None]
    otherwise. *)
let replay obj data =
  let () = replay_weight := 0 in
  match replay_into data obj data with
  | data ->
    query_weight := !query_weight + !replay_weight;
    debug_cache Pp.(fun () -> str "replayed" ++ spc () ++ GlobRef.print obj);
    Some data
  | exception Miss -> None

let warn_unreachable_opaque_body =
  CWarnings.create ~name:"unreachable-opaque-body" ~category:CWarnings.CoreCategories.vernacular
    Pp.(fun kn -> str "Cannot access the opaque body of "
                  ++ Nametab.pr_global_env Id.Set.empty (GlobRef.ConstRef kn)
                  ++ str ", its assumptions are unknown.")

(* Answers [None] both for a constant which has no body and for an opaque
   constant whose body could not be read, for instance a delayed proof
   missing in vok mode. The two are told apart by [Declareops.is_opaque] in
   [assumptions] below. *)
let get_constant_body access kn =
  let cb = lookup_constant kn in
  match cb.const_body with
  | Undef _ | Primitive _ | Symbol _ -> None
  | Def c -> Some c
  | OpaqueDef o ->
    match Global.force_proof access o with
    | c, _ -> Some c
    | exception e when CErrors.noncritical e ->
      warn_unreachable_opaque_body kn;
      incr unreplayable_steps;
      None

(* The types of the constants without a body whose walk is in progress,
   innermost first, kept on the heap like [inductive_marks]: the walk would
   otherwise keep its type live across the walk of that type, which adds a slot
   to the frame of [walk_object]. [pop_type] moves the innermost to
   [last_type], where [edges_have_entries] reads it. The environment is not
   consulted again for it. *)
let type_stack = ref ([] : Constr.t list)
let last_type = ref (GlobRef.VarRef (Id.of_string "_"), Constr.mkProp)

let[@inline never] pop_type obj =
  match !type_stack with
  | t :: l -> last_type := (obj, t); type_stack := l
  | [] -> assert false

(* Whether each reference in [edges] of [obj] has an entry. When [obj] is the
   constant without a body whose type was popped last ([last_type], tagged
   with the object itself, compared physically), [edges] are the references of
   that type, since a walk that reaches this check met no empty match. The
   types of many such constants are one key of [WalkedTerm.Tbl] (equal for the
   walk), and the references of a type do not depend on the constant: entries
   are never replaced, so a type whose references all had an entry keeps them
   until the entries are cleared. Such a type is entered in [memo.verified],
   keyed by the comparison of [WalkedTerm.Tbl], which does not depend on how
   many types there are, and the check is skipped for the constants that share
   it. No environment lookup is
   made here, and a constant with a body is never tagged. The object is passed
   rather than the value, so that the walk's frame is as it would be without
   this function; the three functions are small and not inlined for the same
   reason (a single larger function adds a slot to the frame of
   [walk_object]). *)
let[@inline never] type_verified obj =
  let (o, typ) = !last_type in
  o == obj && WalkedTerm.Tbl.mem !memo.verified typ

let[@inline never] note_verified obj =
  let (o, typ) = !last_type in
  if o == obj then WalkedTerm.Tbl.replace !memo.verified typ ()

let[@inline never] edges_have_entries obj edges =
  type_verified obj
  || (GlobRef.Set.for_all has_entry edges && (note_verified obj; true))

(* The [Var], [Const], [Ind] and [Construct] arms below and the empty-match
   arm are mirrored by [fold_refs_of_type], which a replay of a constant
   without a body uses in place of this walk of its type: a change to what
   these arms collect must be made there too. *)
let rec traverse access (current:GlobRef.t) ctx accu t =
  let open GlobRef in
  let open Constr in
  match Constr.kind t with
| Var id ->
  let body () = id |> Global.lookup_named |> NamedDecl.get_value in
  traverse_object access accu body (VarRef id)
| Const (kn, _) ->
  let body () = get_constant_body access kn in
  traverse_object access accu body (ConstRef kn)
| Ind ((mind, _) as ind, _) ->
  traverse_inductive access accu mind (IndRef ind)
| Construct (((mind, _), _) as cst, _) ->
  traverse_inductive access accu mind (ConstructRef cst)
| Meta _ | Evar _ -> assert false
| Case (_, _, _, (([|_|], oty),_), _, c, [||]) when Vars.noccurn 1 oty ->
    (* non dependent match on an inductive with no constructors *)
    begin match Constr.kind c with
    | Const (kn, _) when not (Declareops.constant_has_body (lookup_constant kn)) ->
      let () = incr unreplayable_steps in
      let (curr, data, ax2ty) = accu in
      let obj = ConstRef kn in
      let already_in = GlobRef.Map.mem obj data in
      let data = if not already_in then GlobRef.Map.add obj None data else data in
      let ty = (current, ctx, Vars.subst1 mkProp oty) in
      let ax2ty =
        try let l = GlobRef.Map.find obj ax2ty in GlobRef.Map.add obj (ty::l) ax2ty
        with Not_found -> GlobRef.Map.add obj [ty] ax2ty in
      (GlobRef.Set.add obj curr, data, ax2ty)
    | _ ->
        fold_with_full_binders
          Context.Rel.add (traverse access current) ctx accu t
    end
| _ -> fold_with_full_binders
          Context.Rel.add (traverse access current) ctx accu t

(* [walk_object] and [walk_inductive] are entered by tail calls, which the
   compiler checks ([@ocaml.tailcall]): a walk holds one frame per object, as
   it would without reuse, and [walk_inductive] keeps its mark in
   [inductive_marks] rather than in that frame. *)
and traverse_object access (curr, data, ax2ty) body obj =
  let curr = GlobRef.Set.add obj curr in
  if GlobRef.Map.mem obj data then (curr, data, ax2ty)
  else match replay obj data with
  | Some data -> (curr, data, ax2ty)
  | None -> (walk_object [@ocaml.tailcall]) access curr data ax2ty body obj

and walk_object access curr data ax2ty body obj =
  let () = object_marks := !unreplayable_steps :: !object_marks in
  let value, edges, data, ax2ty =
    match body () (* Beware: this can be very costly *) with
    | None ->
      (* This is an axiom. Always traverse its type to find dependencies *)
      let data = GlobRef.Map.add obj None data in
      begin match obj with
      | GlobRef.ConstRef kn ->
        let typ = (lookup_constant kn).Declarations.const_type in
        type_stack := typ :: !type_stack;
        let type_refs, data, ax2ty =
          traverse access obj Context.Rel.empty
                   (GlobRef.Set.empty, data, ax2ty) typ in
        pop_type obj;
        None, type_refs, data, ax2ty
      (* VarRef, IndRef and ConstructRef don't need recursive type traversal.
         For VarRef (section variables), the dependencies are already tracked.
         For IndRef and ConstructRef, dependencies are handled by traverse_inductive *)
      | GlobRef.VarRef _ | GlobRef.IndRef _ | GlobRef.ConstructRef _ ->
        None, GlobRef.Set.empty, data, ax2ty end
    | Some body ->
      let contents,data,ax2ty =
        traverse access obj Context.Rel.empty
                 (GlobRef.Set.empty,data,ax2ty) body in
      (* Also traverse the type of globals, which may mention unrelated
         references depending on axioms even if they convert to something else. *)
      let contents,data,ax2ty = match obj with
        | GlobRef.ConstRef kn ->
          let cb = lookup_constant kn in
          let typ = cb.Declarations.const_type in
          traverse access obj Context.Rel.empty
                   (contents,data,ax2ty) typ
        | _ -> (contents,data,ax2ty)
      in
      Some contents, contents, GlobRef.Map.add obj (Some contents) data, ax2ty
  in
  let mark = match !object_marks with
    | mark :: marks -> object_marks := marks; mark
    | [] -> assert false
  in
  let () =
    if Int.equal mark !unreplayable_steps && user_name_unrecorded obj
       && edges_have_entries obj edges
    then add_entry value edges obj
  in
  (curr, data, ax2ty)

(** Collects the references occurring in the declaration of mutual inductive
    definitions. All the constructors and names of a mutual inductive
    definition share exactly the same dependencies. Also, there is no explicit
    dependency between mutually defined inductives and constructors. *)
and traverse_inductive access (curr, data, ax2ty) mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  (* Invariant : I_0 \in data iff I_i \in data iff c_ij \in data
     where I_0, I_1, ... are in the same mutual definition and c_ij
     are all their constructors. *)
  let recursive = GlobRef.Set.mem firstind_ref curr in
  let curr = GlobRef.Set.add obj curr in
  if
    (* recursive call: *) recursive ||
    (* already in: *) GlobRef.Map.mem firstind_ref data
  then (curr, data, ax2ty)
  else match replay obj data with
  | Some data -> (curr, data, ax2ty)
  | None -> (walk_inductive [@ocaml.tailcall]) access curr data ax2ty mind obj

and walk_inductive access curr data ax2ty mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  let () = inductive_marks := !unreplayable_steps :: !inductive_marks in
  (* Take into account potential recursivity of ind in itself *)
  let accu = (GlobRef.Set.add firstind_ref GlobRef.Set.empty, data, ax2ty) in
  let mib = lookup_mind mind in
  (* Collects references of parameters *)
  let param_ctx = mib.mind_params_ctxt in
  let nparam = List.length param_ctx in
  let accu = traverse_context access obj Context.Rel.empty accu param_ctx in
  (* For each inductive, collects references in their arity and in the type
     of constructors*)
  let (contents, data, ax2ty) = Array.fold_left (fun accu oib ->
      let arity_wo_param =
        List.rev (List.skipn nparam (List.rev oib.mind_arity_ctxt))
      in
      let accu =
        traverse_context
          access obj param_ctx accu arity_wo_param
      in
      Array.fold_left (fun accu cst_typ ->
         let param_ctx, cst_typ_wo_param = Term.decompose_prod_n_decls nparam cst_typ in
         traverse access obj param_ctx accu cst_typ_wo_param)
        accu oib.mind_user_lc)
    accu mib.mind_packets
  in
  (* Maps all these dependencies to inductives and constructors*)
  let contents = GlobRef.Set.remove firstind_ref contents in
  let data =
    Array.fold_left_i (fun n data oib ->
    let ind = (mind, n) in
    let data = GlobRef.Map.add (GlobRef.IndRef ind) (Some contents) data in
    Array.fold_left_i (fun k data _ ->
      GlobRef.Map.add (GlobRef.ConstructRef (ind, k+1)) (Some contents) data
    ) data oib.mind_consnames) data mib.mind_packets
  in
  let mark = match !inductive_marks with
    | mark :: marks -> inductive_marks := marks; mark
    | [] -> assert false
  in
  let () = if Int.equal mark !unreplayable_steps then record_block mind mib contents in
  (curr, data, ax2ty)

(** Collects references in a rel_context. *)
and traverse_context access current ctx accu ctxt =
  snd (Context.Rel.fold_outside (fun decl (ctx, accu) ->
    match decl with
     | Context.Rel.Declaration.LocalDef (_,c,t) ->
          let accu = traverse access current ctx (traverse access current ctx accu t) c in
          let ctx = Context.Rel.add decl ctx in
          ctx, accu
     | Context.Rel.Declaration.LocalAssum (_,t) ->
          let accu = traverse access current ctx accu t in
          let ctx = Context.Rel.add decl ctx in
           ctx, accu) ctxt ~init:(ctx, accu))

let traverse access grs =
  let () = modcache := ModPath.Map.empty in
  let () = object_marks := [] in
  let () = inductive_marks := [] in
  let () = type_stack := [] in
  let () = sync_memo access in
  let env = Global.env () in
  List.fold_left (fun accu gr ->
    let t, _ = UnivGen.fresh_global_instance env gr in
    traverse access gr Context.Rel.empty accu t
  ) (GlobRef.Set.empty, GlobRef.Map.empty, GlobRef.Map.empty) grs

(** Hopefully bullet-proof function to recover the type of a constant. It just
    ignores all the universe stuff. There are many issues that can arise when
    considering terms out of any valid environment, so use with caution. *)
let type_of_constant cb = cb.Declarations.const_type

let uses_uip mib =
  Array.exists (fun mip ->
      Option.is_empty mip.mind_squashed
      && mip.mind_relevance == Sorts.Irrelevant
      && Array.length mip.mind_nf_lc = 1
      && List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt)
    mib.mind_packets

let assumptions ?(add_opaque=false) ?(add_transparent=false) access st grs =
  let open Printer in
  (* Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse access grs in
  let open GlobRef in
  let has_impredicative_set = ref false in
  let has_rewrite_rules = ref false in
  let has_type_in_type = ref false in
  let collect_theory_flags (tf : Declarations.typing_flags) =
    if tf.impredicative_set then has_impredicative_set := true;
    if not tf.check_universes then has_type_in_type := true
  in
  let fold obj contents accu = match obj with
  | VarRef id ->
    let decl = Global.lookup_named id in
    if Context.Named.Declaration.is_local_assum decl then
      let t = Context.Named.Declaration.get_type decl in
      ContextObjectMap.add (Variable id) t accu
    else accu
  | ConstRef kn ->
      let cb = lookup_constant kn in
      collect_theory_flags cb.const_typing_flags;
      begin match cb.const_body with
        | Symbol _ -> has_rewrite_rules := true
        | _ -> ()
      end;
      let accu =
        if cb.const_typing_flags.check_guarded then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded obj, l)) Constr.mkProp accu
      in
      let accu =
        if cb.const_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
      let accu =
        if not cb.const_typing_flags.impredicative_set then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (ImpredicativeSet obj, l)) Constr.mkProp accu
      in
    if not (Option.has_some contents) then
      let t = type_of_constant cb in
      (* An opaque constant reaches this point only when its body could not
         be read. It is not an axiom, we just do not know what it assumes. *)
      if Declareops.is_opaque cb then
        ContextObjectMap.add (UnreachableOpaque kn) t accu
      else
        let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
        ContextObjectMap.add (Axiom (Constant kn,l)) t accu
    else if add_opaque && (Declareops.is_opaque cb || not (Structures.PrimitiveProjections.is_transparent_constant st kn)) then
      let t = type_of_constant cb in
      ContextObjectMap.add (Opaque kn) t accu
    else if add_transparent then
      let t = type_of_constant cb in
      ContextObjectMap.add (Transparent kn) t accu
    else
      accu
  | IndRef (m,_) | ConstructRef ((m,_),_) ->
      let mind = lookup_mind m in
      collect_theory_flags mind.mind_typing_flags;
      let accu =
        if mind.mind_typing_flags.check_positive then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Positive m, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_guarded then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded obj, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
      let accu =
        if not (uses_uip mind) then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (UIP m, l)) Constr.mkProp accu
      in
      let accu =
        if not (Array.exists (fun mip -> mip.mind_relies_on_indices_not_mattering) mind.mind_packets) then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (IndicesNotMattering m, l)) Constr.mkProp accu
      in
      let accu =
        if not mind.mind_typing_flags.impredicative_set then accu
        else
          let l = try GlobRef.Map.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (ImpredicativeSet obj, l)) Constr.mkProp accu
      in
      accu
  in
  let map = GlobRef.Map.fold fold graph ContextObjectMap.empty in
  let theory = {
    has_impredicative_set = !has_impredicative_set;
    has_rewrite_rules = !has_rewrite_rules;
    has_type_in_type = !has_type_in_type;
  } in
  (theory, map)
