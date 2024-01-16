(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Nameops
open Constr
open Vars
open Environ

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type econstr = constr
type etypes = types
type esorts = Sorts.t

(** Generic filters *)
module Filter :
sig
  type t
  val equal : t -> t -> bool
  val identity : t
  val filter_list : t -> 'a list -> 'a list
  val filter_array : t -> 'a array -> 'a array
  val filter_slist : t -> 'a SList.t -> 'a SList.t
  val extend : int -> t -> t
  val compose : t -> t -> t
  val apply_subfilter : t -> bool list -> t
  val restrict_upon : t -> int -> (int -> bool) -> t option
  val map_along : (bool -> 'a -> bool) -> t -> 'a list -> t
  val make : bool list -> t
  val repr :  t -> bool list option

  type compact =
  | Empty
  | TCons of int * compact
  | FCons of int * compact

  val unfold : t -> compact option

end =
struct

  type compact =
  | Empty
  | TCons of int * compact
  | FCons of int * compact

  let rec compact l = match l with
  | [] -> Empty
  | true :: l ->
    begin match compact l with
    | TCons (n, c) -> TCons (n + 1, c)
    | (Empty | FCons _ as c) -> TCons (1, c)
    end
  | false :: l ->
    begin match compact l with
    | FCons (n, c) -> FCons (n + 1, c)
    | (Empty | TCons _ as c) -> FCons (1, c)
    end

  type t = {
    data : bool list option;
    compact : compact;
  }
  (** We guarantee through the interface that if a filter is [Some _] then it
      contains at least one [false] somewhere. *)

  let identity = { data = None; compact = Empty }

  let rec equal l1 l2 = match l1, l2 with
  | [], [] -> true
  | h1 :: l1, h2 :: l2 ->
    (if h1 then h2 else not h2) && equal l1 l2
  | _ -> false

  let equal l1 l2 = match l1.data, l2.data with
  | None, None -> true
  | Some _, None | None, Some _ -> false
  | Some l1, Some l2 -> equal l1 l2

  let rec is_identity = function
  | [] -> true
  | true :: l -> is_identity l
  | false :: _ -> false

  let normalize f =
    if is_identity f then identity
    else { data = Some f; compact = compact f }

  let filter_list f l = match f.data with
  | None -> l
  | Some f -> CList.filter_with f l

  let filter_array f v = match f.data with
  | None -> v
  | Some f -> CArray.filter_with f v

  let filter_slist f l = match f.data with
  | None -> l
  | Some f ->
    let rec filter f l = match f, SList.view l with
    | [], None -> SList.empty
    | true :: f, Some (o, l) -> SList.cons_opt o (filter f l)
    | false :: f, Some (_, l) -> filter f l
    | _ :: _, None | [], Some _ -> invalid_arg "List.filter_with"
    in
    filter f l

  let rec extend n l =
    if n = 0 then l
    else extend (pred n) (true :: l)

  let extend n f =  match f.data with
  | None -> identity
  | Some f0 ->
    let compact = match f.compact with
    | Empty -> assert false
    | TCons (m, c) -> TCons (n + m, c)
    | c -> TCons (n, c)
    in
    { data = Some (extend n f0); compact }

  let compose f1 f2 = match f1.data with
  | None -> f2
  | Some f1 ->
    match f2.data with
    | None -> identity
    | Some f2 -> normalize (CList.filter_with f1 f2)

  let apply_subfilter_array filter subfilter =
    (* In both cases we statically know that the argument will contain at
       least one [false] *)
    match filter.data with
    | None ->
      let l = Array.to_list subfilter in
      { data = Some l; compact = compact l }
    | Some f ->
    let len = Array.length subfilter in
    let fold b (i, ans) =
      if b then
        let () = assert (0 <= i) in
        (pred i, Array.unsafe_get subfilter i :: ans)
      else
        (i, false :: ans)
    in
    let data = snd (List.fold_right fold f (pred len, [])) in
    { data = Some data; compact = compact data }

  let apply_subfilter filter subfilter =
    apply_subfilter_array filter (Array.of_list subfilter)

  let restrict_upon f len p =
    let newfilter = Array.init len p in
    if Array.for_all (fun id -> id) newfilter then None
    else
      Some (apply_subfilter_array f newfilter)

  let map_along f flt l =
    let ans = match flt.data with
    | None -> List.map (fun x -> f true x) l
    | Some flt -> List.map2 f flt l
    in
    normalize ans

  let make l = normalize l

  let repr f = f.data

  let unfold f = match f.data with
  | None -> None
  | Some _ -> Some f.compact

end

module Abstraction = struct

  type abstraction =
    | Abstract
    | Imitate

  type t = abstraction list

  let identity = []

  let abstract_last l = Abstract :: l
end

(* The kinds of existential variables are now defined in [Evar_kinds] *)

(* The type of mappings for existential variables *)

module Store = Store.Make ()

let string_of_existential evk = "?X" ^ string_of_int (Evar.repr evk)

type defined = [ `defined ]
type undefined = [ `undefined ]

type _ evar_body =
  | Evar_empty : undefined evar_body
  | Evar_defined : econstr -> defined evar_body

type (_, 'a) when_undefined =
| Defined : (defined, 'a) when_undefined
| Undefined : 'a -> (undefined, 'a) when_undefined

type 'a evar_info = {
  evar_concl : ('a, constr) when_undefined;
  evar_hyps : named_context_val;
  evar_body : 'a evar_body;
  evar_filter : Filter.t;
  evar_abstract_arguments : ('a, Abstraction.t) when_undefined;
  evar_source : Evar_kinds.t Loc.located;
  evar_candidates : ('a, constr list option) when_undefined; (* if not None, list of allowed instances *)
  evar_relevance: Sorts.relevance;
}

type any_evar_info = EvarInfo : 'a evar_info -> any_evar_info

let instance_mismatch () =
  anomaly (Pp.str "Signature and its instance do not match.")

let evar_concl evi = match evi.evar_concl with
| Undefined c -> c

let evar_filter evi = evi.evar_filter

let evar_body evi = evi.evar_body

let evar_context evi = named_context_of_val evi.evar_hyps

let evar_filtered_context evi =
  Filter.filter_list (evar_filter evi) (evar_context evi)

let evar_candidates evi = match evi.evar_candidates with
| Undefined c -> c

let evar_abstract_arguments evi = match evi.evar_abstract_arguments with
| Undefined c -> c

let evar_relevance evi = evi.evar_relevance

let evar_hyps evi = evi.evar_hyps

let evar_filtered_hyps evi = match Filter.repr (evar_filter evi) with
| None -> evar_hyps evi
| Some filter ->
  let rec make_hyps filter ctxt = match filter, ctxt with
  | [], [] -> empty_named_context_val
  | false :: filter, _ :: ctxt -> make_hyps filter ctxt
  | true :: filter, decl :: ctxt ->
    let hyps = make_hyps filter ctxt in
    push_named_context_val decl hyps
  | _ -> instance_mismatch ()
  in
  make_hyps filter (evar_context evi)

let evar_env env evi =
  Environ.reset_with_named_context evi.evar_hyps env

let evar_filtered_env env evi = Environ.reset_with_named_context (evar_filtered_hyps evi) env

let evar_identity_subst evi =
  let len = match Filter.repr evi.evar_filter with
  | None -> List.length @@ Environ.named_context_of_val evi.evar_hyps
  | Some f -> List.count (fun b -> b) f
  in
  SList.defaultn len SList.empty

let map_evar_body (type a) f : a evar_body -> a evar_body = function
  | Evar_empty -> Evar_empty
  | Evar_defined d -> Evar_defined (f d)

let map_when_undefined (type a b) f : (a, b) when_undefined -> (a, b) when_undefined = function
| Defined -> Defined
| Undefined x -> Undefined (f x)

let map_evar_info f evi =
  {evi with
    evar_body = map_evar_body f evi.evar_body;
    evar_hyps = map_named_val (fun d -> NamedDecl.map_constr f d) evi.evar_hyps;
    evar_concl = map_when_undefined f evi.evar_concl;
    evar_candidates = map_when_undefined (fun c -> Option.map (List.map f) c) evi.evar_candidates }

(* This exception is raised by *.existential_value *)
exception NotInstantiatedEvar

(* Note: let-in contributes to the instance *)
let evar_instance_array empty push info args =
  let rec instrec pos filter args = match filter with
  | Filter.Empty -> if SList.is_empty args then empty else instance_mismatch ()
  | Filter.TCons (n, filter) -> instpush pos n filter args
  | Filter.FCons (n, filter) -> instrec (pos + n) filter args
  and instpush pos n filter args =
    if n <= 0 then instrec pos filter args
    else match args with
    | SList.Nil -> assert false
    | SList.Cons (c, args) ->
      let d = Range.get info.evar_hyps.env_named_idx pos in
      let id = NamedDecl.get_id d in
      push id c (instpush (pos + 1) (n - 1) filter args)
    | SList.Default (m, args) ->
      if m <= n then instpush (pos + m) (n - m) filter args
      else instrec (pos + n) filter (SList.defaultn (m - n) args)
  in
  match Filter.unfold (evar_filter info) with
  | None ->
    let rec instance pos args = match args with
    | SList.Nil -> empty
    | SList.Cons (c, args) ->
      let d = Range.get info.evar_hyps.env_named_idx pos in
      let id = NamedDecl.get_id d in
      push id c (instance (pos + 1) args)
    | SList.Default (n, args) -> instance (pos + n) args
    in
    instance 0 args
  | Some filter ->
    instrec 0 filter args

let make_evar_instance_array info args =
  if SList.is_default args then []
  else
    let push id c l = if isVarId id c then l else (id, c) :: l in
    evar_instance_array [] push info args

type 'a in_evar_universe_context = 'a * UState.t

(*******************************************************************)
(* Metamaps *)

(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Int.Set.t }

(* Collects all metavars appearing in a constr *)
let metavars_of c =
  let rec collrec acc c =
    match kind c with
      | Meta mv -> Int.Set.add mv acc
      | _         -> Constr.fold collrec acc c
  in
  collrec Int.Set.empty c

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }

let map_fl f cfl = { cfl with rebus=f cfl.rebus }

(* Status of an instance found by unification wrt to the meta it solves:
  - a supertype of the meta (e.g. the solution to ?X <= T is a supertype of ?X)
  - a subtype of the meta (e.g. the solution to T <= ?X is a supertype of ?X)
  - a term that can be eta-expanded n times while still being a solution
    (e.g. the solution [P] to [?X u v = P u v] can be eta-expanded twice)
*)

type instance_constraint = IsSuperType | IsSubType | Conv

let eq_instance_constraint c1 c2 = c1 == c2

(* Status of the unification of the type of an instance against the type of
     the meta it instantiates:
   - CoerceToType means that the unification of types has not been done
     and that a coercion can still be inserted: the meta should not be
     substituted freely (this happens for instance given via the
     "with" binding clause).
   - TypeProcessed means that the information obtainable from the
     unification of types has been extracted.
   - TypeNotProcessed means that the unification of types has not been
     done but it is known that no coercion may be inserted: the meta
     can be substituted freely.
*)

type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

(* Status of an instance together with the status of its type unification *)

type instance_status = instance_constraint * instance_typing_status

(* Clausal environments *)

type clbinding =
  | Cltyp of Name.t * constr freelisted
  | Clval of Name.t * (constr freelisted * instance_status) * constr freelisted

let map_clb f = function
  | Cltyp (na,cfl) -> Cltyp (na,map_fl f cfl)
  | Clval (na,(cfl1,pb),cfl2) -> Clval (na,(map_fl f cfl1,pb),map_fl f cfl2)

(* name of defined is erased (but it is pretty-printed) *)
let clb_name = function
    Cltyp(na,_) -> (na,false)
  | Clval (na,_,_) -> (na,true)

(***********************)

module Metaset = Int.Set

module Metamap = Int.Map

(*************************)
(* Unification state *)

type conv_pb = Conversion.conv_pb
type evar_constraint = conv_pb * Environ.env * constr * constr

module EvMap = Evar.Map

module EvNames :
sig

type t

val empty : t
val add_name_undefined : Id.t option -> Evar.t -> 'a evar_info -> t -> t
val remove_name_defined : Evar.t -> t -> t
val rename : Evar.t -> Id.t -> t -> t
val reassign_name_defined : Evar.t -> Evar.t -> t -> t
val ident : Evar.t -> t -> Id.t option
val key : Id.t -> t -> Evar.t
val state : t -> Fresh.t

end =
struct

type t = {
  fwd_map : Id.t EvMap.t;
  rev_map : Evar.t Id.Map.t;
  fsh_map : Fresh.t;
}

let empty = {
  fwd_map = EvMap.empty;
  rev_map = Id.Map.empty;
  fsh_map = Fresh.empty;
}

let add_name_newly_undefined id evk evi names =
  match id with
  | None -> names
  | Some id ->
    if Id.Map.mem id names.rev_map then
      user_err  (str "Already an existential evar of name " ++ Id.print id);
    { fwd_map = EvMap.add evk id names.fwd_map;
      rev_map = Id.Map.add id evk names.rev_map;
      fsh_map = Fresh.add id names.fsh_map; }

let add_name_undefined naming evk evi evar_names =
  if EvMap.mem evk evar_names.fwd_map then
    evar_names
  else
    add_name_newly_undefined naming evk evi evar_names

let remove_name_defined evk names =
  let id = try Some (EvMap.find evk names.fwd_map) with Not_found -> None in
  match id with
  | None -> names
  | Some id ->
    { fwd_map = EvMap.remove evk names.fwd_map;
      rev_map = Id.Map.remove id names.rev_map;
      fsh_map = Fresh.remove id names.fsh_map }

let rename evk id names =
  let id' = try Some (EvMap.find evk names.fwd_map) with Not_found -> None in
  match id' with
  | None ->
    { fwd_map = EvMap.add evk id names.fwd_map;
      rev_map = Id.Map.add id evk names.rev_map;
      fsh_map = Fresh.add id names.fsh_map }
  | Some id' ->
    if Id.Map.mem id names.rev_map then anomaly (str "Evar name already in use.");
    { fwd_map = EvMap.set evk id names.fwd_map; (* overwrite old name *)
      rev_map = Id.Map.add id evk (Id.Map.remove id' names.rev_map);
      fsh_map = Fresh.add id (Fresh.remove id' names.fsh_map) }

let reassign_name_defined evk evk' names =
  let id = try Some (EvMap.find evk names.fwd_map) with Not_found -> None in
  match id with
  | None -> names (* evk' must not be defined *)
  | Some id ->
    { fwd_map = EvMap.add evk' id (EvMap.remove evk names.fwd_map);
      rev_map = Id.Map.add id evk' (Id.Map.remove id names.rev_map);
      fsh_map = names.fsh_map; }

let ident evk names =
  try Some (EvMap.find evk names.fwd_map) with Not_found -> None

let key id names =
  Id.Map.find id names.rev_map

let state names = names.fsh_map

end

type evar_flags =
  { obligation_evars : Evar.Set.t;
    aliased_evars : Evar.t Evar.Map.t;
    typeclass_evars : Evar.Set.t;
    impossible_case_evars : Evar.Set.t;
  }

type side_effect_role =
| Schema of inductive * string

type side_effects = {
  seff_private : Safe_typing.private_constants;
  seff_roles : side_effect_role Cmap.t;
}

module FutureGoals : sig

  type t

  val comb : t -> Evar.t list

  val principal : t -> Evar.t option

  val map_filter : (Evar.t -> Evar.t option) -> t -> t
  (** Applies a function on the future goals *)

  val filter : (Evar.t -> bool) -> t -> t
  (** Applies a filter on the future goals *)

  type stack

  val empty_stack : stack

  val push : stack -> stack
  val pop : stack -> t * stack

  val add : principal:bool -> Evar.t -> stack -> stack
  val remove : Evar.t -> stack -> stack

  val fold : ('a -> Evar.t -> 'a) -> 'a -> stack -> 'a

  val pr_stack : stack -> Pp.t

end = struct

  type t = {
    uid : int;
    comb : Evar.t Int.Map.t;
    revmap : int Evar.Map.t;
    principal : Evar.t option; (** if [Some e], [e] must be
                                   contained in
                                   [comb]. The evar
                                   [e] will inherit
                                   properties (now: the
                                   name) of the evar which
                                   will be instantiated with
                                   a term containing [e]. *)
  }

  let comb g =
    (* Keys are reversed, highest number is last introduced *)
    Int.Map.fold (fun _ evk accu -> evk :: accu) g.comb []

  let principal g = g.principal

  type stack = t list

  let set f = function
  | [] -> anomaly Pp.(str"future_goals stack should not be empty")
  | hd :: tl ->
    f hd :: tl

  let add ~principal evk stack =
    let add fgl =
      let comb = Int.Map.add fgl.uid evk fgl.comb in
      let revmap = Evar.Map.add evk fgl.uid fgl.revmap in
      let principal =
        if principal then
          match fgl.principal with
          | Some _ -> CErrors.user_err Pp.(str "Only one main goal per instantiation.")
          | None -> Some evk
        else fgl.principal
      in
      let uid = fgl.uid + 1 in
      let () = assert (0 <= uid) in
      { comb; revmap; principal; uid }
    in
    set add stack

  let remove e stack =
    let remove fgl =
      let filter e' = not (Evar.equal e e') in
      let principal = Option.filter filter fgl.principal in
      let comb, revmap = match Evar.Map.find e fgl.revmap with
      | index -> (Int.Map.remove index fgl.comb, Evar.Map.remove e fgl.revmap)
      | exception Not_found -> fgl.comb, fgl.revmap
      in
      { principal; comb; revmap; uid = fgl.uid }
    in
    List.map remove stack

  let empty = {
    uid = 0;
    principal = None;
    comb = Int.Map.empty;
    revmap = Evar.Map.empty;
  }

  let empty_stack = [empty]

  let push stack = empty :: stack

  let pop stack =
    match stack with
    | [] -> anomaly Pp.(str"future_goals stack should not be empty")
    | hd :: tl ->
      hd, tl

  let fold f acc stack =
    let future_goals = List.hd stack in
    List.fold_left f acc (comb future_goals)

  let filter f fgl =
    let fold index evk (comb, revmap) =
      if f evk then (comb, revmap)
      else (Int.Map.remove index comb, Evar.Map.remove evk revmap)
    in
    let (comb, revmap) = Int.Map.fold fold fgl.comb (fgl.comb, fgl.revmap) in
    let principal = Option.filter f fgl.principal in
    { comb; principal; revmap; uid = fgl.uid }

  let map_filter f fgl =
    let fold index evk (comb, revmap) = match f evk with
    | None -> (comb, revmap)
    | Some evk' ->
      (Int.Map.add index evk' comb, Evar.Map.add evk' index revmap)
    in
    let (comb, revmap) = Int.Map.fold fold fgl.comb (Int.Map.empty, Evar.Map.empty) in
    let principal = Option.bind fgl.principal f in
    { comb; revmap; principal; uid = fgl.uid }

  let pr_stack stack =
    let open Pp in
    let pr_future_goals fgl =
      let comb = comb fgl in
      prlist_with_sep spc Evar.print comb ++
        pr_opt (fun ev -> str"(principal: " ++ Evar.print ev ++ str")") fgl.principal
    in
    if List.is_empty stack then str"(empty stack)"
    else prlist_with_sep (fun () -> str"||") pr_future_goals stack

end

type evar_map = {
  (* Existential variables *)
  defn_evars : defined evar_info EvMap.t;
  undf_evars : undefined evar_info EvMap.t;
  evar_names : EvNames.t;
  candidate_evars : Evar.Set.t; (* The subset of undefined evars with a non-empty candidate list. *)
  (** Universes *)
  universes  : UState.t;
  (** Conversion problems *)
  conv_pbs   : evar_constraint list;
  last_mods  : Evar.Set.t;
  (** Metas *)
  metas      : clbinding Metamap.t;
  evar_flags : evar_flags;
  (** Interactive proofs *)
  effects    : side_effects;
  future_goals : FutureGoals.stack; (** list of newly created evars, to be
                                        eventually turned into goals if not solved.*)
  given_up : Evar.Set.t;
  shelf : Evar.t list list;
  extras : Store.t;
}

let find d e =
  try EvarInfo (EvMap.find e d.undf_evars)
  with Not_found -> EvarInfo (EvMap.find e d.defn_evars)

let rec thin_val = function
  | [] -> []
  | (id, c) :: tl ->
    match Constr.kind c with
    | Constr.Var v ->
      if Id.equal id v then thin_val tl
      else (id, make_substituend c) :: (thin_val tl)
    | _ -> (id, make_substituend c) :: (thin_val tl)

let rec find_var id = function
| [] -> raise_notrace Not_found
| (idc, c) :: subst ->
  if Id.equal id idc then c
  else find_var id subst

let replace_vars sigma var_alist x =
  let var_alist = thin_val var_alist in
  match var_alist with
  | [] -> x
  | _ ->
    let rec substrec n c = match Constr.kind c with
    | Constr.Var id ->
      begin match find_var id var_alist with
      | var -> (lift_substituend n var)
      | exception Not_found -> c
      end
    | Constr.Evar (evk, args) ->
      let EvarInfo evi = find sigma evk in
      let args' = substrec_instance n (evar_filtered_context evi) args in
      if args' == args then c
      else Constr.mkEvar (evk, args')
    | _ -> Constr.map_with_binders succ substrec n c

    and substrec_instance n ctx args = match ctx, SList.view args with
    | [], None -> SList.empty
    | decl :: ctx, Some (c, args) ->
      let c' = match c with
      | None ->
        begin match find_var (NamedDecl.get_id decl) var_alist with
        | var -> Some (lift_substituend n var)
        | exception Not_found -> None
        end
      | Some c ->
        let c' = substrec n c in
        if isVarId (NamedDecl.get_id decl) c' then None
        else Some c'
      in
      SList.cons_opt c' (substrec_instance n ctx args)
    | _ :: _, None | [], Some _ -> instance_mismatch ()
    in
    substrec 0 x

let instantiate_evar_array sigma info c args =
  let inst = make_evar_instance_array info args in
  match inst with
  | [] -> c
  | _ -> replace_vars sigma inst c

let expand_existential sigma (evk, args) =
  let EvarInfo evi = find sigma evk in
  let rec expand ctx args = match ctx, SList.view args with
  | [], None -> []
  | _ :: ctx, Some (Some c, args) -> c :: expand ctx args
  | decl :: ctx, Some (None, args) -> mkVar (NamedDecl.get_id decl) :: expand ctx args
  | [], Some _ | _ :: _, None -> instance_mismatch ()
  in
  expand (evar_filtered_context evi) args

let expand_existential0 = expand_existential

let get_is_maybe_typeclass, (is_maybe_typeclass_hook : (evar_map -> constr -> bool) Hook.t) = Hook.make ()

let is_maybe_typeclass sigma c = Hook.get get_is_maybe_typeclass sigma c

(*** Lifting primitive from Evar.Map. ***)

let rename evk id evd =
  { evd with evar_names = EvNames.rename evk id evd.evar_names }

let add_with_name (type a) ?name ?(typeclass_candidate = true) d e (i : a evar_info) = match i.evar_body with
| Evar_empty ->
  let evar_names = EvNames.add_name_undefined name e i d.evar_names in
  let evar_flags =
    if typeclass_candidate && is_maybe_typeclass d (evar_concl i) then
      let flags = d.evar_flags in
      { flags with typeclass_evars = Evar.Set.add e flags.typeclass_evars }
    else d.evar_flags
  in
  let evar_flags = match i.evar_source with
    | _, ImpossibleCase ->
      { evar_flags with impossible_case_evars = Evar.Set.add e evar_flags.impossible_case_evars }
    | _ -> evar_flags
  in
  let candidate_evars = match i.evar_candidates with
  | Undefined None -> Evar.Set.remove e d.candidate_evars
  | Undefined (Some _) -> Evar.Set.add e d.candidate_evars
  in
  { d with undf_evars = EvMap.add e i d.undf_evars; evar_names; evar_flags; candidate_evars }
| Evar_defined _ ->
  let evar_names = EvNames.remove_name_defined e d.evar_names in
  { d with defn_evars = EvMap.add e i d.defn_evars; evar_names }

(** Evd.add is a low-level function mainly used to update the evar_info
    associated to an evar, so we prevent registering its typeclass status. *)
let add d e i = add_with_name ~typeclass_candidate:false d e i

(*** Evar flags: typeclasses, aliased or obligation flag *)

let get_typeclass_evars evd = evd.evar_flags.typeclass_evars

let set_typeclass_evars evd tcs =
  let flags = evd.evar_flags in
  { evd with evar_flags = { flags with typeclass_evars = tcs } }

let is_typeclass_evar evd evk =
  let flags = evd.evar_flags in
  Evar.Set.mem evk flags.typeclass_evars

let get_obligation_evars evd = evd.evar_flags.obligation_evars

let set_obligation_evar evd evk =
  let flags = evd.evar_flags in
  let evar_flags = { flags with obligation_evars = Evar.Set.add evk flags.obligation_evars } in
  { evd with evar_flags }

let is_obligation_evar evd evk =
  let flags = evd.evar_flags in
  Evar.Set.mem evk flags.obligation_evars

let get_impossible_case_evars evd = evd.evar_flags.impossible_case_evars

(** Inheritance of flags: for evar-evar and restriction cases *)

let inherit_evar_flags evar_flags evk evk' =
  let evk_typeclass = Evar.Set.mem evk evar_flags.typeclass_evars in
  let evk_obligation = Evar.Set.mem evk evar_flags.obligation_evars in
  let evk_impossible = Evar.Set.mem evk evar_flags.impossible_case_evars in
  let aliased_evars = Evar.Map.add evk evk' evar_flags.aliased_evars in
  let typeclass_evars =
    if evk_typeclass then
      let typeclass_evars = Evar.Set.remove evk evar_flags.typeclass_evars in
      Evar.Set.add evk' typeclass_evars
    else evar_flags.typeclass_evars
  in
  let obligation_evars =
    if evk_obligation then
      let obligation_evars = Evar.Set.remove evk evar_flags.obligation_evars in
      Evar.Set.add evk' obligation_evars
    else evar_flags.obligation_evars
  in
  let impossible_case_evars =
    if evk_impossible then
      let impossible_case_evars = Evar.Set.remove evk evar_flags.impossible_case_evars in
      Evar.Set.add evk' impossible_case_evars
    else evar_flags.impossible_case_evars
  in
  { obligation_evars; aliased_evars; typeclass_evars; impossible_case_evars; }

(** Removal: in all other cases of definition *)

let remove_evar_flags evk evar_flags =
  { typeclass_evars = Evar.Set.remove evk evar_flags.typeclass_evars;
    obligation_evars = Evar.Set.remove evk evar_flags.obligation_evars;
    impossible_case_evars = Evar.Set.remove evk evar_flags.impossible_case_evars;
    (* Aliasing information is kept. *)
    aliased_evars = evar_flags.aliased_evars;
  }

(** New evars *)

let evar_counter_summary_name = "evar counter"

(* Generator of existential names *)
let evar_ctr, evar_counter_summary_tag = Summary.ref_tag 0 ~name:evar_counter_summary_name
let new_untyped_evar () = incr evar_ctr; Evar.unsafe_of_int !evar_ctr

let default_source = Loc.tag @@ Evar_kinds.InternalHole

let remove d e =
  let undf_evars = EvMap.remove e d.undf_evars in
  let defn_evars = EvMap.remove e d.defn_evars in
  let future_goals = FutureGoals.remove e d.future_goals in
  let evar_flags = remove_evar_flags e d.evar_flags in
  let candidate_evars = Evar.Set.remove e d.candidate_evars in
  { d with undf_evars; defn_evars; future_goals;
           evar_flags; candidate_evars }

let undefine sigma e concl =
  let EvarInfo evi = find sigma e in
  let evi = { evi with
    evar_body = Evar_empty;
    evar_concl = Undefined concl;
    evar_candidates = Undefined None;
    evar_abstract_arguments = Undefined Abstraction.identity;
  } in
  add (remove sigma e) e evi

let find_defined d e = EvMap.find_opt e d.defn_evars

let find_undefined d e = EvMap.find e d.undf_evars

let mem d e = EvMap.mem e d.undf_evars || EvMap.mem e d.defn_evars

let undefined_map d = d.undf_evars

let drop_all_defined d = { d with defn_evars = EvMap.empty }

(* spiwack: not clear what folding over an evar_map, for now we shall
    simply fold over the inner evar_map. *)
let fold f d a =
  let f evk evi accu = f evk (EvarInfo evi) accu in
  EvMap.fold f d.defn_evars (EvMap.fold f d.undf_evars a)

let fold_undefined f d a = EvMap.fold f d.undf_evars a

type map = { map : 'r. Evar.t -> 'r evar_info -> 'r evar_info }

let raw_map f d =
  let defn_evars = EvMap.Smart.mapi f.map d.defn_evars in
  let undf_evars = EvMap.Smart.mapi f.map d.undf_evars in
  { d with defn_evars; undf_evars; }

let raw_map_undefined f d =
  { d with undf_evars = EvMap.Smart.mapi f d.undf_evars; }

let is_evar = mem

let is_defined d e = EvMap.mem e d.defn_evars

let is_undefined d e = EvMap.mem e d.undf_evars

let existential_opt_value d (n, args) =
  match EvMap.find_opt n d.defn_evars with
  | None -> None
  | Some info ->
    let Evar_defined c = evar_body info in
    Some (instantiate_evar_array d info c args)

let existential_value d ev = match existential_opt_value d ev with
  | None -> raise NotInstantiatedEvar
  | Some v -> v

let existential_value0 = existential_value

let existential_opt_value0 = existential_opt_value

let existential_expand_value0 sigma (evk, args) = match existential_opt_value sigma (evk, args) with
| None ->
  let args = expand_existential sigma (evk, args) in
  CClosure.EvarUndefined (evk, args)
| Some c -> CClosure.EvarDefined c

let mkLEvar sigma (evk, args) =
  let EvarInfo evi = find sigma evk in
  let fold decl arg accu =
    if isVarId (NamedDecl.get_id decl) arg then SList.default accu
    else SList.cons arg accu
  in
  let args = List.fold_right2 fold (evar_filtered_context evi) args SList.empty in
  mkEvar (evk, args)

let evar_handler sigma =
  let evar_expand ev = existential_expand_value0 sigma ev in
  let qvar_irrelevant q = match UState.nf_qvar sigma.universes q with
  | QConstant QSProp -> true
  | QConstant QProp | QConstant QType | QVar _ -> false
  in
  let evar_irrelevant (evk, _) = match find sigma evk with
  | EvarInfo evi ->
    begin match evi.evar_relevance with
    | Sorts.Relevant -> false
    | Sorts.Irrelevant -> true
    | Sorts.RelevanceVar q -> qvar_irrelevant q
    end
  | exception Not_found -> true
  in
  let evar_repack ev = mkLEvar sigma ev in
  { CClosure.evar_expand; evar_irrelevant; evar_repack; qvar_irrelevant }

let existential_type_opt d (n, args) =
  match find_undefined d n with
  | exception Not_found -> None
  | info ->
    Some (instantiate_evar_array d info (evar_concl info) args)

let existential_type d n = match existential_type_opt d n with
  | Some t -> t
  | None -> anomaly (str "Evar " ++ str (string_of_existential (fst n)) ++ str " was not declared.")

let existential_type0 = existential_type

let add_constraints d c =
  { d with universes = UState.add_constraints d.universes c }

let add_quconstraints d c =
  { d with universes = UState.add_quconstraints d.universes c }

let add_universe_constraints d c =
  { d with universes = UState.add_universe_constraints d.universes c }

(*** /Lifting... ***)

(* evar_map are considered empty disregarding histories *)
let is_empty d =
  EvMap.is_empty d.defn_evars &&
  EvMap.is_empty d.undf_evars &&
  List.is_empty d.conv_pbs &&
  Metamap.is_empty d.metas

let cmap f evd =
  { evd with
      metas = Metamap.map (map_clb f) evd.metas;
      defn_evars = EvMap.map (map_evar_info f) evd.defn_evars;
      undf_evars = EvMap.map (map_evar_info f) evd.undf_evars
  }

(* spiwack: deprecated *)
let create_evar_defs sigma = { sigma with
  conv_pbs=[]; last_mods=Evar.Set.empty; metas=Metamap.empty }

let empty_evar_flags =
  { obligation_evars = Evar.Set.empty;
    aliased_evars = Evar.Map.empty;
    typeclass_evars = Evar.Set.empty;
    impossible_case_evars = Evar.Set.empty;
  }

let empty_side_effects = {
  seff_private = Safe_typing.empty_private_constants;
  seff_roles = Cmap.empty;
}

let empty = {
  defn_evars = EvMap.empty;
  undf_evars = EvMap.empty;
  universes  = UState.empty;
  conv_pbs   = [];
  last_mods  = Evar.Set.empty;
  evar_flags = empty_evar_flags;
  candidate_evars = Evar.Set.empty;
  metas      = Metamap.empty;
  effects    = empty_side_effects;
  evar_names = EvNames.empty; (* id<->key for undefined evars *)
  future_goals = FutureGoals.empty_stack;
  given_up = Evar.Set.empty;
  shelf = [[]];
  extras = Store.empty;
}

let from_env ?binders e = { empty with universes = UState.from_env ?binders e }

let from_ctx uctx = { empty with universes = uctx }

let has_undefined evd = not (EvMap.is_empty evd.undf_evars)

let has_given_up evd = not (Evar.Set.is_empty evd.given_up)

let has_shelved evd = not (List.for_all List.is_empty evd.shelf)

let merge_universe_context evd uctx' =
  { evd with universes = UState.union evd.universes uctx' }

let set_universe_context evd uctx' =
  { evd with universes = uctx' }

(* TODO: make unique *)
let add_conv_pb ?(tail=false) pb d =
  if tail then {d with conv_pbs = d.conv_pbs @ [pb]}
  else {d with conv_pbs = pb::d.conv_pbs}

let conv_pbs d = d.conv_pbs

let evar_source evi = evi.evar_source

let evar_names evd = EvNames.state evd.evar_names
let evar_ident evk evd = EvNames.ident evk evd.evar_names
let evar_key id evd = EvNames.key id evd.evar_names

let get_aliased_evars evd = evd.evar_flags.aliased_evars

let max_undefined_with_candidates evd =
  try Some (Evar.Set.max_elt evd.candidate_evars) with Not_found -> None

let is_aliased_evar evd evk =
  try Some (Evar.Map.find evk evd.evar_flags.aliased_evars)
  with Not_found -> None

let downcast evk ccl evd =
  let evar_info = EvMap.find evk evd.undf_evars in
  let evar_info' = { evar_info with evar_concl = Undefined ccl } in
  { evd with undf_evars = EvMap.add evk evar_info' evd.undf_evars }

(* extracts conversion problems that satisfy predicate p *)
(* Note: conv_pbs not satisying p are stored back in reverse order *)
let extract_conv_pbs evd p =
  let (pbs,pbs1) =
    List.fold_left
      (fun (pbs,pbs1) pb ->
         if p pb then
           (pb::pbs,pbs1)
         else
           (pbs,pb::pbs1))
      ([],[])
      evd.conv_pbs
  in
  {evd with conv_pbs = pbs1; last_mods = Evar.Set.empty},
  pbs

let extract_changed_conv_pbs evd p =
  extract_conv_pbs evd (fun pb -> p evd.last_mods pb)

let extract_all_conv_pbs evd =
  extract_conv_pbs evd (fun _ -> true)

let loc_of_conv_pb evd (pbty,env,t1,t2) =
  match kind (fst (decompose_app t1)) with
  | Evar (evk1,_) ->
    let EvarInfo evi = find evd evk1 in
    fst (evar_source evi)
  | _ ->
  match kind (fst (decompose_app t2)) with
  | Evar (evk2,_) ->
    let EvarInfo evi = find evd evk2 in
    fst (evar_source evi)
  | _             -> None

(**********************************************************)
(* Sort variables *)

type rigid = UState.rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let evar_universe_context d = d.universes

let universe_context_set d = UState.context_set d.universes

let sort_context_set d = UState.sort_context_set d.universes

let to_universe_context evd = UState.context evd.universes

let univ_entry ~poly evd = UState.univ_entry ~poly evd.universes

let check_univ_decl ~poly evd decl = UState.check_univ_decl ~poly evd.universes decl

let restrict_universe_context evd vars =
  { evd with universes = UState.restrict evd.universes vars }

let universe_subst evd =
  UState.subst evd.universes

let merge_context_set ?loc ?(sideff=false) rigid evd uctx' =
  {evd with universes = UState.merge ?loc ~sideff rigid evd.universes uctx'}

let merge_sort_context_set ?loc ?(sideff=false) rigid evd ctx' =
  {evd with universes = UState.merge_sort_context ?loc ~sideff rigid evd.universes ctx'}

let merge_sort_variables ?loc ?(sideff=false) evd qs =
  { evd with universes = UState.merge_sort_variables ?loc ~sideff evd.universes qs }

let with_context_set ?loc rigid evd (a, uctx) =
  (merge_context_set ?loc rigid evd uctx, a)

let with_sort_context_set ?loc rigid d (a, ctx) =
  (merge_sort_context_set ?loc rigid d ctx, a)

let new_univ_level_variable ?loc ?name rigid evd =
  let uctx', u = UState.new_univ_variable ?loc rigid name evd.universes in
    ({evd with universes = uctx'}, u)

let new_univ_variable ?loc ?name rigid evd =
  let uctx', u = UState.new_univ_variable ?loc rigid name evd.universes in
    ({evd with universes = uctx'}, Univ.Universe.make u)

let new_quality_variable ?loc ?name evd =
  let uctx, q = UState.new_sort_variable ?loc ?name evd.universes in
  {evd with universes = uctx}, q

let new_sort_variable ?loc rigid sigma =
  let (sigma, u) = new_univ_variable ?loc rigid sigma in
  let uctx, q = UState.new_sort_variable sigma.universes in
  ({ sigma with universes = uctx }, Sorts.qsort q u)

let add_global_univ d u =
  { d with universes = UState.add_global_univ d.universes u }

let make_nonalgebraic_variable evd u =
  { evd with universes = UState.make_nonalgebraic_variable evd.universes u }

(****************************************)
(* Operations on constants              *)
(****************************************)

let fresh_sort_in_family ?loc ?(rigid=univ_flexible) evd s =
  with_sort_context_set ?loc rigid evd (UnivGen.fresh_sort_in_family s)

let fresh_constant_instance ?loc ?(rigid=univ_flexible) env evd c =
  with_sort_context_set ?loc rigid evd (UnivGen.fresh_constant_instance env c)

let fresh_inductive_instance ?loc ?(rigid=univ_flexible) env evd i =
  with_sort_context_set ?loc rigid evd (UnivGen.fresh_inductive_instance env i)

let fresh_constructor_instance ?loc ?(rigid=univ_flexible) env evd c =
  with_sort_context_set ?loc rigid evd (UnivGen.fresh_constructor_instance env c)

let fresh_array_instance ?loc ?(rigid=univ_flexible) env evd =
  with_sort_context_set ?loc rigid evd (UnivGen.fresh_array_instance env)

let fresh_global ?loc ?(rigid=univ_flexible) ?names env evd gr =
  with_sort_context_set ?loc rigid evd (UnivGen.fresh_global_instance ?loc ?names env gr)

let is_flexible_level evd l =
  let uctx = evd.universes in
  UnivFlex.mem l (UState.subst uctx)

let is_eq_sort s1 s2 =
  if Sorts.equal s1 s2 then None
  else Some (s1, s2)

(* Precondition: l is not defined in the substitution *)
let universe_rigidity evd l =
  let uctx = evd.universes in
  (* XXX why are we considering all locals to be flexible here? *)
  if Univ.Level.Set.mem l (Univ.ContextSet.levels (UState.context_set uctx)) then
    UnivFlexible (UState.is_algebraic l uctx)
  else UnivRigid

let normalize_universe_instance evd l =
  UState.nf_instance evd.universes l

let normalize_sort evars s =
  UState.nf_sort evars.universes s

(* FIXME inefficient *)
let set_eq_sort env d s1 s2 =
  let s1 = normalize_sort d s1 and s2 = normalize_sort d s2 in
  match is_eq_sort s1 s2 with
  | None -> d
  | Some (u1, u2) ->
    if not (type_in_type env) then
      add_universe_constraints d
        (UnivProblem.Set.singleton (UnivProblem.UEq (u1,u2)))
    else
      d

let set_eq_level d u1 u2 =
  add_constraints d (Univ.enforce_eq_level u1 u2 Univ.Constraints.empty)

let set_leq_level d u1 u2 =
  add_constraints d (Univ.enforce_leq_level u1 u2 Univ.Constraints.empty)

let set_eq_instances ?(flex=false) d u1 u2 =
  add_universe_constraints d
    (UnivProblem.enforce_eq_instances_univs flex u1 u2 UnivProblem.Set.empty)

let set_leq_sort env evd s1 s2 =
  let s1 = normalize_sort evd s1
  and s2 = normalize_sort evd s2 in
  match is_eq_sort s1 s2 with
  | None -> evd
  | Some (u1, u2) ->
     if not (type_in_type env) then
       add_universe_constraints evd (UnivProblem.Set.singleton (UnivProblem.ULe (u1,u2)))
     else evd

let check_eq evd s s' =
  let ustate = evd.universes in
  UGraph.check_eq_sort (UState.ugraph ustate) (UState.nf_sort ustate s) (UState.nf_sort ustate s')

let check_leq evd s s' =
  let ustate = evd.universes in
  UGraph.check_leq_sort (UState.ugraph ustate) (UState.nf_sort ustate s) (UState.nf_sort ustate s')

let check_constraints evd csts =
  UGraph.check_constraints csts (UState.ugraph evd.universes)

let check_qconstraints evd csts =
  UState.check_qconstraints evd.universes csts

let check_quconstraints evd (qcsts,ucsts) =
  check_qconstraints evd qcsts && check_constraints evd ucsts

let fix_undefined_variables evd =
  { evd with universes = UState.fix_undefined_variables evd.universes }

let nf_univ_variables evd =
  let uctx = UState.normalize_variables evd.universes in
  {evd with universes = uctx}

let collapse_sort_variables evd =
  let universes = UState.collapse_sort_variables evd.universes in
  { evd with universes }

let minimize_universes evd =
  let uctx' = UState.collapse_sort_variables evd.universes in
  let uctx' = UState.normalize_variables uctx' in
  let uctx' = UState.minimize uctx' in
  {evd with universes = uctx'}

let universe_of_name evd s = UState.universe_of_name evd.universes s

let quality_of_name evd s = UState.quality_of_name evd.universes s

let universe_binders evd = UState.universe_binders evd.universes

let universes evd = UState.ugraph evd.universes

let update_sigma_univs ugraph evd =
  { evd with universes = UState.update_sigma_univs evd.universes ugraph }

exception UniversesDiffer = UState.UniversesDiffer

(**********************************************************)
(* Side effects *)

let concat_side_effects eff eff' = {
  seff_private = Safe_typing.concat_private eff.seff_private eff'.seff_private;
  seff_roles = Cmap.fold Cmap.add eff.seff_roles eff'.seff_roles;
}

let emit_side_effects eff evd =
  let effects = concat_side_effects eff evd.effects in
  { evd with effects; universes = UState.emit_side_effects eff.seff_private evd.universes }

let drop_side_effects evd =
  { evd with effects = empty_side_effects; }

let eval_side_effects evd = evd.effects

(* Future goals *)
let declare_future_goal evk evd =
  let future_goals = FutureGoals.add ~principal:false evk evd.future_goals in
  { evd with future_goals }

let declare_principal_goal evk evd =
  let future_goals = FutureGoals.add ~principal:true evk evd.future_goals in
  { evd with future_goals }

let push_future_goals evd =
  { evd with future_goals = FutureGoals.push evd.future_goals }

let pop_future_goals evd =
  let hd, future_goals = FutureGoals.pop evd.future_goals in
  hd, { evd with future_goals }

let fold_future_goals f sigma =
  FutureGoals.fold f sigma sigma.future_goals

let remove_future_goal evd evk =
  { evd with future_goals = FutureGoals.remove evk evd.future_goals }

let pr_future_goals_stack evd =
  FutureGoals.pr_stack evd.future_goals

let give_up ev evd =
  { evd with given_up = Evar.Set.add ev evd.given_up }

let push_shelf evd =
  { evd with shelf = [] :: evd.shelf }

let pop_shelf evd =
  match evd.shelf with
  | [] -> anomaly Pp.(str"shelf stack should not be empty")
  | hd :: tl ->
    hd, { evd with shelf = tl }

let filter_shelf f evd =
  { evd with shelf = List.map (List.filter f) evd.shelf }

let shelve evd l =
  match evd.shelf with
  | [] -> anomaly Pp.(str"shelf stack should not be empty")
  | hd :: tl ->
    { evd with shelf = (hd@l) :: tl }

let unshelve evd l =
  { evd with shelf = List.map (List.filter (fun ev -> not (CList.mem_f Evar.equal ev l))) evd.shelf }

let given_up evd = evd.given_up

let shelf evd = List.flatten evd.shelf

let pr_shelf evd =
  let open Pp in
  if List.is_empty evd.shelf then str"(empty stack)"
  else prlist_with_sep (fun () -> str"||") (prlist_with_sep spc Evar.print) evd.shelf

let new_pure_evar ?(src=default_source) ?(filter = Filter.identity) ?(relevance = Sorts.Relevant)
  ?(abstract_arguments = Abstraction.identity) ?candidates
  ?name ?typeclass_candidate ?(principal=false) sign evd typ =
  let evi = {
    evar_hyps = sign;
    evar_concl = Undefined typ;
    evar_body = Evar_empty;
    evar_filter = filter;
    evar_abstract_arguments = Undefined abstract_arguments;
    evar_source = src;
    evar_candidates = Undefined candidates;
    evar_relevance = relevance;
  }
  in
  let typeclass_candidate = if principal then Some false else typeclass_candidate in
  let newevk = new_untyped_evar () in
  let evd = add_with_name evd ?name ?typeclass_candidate newevk evi in
  let evd =
    if principal then declare_principal_goal newevk evd
    else declare_future_goal newevk evd
  in
  (evd, newevk)

let define_aux def undef evk body =
  let oldinfo =
    try EvMap.find evk undef
    with Not_found ->
      if EvMap.mem evk def then
        anomaly ~label:"Evd.define" (Pp.str "cannot define an evar twice.")
      else
        anomaly ~label:"Evd.define" (Pp.str "cannot define undeclared evar.")
  in
  let () = assert (oldinfo.evar_body == Evar_empty) in
  let newinfo = { oldinfo with
    evar_body = Evar_defined body;
    evar_concl = Defined;
    evar_candidates = Defined;
    evar_abstract_arguments = Defined;
  } in
  EvMap.add evk newinfo def, EvMap.remove evk undef

(* define the existential of section path sp as the constr body *)
let define_gen evk body evd evar_flags =
  let future_goals = FutureGoals.remove evk evd.future_goals in
  let evd = { evd with future_goals } in
  let (defn_evars, undf_evars) = define_aux evd.defn_evars evd.undf_evars evk body in
  let last_mods = match evd.conv_pbs with
  | [] ->  evd.last_mods
  | _ -> Evar.Set.add evk evd.last_mods
  in
  let evar_names = EvNames.remove_name_defined evk evd.evar_names in
  let candidate_evars = Evar.Set.remove evk evd.candidate_evars in
  { evd with defn_evars; undf_evars; last_mods; evar_names; evar_flags; candidate_evars }

(** By default, the obligation and evar tag of the evar is removed *)
let define evk body evd =
  let evar_flags = remove_evar_flags evk evd.evar_flags in
  define_gen evk body evd evar_flags

(** In case of an evar-evar solution, the flags are inherited *)
let define_with_evar evk body evd =
  let evk' = fst (destEvar body) in
  let evar_flags = inherit_evar_flags evd.evar_flags evk evk' in
  let evd = unshelve evd [evk] in
  define_gen evk body evd evar_flags

(* In case of restriction, we declare the aliasing and inherit the obligation
   and typeclass flags. *)

let restrict evk filter ?candidates ?src evd =
  let evk' = new_untyped_evar () in
  let evar_info = EvMap.find evk evd.undf_evars in
  let len = Range.length evar_info.evar_hyps.env_named_idx in
  let id_inst = Filter.filter_slist filter (SList.defaultn len SList.empty) in
  let evar_info' =
    { evar_info with evar_filter = filter;
      evar_candidates = Undefined candidates;
      evar_source = (match src with None -> evar_info.evar_source | Some src -> src);
    } in
  let last_mods = match evd.conv_pbs with
  | [] ->  evd.last_mods
  | _ -> Evar.Set.add evk evd.last_mods in
  let evar_names = EvNames.reassign_name_defined evk evk' evd.evar_names in
  let body = mkEvar(evk',id_inst) in
  let (defn_evars, undf_evars) = define_aux evd.defn_evars evd.undf_evars evk body in
  let evar_flags = inherit_evar_flags evd.evar_flags evk evk' in
  let evar_flags = match src with
    | Some (_,Evar_kinds.ImpossibleCase) ->
      { evar_flags with impossible_case_evars = Evar.Set.add evk' evar_flags.impossible_case_evars }
    | _ -> evar_flags
  in
  let candidate_evars = Evar.Set.remove evk evd.candidate_evars in
  let candidate_evars = match candidates with
  | None -> candidate_evars
  | Some _ -> Evar.Set.add evk' candidate_evars
  in
  let evd = { evd with undf_evars = EvMap.add evk' evar_info' undf_evars;
    defn_evars; last_mods; evar_names; evar_flags; candidate_evars }
  in
  (* Mark new evar as future goal, removing previous one,
    circumventing Proofview.advance but making Proof.run_tactic catch these. *)
  let evd = unshelve evd [evk] in
  let evd = remove_future_goal evd evk in
  let evd = declare_future_goal evk' evd in
  (evd, evk')

let update_source evd evk src =
  let modify _ info = { info with evar_source = src } in
  { evd with undf_evars = EvMap.modify evk modify evd.undf_evars }

(**********************************************************)
(* Accessing metas *)

(** We use this function to overcome OCaml compiler limitations and to prevent
    the use of costly in-place modifications. *)
let set_metas evd metas = {
  defn_evars = evd.defn_evars;
  undf_evars = evd.undf_evars;
  universes  = evd.universes;
  conv_pbs = evd.conv_pbs;
  last_mods = evd.last_mods;
  evar_flags = evd.evar_flags;
  candidate_evars = evd.candidate_evars;
  metas;
  effects = evd.effects;
  evar_names = evd.evar_names;
  future_goals = evd.future_goals;
  given_up = evd.given_up;
  shelf = evd.shelf;
  extras = evd.extras;
}

let meta_list evd = evd.metas

let map_metas_fvalue f evd =
  let map = function
  | Clval(id,(c,s),typ) -> Clval(id,(mk_freelisted (f c.rebus),s),typ)
  | x -> x
  in
  set_metas evd (Metamap.Smart.map map evd.metas)

let map_metas f evd =
  let map cl = map_clb f cl in
  set_metas evd (Metamap.Smart.map map evd.metas)

let meta_opt_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> Some b
    | Cltyp _ -> None

let meta_value evd mv = match meta_opt_fvalue evd mv with
| Some (body, _) -> body.rebus
| None -> raise Not_found

let meta_ftype evd mv =
  match Metamap.find mv evd.metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b

let meta_declare mv v ?(name=Anonymous) evd =
  let metas = Metamap.add mv (Cltyp(name,mk_freelisted v)) evd.metas in
  set_metas evd metas

(* If the meta is defined then forget its name *)
let meta_name evd mv =
  try fst (clb_name (Metamap.find mv evd.metas)) with Not_found -> Anonymous

let evar_source_of_meta mv evd =
  match meta_name evd mv with
  | Anonymous -> Loc.tag Evar_kinds.GoalEvar
  | Name id   -> Loc.tag @@ Evar_kinds.VarInstance id

let use_meta_source evd mv v =
  match Constr.kind v with
  | Evar (evk,_) ->
    let f = function
    | None -> None
    | Some evi as x ->
      match evi.evar_source with
      | None, Evar_kinds.GoalEvar -> Some { evi with evar_source = evar_source_of_meta mv evd }
      | _ -> x in
    { evd with undf_evars = EvMap.update evk f evd.undf_evars }
  | _ -> evd

let meta_assign mv (v, pb) evd =
  let modify _ = function
  | Cltyp (na, ty) -> Clval (na, (mk_freelisted v, pb), ty)
  | _ -> anomaly ~label:"meta_assign" (Pp.str "already defined.")
  in
  let metas = Metamap.modify mv modify evd.metas in
  let evd = use_meta_source evd mv v in
  set_metas evd metas

let meta_reassign mv (v, pb) evd =
  let modify _ = function
  | Clval(na, _, ty) -> Clval (na, (mk_freelisted v, pb), ty)
  | _ -> anomaly ~label:"meta_reassign" (Pp.str "not yet defined.")
  in
  let metas = Metamap.modify mv modify evd.metas in
  set_metas evd metas

let clear_metas evd = {evd with metas = Metamap.empty}

let meta_merge metas sigma =
  let metas = Metamap.fold Metamap.add metas sigma.metas in
  { sigma with metas }

type metabinding = metavariable * constr * instance_status

let retract_coercible_metas evd =
  let mc = ref [] in
  let map n v = match v with
  | Clval (na, (b, (Conv, CoerceToType as s)), typ) ->
    let () = mc := (n, b.rebus, s) :: !mc in
    Cltyp (na, typ)
  | v -> v
  in
  let metas = Metamap.Smart.mapi map evd.metas in
  !mc, set_metas evd metas

let dependent_evar_ident ev evd =
  let EvarInfo evi = find evd ev in
  match evi.evar_source with
  | (_,Evar_kinds.VarInstance id) -> id
  | _ -> anomaly (str "Not an evar resulting of a dependent binding.")

(**********************************************************)
(* Extra data *)

let get_extra_data evd = evd.extras
let set_extra_data extras evd = { evd with extras }

(*******************************************************************)

type open_constr = evar_map * constr

(*******************************************************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map
}

let sig_it x = x.it
let sig_sig x = x.sigma
let on_sig s f =
  let sigma', v = f s.sigma in
    { s with sigma = sigma' }, v

(*******************************************************************)
(* The state monad with state an evar map. *)

module MonadR =
  Monad.Make (struct

    type +'a t = evar_map -> evar_map * 'a

    let return a = fun s -> (s,a)

    let (>>=) x f = fun s ->
      let (s',a) = x s in
      f a s'

    let (>>) x y = fun s ->
      let (s',()) = x s in
      y s'

    let map f x = fun s ->
      on_snd f (x s)

  end)

module Monad =
  Monad.Make (struct

    type +'a t = evar_map -> 'a * evar_map

    let return a = fun s -> (a,s)

    let (>>=) x f = fun s ->
      let (a,s') = x s in
      f a s'

    let (>>) x y = fun s ->
      let ((),s') = x s in
      y s'

    let map f x = fun s ->
      on_fst f (x s)

  end)

(**********************************************************)
(* Failure explanation *)

type unsolvability_explanation = SeveralInstancesFound of int

module MiniEConstr = struct

  module ESorts =
  struct
    type t = Sorts.t
    let make s = s
    let kind = normalize_sort
    let unsafe_to_sorts s = s
  end

  module EInstance =
  struct
    type t = UVars.Instance.t
    let make i = i
    let kind sigma i =
      if UVars.Instance.is_empty i then i
      else normalize_universe_instance sigma i
    let empty = UVars.Instance.empty
    let is_empty = UVars.Instance.is_empty
    let unsafe_to_instance t = t
  end

  type t = econstr

  let rec whd_evar sigma c =
    match Constr.kind c with
    | Evar ev ->
      begin match existential_opt_value sigma ev with
        | Some c -> whd_evar sigma c
        | None -> c
      end
    | App (f, args) when isEvar f ->
      (* Enforce smart constructor invariant on applications *)
      let ev = destEvar f in
      begin match existential_opt_value sigma ev with
        | None -> c
        | Some f -> whd_evar sigma (mkApp (f, args))
      end
    | Cast (c0, k, t) when isEvar c0 ->
      (* Enforce smart constructor invariant on casts. *)
      let ev = destEvar c0 in
      begin match existential_opt_value sigma ev with
        | None -> c
        | Some c -> whd_evar sigma (mkCast (c, k, t))
      end
    | _ -> c

  let mkLEvar = mkLEvar
  let replace_vars = replace_vars
  let kind sigma c = Constr.kind (whd_evar sigma c)
  let kind_upto = kind
  let of_kind = Constr.of_kind
  let of_constr c = c
  let of_constr_array v = v
  let unsafe_to_constr c = c
  let unsafe_to_constr_array v = v
  let unsafe_eq = Refl

  type evclos = {
    evc_map : (int * Vars.substituend Lazy.t) Id.Map.t;
    (* Map each bound ident to its value and the depth it was introduced at *)
    evc_lift : int; (* number of binders crossed since last evar *)
    evc_stack : int list; (* stack of binders crossed at each evar *)
    evc_depth : int; (* length of evc_stack *)
    evc_cache : int Int.Map.t ref; (* Cache get_lift on evc_stack *)
  }

  let to_constr_gen ~expand ~ignore_missing sigma c =
    let saw_evar = ref false in
    let lsubst = universe_subst sigma in
    let univ_value l =
      UnivFlex.normalize_univ_variable lsubst l
    in
    let qvar_value q = UState.nf_qvar sigma.universes q in
    let next s = { s with evc_lift = s.evc_lift + 1 } in
    let find clos id = match Id.Map.find_opt id clos.evc_map with
    | None -> None
    | Some (depth, lazy v) ->
      let pos = clos.evc_depth - depth - 1 in
      let rec get_lift accu n lft =
        if Int.equal n 0 then accu
        else match lft with
        | [] -> assert false
        | k :: lft -> get_lift (accu + k) (n - 1) lft
      in
      let ans = match Int.Map.find_opt pos clos.evc_cache.contents with
      | None ->
        let ans = get_lift 0 pos clos.evc_stack in
        let () = clos.evc_cache := Int.Map.add pos ans clos.evc_cache.contents in
        ans
      | Some ans -> ans
      in
      let k = clos.evc_lift + ans in
      Some (lift_substituend k v)
    in
    let rec self clos c = match Constr.kind c with
    | Var id ->
      begin match find clos id with
      | None -> c
      | Some v -> v
      end
    | Evar (evk, args) ->
      begin match EvMap.find_opt evk sigma.defn_evars with
      | None ->
        let () = saw_evar := true in
        begin match EvMap.find_opt evk sigma.undf_evars with
        | None ->
          if ignore_missing then
            let map c = self clos c in
            let args' = SList.Smart.map map args in
            if args' == args then c else mkEvar (evk, args')
          else raise Not_found
        | Some evi ->
          let rec inst ctx args = match ctx, SList.view args with
          | [], None -> SList.empty
          | decl :: ctx, Some (c, args) ->
            let c = match c with
            | None ->
              let c = find clos (NamedDecl.get_id decl) in
              if expand then match c with
              | None -> Some (mkVar (NamedDecl.get_id decl))
              | Some _  -> c
              else c
            | Some c -> Some (self clos c)
            in
            SList.cons_opt c (inst ctx args)
          | _ :: _, None | [], Some _ -> instance_mismatch ()
          in
          let args' = inst (evar_filtered_context evi) args in
          if args == args' then c else mkEvar (evk, args')
        end
      | Some info ->
        let Evar_defined c = evar_body info in
        let push id c map = Id.Map.add id (clos.evc_depth, lazy (make_substituend (self clos c))) map in
        let nmap = evar_instance_array clos.evc_map push info args in
        let nclos = {
          evc_lift = 0;
          evc_map = nmap;
          evc_depth = clos.evc_depth + 1;
          evc_stack = clos.evc_lift :: clos.evc_stack;
          evc_cache = ref Int.Map.empty;
        } in
        self nclos c
      end
    | _ ->
      UnivSubst.map_universes_opt_subst_with_binders next self qvar_value univ_value clos c
    in
    let clos = {
      evc_lift = 0;
      evc_depth = 0;
      evc_stack = [];
      evc_map = Id.Map.empty;
      evc_cache = ref Int.Map.empty;
    } in
    let c = self clos c in
    !saw_evar, c

  let check_evar c =
    let exception SawEvar in
    let rec iter c = match Constr.kind c with
      | Evar _ -> raise SawEvar
      | _ -> Constr.iter iter c
    in
    try iter c; false with SawEvar -> true

  let to_constr ?(abort_on_undefined_evars=true) sigma c =
    let saw_evar, c = to_constr_gen ~expand:true ~ignore_missing:false sigma c in
    if abort_on_undefined_evars && saw_evar && check_evar c then
      anomaly ~label:"econstr" Pp.(str "grounding a non evar-free term")
    else c

  let to_constr_opt sigma c =
    let saw_evar, c = to_constr_gen ~expand:false ~ignore_missing:false sigma c in
    if saw_evar && check_evar c then None else Some c

  let nf_evar sigma c =
    let _, c = to_constr_gen ~expand:false ~ignore_missing:true sigma c in
    c

  let of_named_decl d = d
  let unsafe_to_named_decl d = d
  let of_rel_decl d = d
  let unsafe_to_rel_decl d = d
  let to_rel_decl sigma d = match d with
  | RelDecl.LocalAssum (na, t) ->
    let na = UnivSubst.nf_binder_annot (fun r -> UState.nf_relevance sigma.universes r) na in
    RelDecl.LocalAssum (na, to_constr sigma t)
  | RelDecl.LocalDef (na, c, t) ->
    let na = UnivSubst.nf_binder_annot (fun r -> UState.nf_relevance sigma.universes r) na in
    RelDecl.LocalDef (na, to_constr sigma c, to_constr sigma t)

  let of_named_context d = d
  let of_rel_context d = d

  let unsafe_to_case_invert x = x
  let of_case_invert x = x

end

(** The following functions return the set of evars immediately
    contained in the object *)

(* excluding defined evars *)

let evars_of_term evd c =
  let rec evrec acc c =
    let c = MiniEConstr.whd_evar evd c in
    match kind c with
    | Evar (n, l) -> Evar.Set.add n (SList.Skip.fold evrec acc l)
    | _ -> Constr.fold evrec acc c
  in
  evrec Evar.Set.empty c

let evars_of_named_context evd nc =
  Context.Named.fold_outside
    (NamedDecl.fold_constr (fun constr s -> Evar.Set.union s (evars_of_term evd constr)))
    nc
    ~init:Evar.Set.empty

let evars_of_filtered_evar_info (type a) evd (evi : a evar_info) =
  let concl = match evi.evar_concl with
  | Undefined c -> evars_of_term evd c
  | Defined -> Evar.Set.empty
  in
  Evar.Set.union concl
    (Evar.Set.union
       (match evi.evar_body with
       | Evar_empty -> Evar.Set.empty
       | Evar_defined b -> evars_of_term evd b)
       (evars_of_named_context evd (evar_filtered_context evi)))

let drop_new_defined ~original sigma =
  let to_keep, to_drop = Evar.Map.partition (fun ev _ ->
      Evar.Map.mem ev original.defn_evars || Evar.Map.mem ev original.undf_evars)
      sigma.defn_evars
  in
  let dummy = { empty with defn_evars = to_drop } in
  let nfc c = snd @@ MiniEConstr.to_constr_gen ~expand:true ~ignore_missing:false dummy c in (* FIXME: do we really need to expand? *)
  assert (Metamap.is_empty sigma.metas);
  assert (List.is_empty sigma.conv_pbs);
  let normalize_changed _ev orig evi =
    match orig, evi with
    | _, None -> None
    | None, Some evi -> Some (map_evar_info nfc evi)
    | Some orig, Some evi -> if orig == evi then None else Some (map_evar_info nfc evi)
  in
  let normalize_against original current =
    let normalized = EvMap.merge normalize_changed original current in
    EvMap.union (fun _ _ x -> Some x) current normalized
  in
  let to_keep = normalize_against original.defn_evars to_keep in
  let undf_evars = normalize_against original.undf_evars sigma.undf_evars in
  { sigma with defn_evars = to_keep; undf_evars }
