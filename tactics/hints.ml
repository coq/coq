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
open CErrors
open Names
open Constr
open Context
open Evd
open EConstr
open Environ
open Mod_subst
open Globnames
open Libobject
open Libnames
open Termops
open Inductiveops
open Typeclasses
open Pattern
open Patternops
open Tacred
open Printer

(****************************************)
(* General functions                    *)
(****************************************)

type debug = Debug | Info | Off

exception Bound

let rec head_bound env sigma t = match EConstr.kind sigma t with
| Prod (_, _, b)  -> head_bound env sigma b
| LetIn (_, _, _, b) -> head_bound env sigma b
| App (c, _) -> head_bound env sigma c
| Case (_, _, _, _, _, c, _) -> head_bound env sigma c
| Ind (ind, _) -> GlobRef.IndRef ind
| Const (c, _) -> GlobRef.ConstRef c
| Construct (c, _) -> GlobRef.ConstructRef c
| Var id -> GlobRef.VarRef id
| Proj (p, _, _) -> GlobRef.ConstRef (Environ.projection_repr_constant env (Projection.repr p))
| Cast (c, _, _) -> head_bound env sigma c
| Evar _ | Rel _ | Meta _ | Sort _ | Fix _ | Lambda _
| CoFix _ | Int _ | Float _ | String _ | Array _ -> raise Bound

let head_constr sigma c =
  try head_bound sigma c
  with Bound -> user_err (Pp.str "Head identifier must be a constant, section variable, \
                                  (co)inductive type, (co)inductive type constructor, or projection.")

let decompose_app_bound env sigma t =
  let t = strip_outer_cast sigma t in
  let _,ccl = decompose_prod_decls sigma t in
  let hd,args = decompose_app sigma ccl in
  let open GlobRef in
  match EConstr.kind sigma hd with
    | Const (c,u) -> ConstRef c, args
    | Ind (i,u) -> IndRef i, args
    | Construct (c,u) -> ConstructRef c, args
    | Var id -> VarRef id, args
    | Proj (p, _, c) -> ConstRef (Environ.projection_repr_constant env (Projection.repr p)), Array.cons c args
    | _ -> raise Bound

(** Compute the set of section variables that remain in the named context.
    Starts from the top to the bottom of the context, stops at the first
    different declaration between the named hyps and the section context. *)
let secvars_of_hyps hyps =
  let secctx = Global.named_context () in
  let open Context.Named.Declaration in
  let pred, all =
    List.fold_left (fun (pred,all) decl ->
        if Termops.is_section_variable_sign ~check:false hyps (get_id decl) then
          (Id.Pred.add (get_id decl) pred, all)
        else (pred, false))
      (Id.Pred.empty,true) secctx
  in
  (* NB: this is not just [forall is_secvar hyps] because we need to
     know if secvars have been cleaned *)
  if all then Id.Pred.full (* If the whole section context is available *)
  else pred

let empty_hint_info =
  { hint_priority = None; hint_pattern = None }

(************************************************************************)
(*           The Type of Constructions Autotactic Hints                 *)
(************************************************************************)

module Internal =
struct

type 'a hint_ast =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of Evaluable.t (* Hint Unfold *)
  | Extern of Pattern.constr_pattern option * Gentactic.glob_generic_tactic (* Hint Extern *)

end

open Internal

type 'a hints_path_atom_gen =
  | PathHints of 'a list
  (* For forward hints, their names is the list of projections *)
  | PathAny

type hints_path_atom = GlobRef.t hints_path_atom_gen

type 'a hints_path_gen =
  | PathAtom of 'a hints_path_atom_gen
  | PathStar of 'a hints_path_gen
  | PathSeq of 'a hints_path_gen * 'a hints_path_gen
  | PathOr of 'a hints_path_gen * 'a hints_path_gen
  | PathEmpty
  | PathEpsilon

type pre_hints_path = Libnames.qualid hints_path_gen
type hints_path = GlobRef.t hints_path_gen

module UID :
sig
type t
val compare : t -> t -> int
val fresh_key : unit -> t
val subst : Mod_subst.substitution -> t -> t

module Set : CSig.USetS with type elt = t
module Map : Map.UExtS with type key = t and module Set := Set

end =
struct

include KerName

let fresh_key =
  let id = Summary.ref ~name:"HINT-COUNTER" 0 in
  fun () ->
    let open Summary.Ref in
    let cur = id := !id + 1; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, _) = KerName.repr kn in
    (* We embed the full path of the kernel name in the label so that
       the identifier should be unique. This ensures that including
       two modules together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%i"
      (ModPath.to_string mp) cur)
    in
    KerName.make mp lbl

let subst = subst_kn

end

type 'a with_uid = {
  obj : 'a;
  uid : UID.t;
}

type raw_hint = {
  rhint_term : GlobRef.t puniverses;
  rhint_type : types;
  rhint_uctx : UnivGen.sort_context_set option;
  rhint_arty : int; (* Number of goals generated by the intended tactic *)
}

type hint = {
  hint_term : GlobRef.t puniverses;
  hint_type : types;
  hint_uctx : UnivGen.sort_context_set option; (* None if monomorphic *)
  hint_clnv : Clenv.clausenv;
  hint_arty : int; (* Number of goals generated by the intended tactic *)
}

type hint_pattern =
| DefaultPattern
| ConstrPattern of constr_pattern
| SyntacticPattern of constr_pattern

type ('a,'db) with_metadata =
  { pri     : int
  (** A number lower is higher priority *)
  ; pat     : hint_pattern option
  (** A pattern for the concl of the Goal *)
  ; name    : GlobRef.t option
  (** A potential name to refer to the hint *)
  ; db : 'db
  (** The database from which the hint comes *)
  ; secvars : Id.Pred.t
  (** The set of section variables the hint depends on *)
  ; code    : 'a
  (** the tactic to apply when the concl matches pat *)
  }

type hint_db_name = string

(* db = None for local database (ie built from goal hyps) *)
type full_hint = (hint hint_ast with_uid, hint_db_name option) with_metadata

type hint_entry = GlobRef.t option *
  (raw_hint hint_ast with_uid, unit) with_metadata

type hint_mode =
  | ModeInput (* No evars *)
  | ModeFrozen (* evars are allowed but will never be instantiated by hints *)
  | ModeNoHeadEvar (* No evar at the head *)
  | ModeOutput (* Anything *)

module Modes =
struct
  type t = { modes : hint_mode array list GlobRef.Map_env.t }
  let empty = { modes = GlobRef.Map_env.empty }
  let union m1 m2 = { modes = GlobRef.Map_env.union (fun _ m1 m2 -> Some (m1@m2)) m1.modes m2.modes }
end

type 'a hints_transparency_target =
  | HintsVariables
  | HintsConstants
  | HintsProjections
  | HintsReferences of 'a list

let hint_as_term h = (h.hint_uctx, mkRef h.hint_term)

let pri_order_int (id1, {pri=pri1}) (id2, {pri=pri2}) =
  let d = Int.compare pri1 pri2 in
    if Int.equal d 0 then Int.compare id2 id1
    else d

let get_default_pattern (h : hint hint_ast) = match h with
| Give_exact h -> h.hint_type
| Res_pf h | ERes_pf h | Res_pf_THEN_trivial_fail h ->
  Clenv.clenv_type h.hint_clnv
| Unfold_nth _ | Extern _ ->
  (* These hints cannot contain DefaultPattern *)
  assert false

(* Nov 98 -- Papageno *)
(* Les Hints sont ré-organisés en plusieurs databases.

  La table impérative "searchtable", de type "hint_db_table",
   associe une database (hint_db) à chaque nom.

  Une hint_db est une table d'association fonctionelle constr -> search_entry
  Le constr correspond à la constante de tête de la conclusion.

  Une search_entry est un triplet comprenant :
     - la liste des tactiques qui n'ont pas de pattern associé
     - la liste des tactiques qui ont un pattern
     - un discrimination net borné (Btermdn.t) constitué de tous les
       patterns de la seconde liste de tactiques *)

type stored_data = int * full_hint
    (* First component is the index of insertion in the table, to keep most recent first semantics. *)

module Bounded_net :
sig
  type t
  val empty : TransparentState.t option -> t
  val build : TransparentState.t option -> UID.Set.t -> stored_data UID.Map.t -> t
  val add : t -> hint_pattern -> full_hint -> t
  val lookup : Environ.env -> Evd.evar_map -> t -> EConstr.constr -> UID.t list
end =
struct
  module Bnet = Btermdn.Make(UID)

  type diff = hint_pattern * full_hint

  type data =
  | Bnet of (TransparentState.t option * Bnet.t)
  | Diff of diff * data ref
  | Build of TransparentState.t option * UID.Set.t * stored_data UID.Map.t

  type t = data ref

  let empty st = ref (Bnet (st, Bnet.empty))

  let add net p v = ref (Diff ((p, v), net))

  let build st uids data = ref (Build (st, uids, data))

  let add0 env sigma st p v dn =
    (* Feedback.msg_debug (let v1 = v in Pp.(str "add0: " ++ Pp.pr_opt Names.GlobRef.print (snd v1).name)); *)
    let p = match p with
    | ConstrPattern p -> Bnet.pattern env st p
    | SyntacticPattern p -> Bnet.pattern_syntactic env p
    | DefaultPattern ->
      let c = get_default_pattern v.code.obj in
      Bnet.constr_pattern env sigma st c
    in
    Bnet.add dn p v.code.uid

  let rec force env sigma net = match !net with
  | Bnet dn -> dn
  | Diff ((p, v), rem) ->
    let st, dn = force env sigma rem in
    let dn = add0 env sigma st p v dn in
    let () = net := (Bnet (st, dn)) in
    st, dn
  | Build (st, uids, data) ->
    let fold uid dn =
      let _, v = UID.Map.get uid data in
      add0 env sigma st (Option.get v.pat) v dn
    in
    let ans = UID.Set.fold fold uids Bnet.empty in
    let () = net := Bnet (st, ans) in
    st, ans

  let lookup env sigma net p =
    let st, dn = force env sigma net in
    Bnet.lookup env sigma st dn p
end

module StoredData :
sig
  type t
  val empty : t
  val mem : UID.t -> t -> bool
  val add : UID.t -> t -> t
  val remove : UID.t -> t -> t
  val elements : t -> UID.Set.t
end =
struct

type t = {
  data : UID.Set.t;
}

let empty = { data = UID.Set.empty; }

let mem kn sd = UID.Set.mem kn sd.data

let add t sd = {
  data = UID.Set.add t sd.data;
}

let remove uid sd = {
  data = UID.Set.remove uid sd.data;
}

let elements v = v.data

end

type search_entry = {
  sentry_nopat : StoredData.t;
  sentry_pat : StoredData.t;
  sentry_bnet : Bounded_net.t;
  sentry_mode : hint_mode array list;
}

let empty_se st = {
  sentry_nopat = StoredData.empty;
  sentry_pat = StoredData.empty;
  sentry_bnet = Bounded_net.empty st;
  sentry_mode = [];
}

let add_tac pat t se =
  match pat with
  | None ->
    let uid = t.code.uid in
    if StoredData.mem uid se.sentry_nopat then se
    else { se with sentry_nopat = StoredData.add uid se.sentry_nopat }
  | Some pat ->
    let uid = t.code.uid in
    if StoredData.mem uid se.sentry_pat then se
    else { se with
        sentry_pat = StoredData.add uid se.sentry_pat;
        sentry_bnet = Bounded_net.add se.sentry_bnet pat t; }

let rebuild_dn st data se =
  let dn' = Bounded_net.build st (StoredData.elements se.sentry_pat) data in
  { se with sentry_bnet = dn' }

let merge_set data s l =
  let map uid = UID.Map.get uid data in
  let elt = List.map map (UID.Set.elements s) in
  let elt = List.stable_sort pri_order_int elt in
  List.merge pri_order_int elt l

let lookup_tacs env sigma concl data se =
  let l' = Bounded_net.lookup env sigma se.sentry_bnet concl in
  let map uid = UID.Map.get uid data in
  let l' = List.map map l' in
  let sl' = List.stable_sort pri_order_int l' in
  merge_set data (StoredData.elements se.sentry_nopat) sl'

let merge_context_set_opt sigma ctx = match ctx with
| None -> sigma
| Some ctx -> Evd.merge_sort_context_set Evd.univ_flexible ~src:UState.Internal sigma ctx

let instantiate_hint env sigma p =
  let mk_clenv { rhint_term = c; rhint_type = cty; rhint_uctx = ctx; rhint_arty = ar } =
    let sigma = merge_context_set_opt sigma ctx in
    let cl = Clenv.mk_clenv_from env sigma (mkRef c, cty) in
    let cl = Clenv.clenv_strip_proj_params cl in
    { hint_term = c; hint_type = cty; hint_uctx = ctx; hint_clnv = cl; hint_arty = ar }
  in
  let code = match p.code.obj with
    | Res_pf c -> Res_pf (mk_clenv c)
    | ERes_pf c -> ERes_pf (mk_clenv c)
    | Res_pf_THEN_trivial_fail c ->
      Res_pf_THEN_trivial_fail (mk_clenv c)
    | Give_exact c -> Give_exact (mk_clenv c)
    | (Unfold_nth _ | Extern _) as h -> h
  in
  { p with code = { p.code with obj = code } }

let hint_mode_eq m1 m2 = match m1, m2 with
  | ModeInput, ModeInput -> true
  | ModeFrozen, ModeFrozen -> true
  | ModeNoHeadEvar, ModeNoHeadEvar -> true
  | ModeOutput, ModeOutput -> true
  | (ModeInput | ModeFrozen | ModeNoHeadEvar | ModeOutput), _ -> false

let hints_path_atom_eq env h1 h2 = match h1, h2 with
| PathHints l1, PathHints l2 -> List.equal (fun gr1 gr2 -> QGlobRef.equal env gr1 gr2) l1 l2
| PathAny, PathAny -> true
| _ -> false

let rec hints_path_eq env h1 h2 = match h1, h2 with
| PathAtom h1, PathAtom h2 -> hints_path_atom_eq env h1 h2
| PathStar h1, PathStar h2 -> hints_path_eq env h1 h2
| PathSeq (l1, r1), PathSeq (l2, r2) ->
  hints_path_eq env l1 l2 && hints_path_eq env r1 r2
| PathOr (l1, r1), PathOr (l2, r2) ->
  hints_path_eq env l1 l2 && hints_path_eq env r1 r2
| PathEmpty, PathEmpty -> true
| PathEpsilon, PathEpsilon -> true
| _ -> false

let path_matches env hp hints =
  let rec aux hp hints k =
    match hp, hints with
    | PathAtom _, [] -> false
    | PathAtom PathAny, (_ :: hints') -> k hints'
    | PathAtom p, (h :: hints') ->
      if hints_path_atom_eq env p h then k hints' else false
    | PathStar hp', hints ->
      k hints || aux hp' hints (fun hints' -> aux hp hints' k)
    | PathSeq (hp, hp'), hints ->
      aux hp hints (fun hints' -> aux hp' hints' k)
    | PathOr (hp, hp'), hints ->
      aux hp hints k || aux hp' hints k
    | PathEmpty, _ -> false
    | PathEpsilon, hints -> k hints
  in aux hp hints (fun hints' -> true)

let rec matches_epsilon = function
  | PathAtom _ -> false
  | PathStar _ -> true
  | PathSeq (p, p') -> matches_epsilon p && matches_epsilon p'
  | PathOr (p, p') -> matches_epsilon p || matches_epsilon p'
  | PathEmpty -> false
  | PathEpsilon -> true

let path_matches_epsilon = matches_epsilon

let rec is_empty = function
  | PathAtom _ -> false
  | PathStar _ -> false
  | PathSeq (p, p') -> is_empty p || is_empty p'
  | PathOr (p, p') -> matches_epsilon p && matches_epsilon p'
  | PathEmpty -> true
  | PathEpsilon -> false

let path_seq p p' =
  match p, p' with
  | PathEpsilon, p' -> p'
  | p, PathEpsilon -> p
  | p, p' -> PathSeq (p, p')

let rec path_derivate env hp hint =
  let rec derivate_atoms env hints hints' =
    match hints, hints' with
    | gr :: grs, gr' :: grs' when QGlobRef.equal env gr gr' -> derivate_atoms env grs grs'
    | [], [] -> PathEpsilon
    | [], hints -> PathEmpty
    | grs, [] -> PathAtom (PathHints grs)
    | _, _ -> PathEmpty
  in
  match hp with
  | PathAtom PathAny -> PathEpsilon
  | PathAtom (PathHints grs) ->
     (match grs, hint with
      | h :: _, PathAny -> PathEmpty
      | hints, PathHints hints' -> derivate_atoms env hints hints'
      | _, _ -> assert false)
  | PathStar p -> if path_matches env p [hint] then hp else PathEpsilon
  | PathSeq (hp, hp') ->
     let hpder = path_derivate env hp hint in
     if matches_epsilon hp then
       PathOr (path_seq hpder hp', path_derivate env hp' hint)
     else if is_empty hpder then PathEmpty
     else path_seq hpder hp'
  | PathOr (hp, hp') ->
     PathOr (path_derivate env hp hint, path_derivate env hp' hint)
  | PathEmpty -> PathEmpty
  | PathEpsilon -> PathEmpty

let rec normalize_path env h =
  match h with
  | PathStar PathEpsilon -> PathEpsilon
  | PathOr (p, q) ->
    (match normalize_path env p with
     | PathEmpty -> normalize_path env q
     | p' ->
     match normalize_path env q with
     | PathEmpty -> p'
     | q' -> if hints_path_eq env p' q' then p' else PathOr (p', q'))
  | PathSeq (p, q) ->
    (match normalize_path env p with
     | PathEmpty -> PathEmpty
     | PathEpsilon -> normalize_path env q
     | p' ->
     match normalize_path env q with
     | PathEmpty -> PathEmpty
     | PathEpsilon -> p'
     | q' -> PathSeq (p', q'))
  | _ -> h

let path_derivate env hp hint =
  let hint = match hint with
  | None -> PathAny
  | Some gr -> PathHints [gr]
  in
  normalize_path env (path_derivate env hp hint)

let pp_hints_path_atom prg a =
  match a with
  | PathAny -> str"_"
  | PathHints grs -> pr_sequence prg grs

let pp_hints_path_gen prg =
  let rec aux = function
    | PathAtom pa -> pp_hints_path_atom prg pa
    | PathStar (PathAtom PathAny) -> str"_*"
    | PathStar p -> str "(" ++ aux p ++ str")*"
    | PathSeq (p, p') -> aux p ++ spc () ++ aux p'
    | PathOr (p, p') ->
     str "(" ++ aux p ++ spc () ++ str"|" ++ cut () ++ spc () ++
     aux p' ++ str ")"
  | PathEmpty -> str"emp"
  | PathEpsilon -> str"eps"
  in aux

let pp_hints_path = pp_hints_path_gen pr_global

let glob_hints_path_atom p =
  match p with
  | PathHints g -> PathHints (List.map Nametab.global g)
  | PathAny -> PathAny

let glob_hints_path =
  let rec aux = function
    | PathAtom pa -> PathAtom (glob_hints_path_atom pa)
    | PathStar p -> PathStar (aux p)
    | PathSeq (p, p') -> PathSeq (aux p, aux p')
    | PathOr (p, p') -> PathOr (aux p, aux p')
    | PathEmpty -> PathEmpty
    | PathEpsilon -> PathEpsilon
  in aux

let subst_path_atom subst p =
  match p with
  | PathAny -> p
  | PathHints grs ->
    let gr' gr = fst (subst_global subst gr) in
    let grs' = List.Smart.map gr' grs in
      if grs' == grs then p else PathHints grs'

let rec subst_hints_path subst hp =
  match hp with
  | PathAtom p ->
    let p' = subst_path_atom subst p in
      if p' == p then hp else PathAtom p'
  | PathStar p -> let p' = subst_hints_path subst p in
      if p' == p then hp else PathStar p'
  | PathSeq (p, q) ->
    let p' = subst_hints_path subst p in
    let q' = subst_hints_path subst q in
      if p' == p && q' == q then hp else PathSeq (p', q')
  | PathOr (p, q) ->
    let p' = subst_hints_path subst p in
    let q' = subst_hints_path subst q in
      if p' == p && q' == q then hp else PathOr (p', q')
  | _ -> hp

type mode_match =
  | NoMode
  | WithMode of Evarsolve.AllowedEvars.t

type mode_restriction = {
  mode_match : mode_match;
  mode_frozen_evars : Evar.Set.t;
}

type 'a with_mode =
  | ModeMatch of mode_match * 'a
  | ModeMismatch

module Hint_db :
sig
type t
val empty : ?name:hint_db_name -> TransparentState.t -> bool -> t
val map_none : secvars:Id.Pred.t -> t -> full_hint list
val map_all : Environ.env -> secvars:Id.Pred.t -> GlobRef.t -> t -> full_hint list
val map_eauto : Environ.env -> evar_map -> secvars:Id.Pred.t ->
                (GlobRef.t * constr array) -> constr -> t -> full_hint list with_mode
val map_eauto_modes : Environ.env -> evar_map -> secvars:Id.Pred.t ->
                (GlobRef.t * constr array) -> constr -> t ->
                (mode_restriction list * full_hint list) option
val map_auto : Environ.env -> evar_map -> secvars:Id.Pred.t ->
               (GlobRef.t * constr array) -> constr -> t -> full_hint list
val add_list : env -> evar_map -> hint_entry list -> t -> t
val remove_one : Environ.env -> GlobRef.t -> t -> t
val remove_list : Environ.env -> GlobRef.t list -> t -> t
val iter : (GlobRef.t option -> hint_mode array list -> full_hint list -> unit) -> t -> unit
val use_dn : t -> bool
val transparent_state : t -> TransparentState.t
val set_transparent_state : t -> TransparentState.t -> t
val add_cut : Environ.env -> hints_path -> t -> t
val add_mode : Environ.env -> GlobRef.t -> hint_mode array -> t -> t
val cut : t -> hints_path
val unfolds : t -> Id.Set.t * Cset_env.t * PRset_env.t
val add_modes : Modes.t -> t -> t
val modes : t -> Modes.t
val find_mode : env -> GlobRef.t -> t -> hint_mode array list
val fold : (GlobRef.t option -> hint_mode array list -> full_hint list -> 'a -> 'a) ->
  t -> 'a -> 'a
end =
struct

  type t = {
    hintdb_state : TransparentState.t;
    hintdb_cut : hints_path;
    hintdb_unfolds : Id.Set.t * Cset_env.t * PRset_env.t;
    hintdb_max_id : int;
    use_dn : bool;
    hintdb_map : search_entry GlobRef.Map_env.t;
    (* A list of unindexed entries with no associated pattern. *)
    hintdb_nopat : UID.Set.t;
    hintdb_name : string option;
    hintdb_data : stored_data UID.Map.t; (* insertion index, hint with uid = key *)
    hintdb_names : UID.Set.t GlobRef.Map_env.t;
  }

  let next_hint_id db =
    let h = db.hintdb_max_id in
    { db with hintdb_max_id = succ db.hintdb_max_id }, h

  let empty ?name st use_dn = { hintdb_state = st;
                          hintdb_cut = PathEmpty;
                          hintdb_unfolds = (Id.Set.empty, Cset_env.empty, PRset_env.empty);
                          hintdb_max_id = 0;
                          use_dn = use_dn;
                          hintdb_map = GlobRef.Map_env.empty;
                          hintdb_nopat = UID.Set.empty;
                          hintdb_name = name;
                          hintdb_data = UID.Map.empty;
                          hintdb_names = GlobRef.Map_env.empty; }

  let dn_ts db = if db.use_dn then (Some db.hintdb_state) else None

  let find0 key db =
    (* We assume here that key is canonical at this point. *)
    try GlobRef.Map_env.find key db.hintdb_map
    with Not_found -> empty_se (dn_ts db)

  let find env key db =
    let key = QGlobRef.canonize env key in
    find0 key db

  let realize_tac secvars (id,tac) =
    if Id.Pred.subset tac.secvars secvars then Some tac
    else
      (* Warn about no longer typable hint? *)
      None

  let has_no_head_evar sigma c =
    let rec hrec c = match EConstr.kind sigma c with
      | Evar (evk,_)   -> false
      | App (c,_)      -> hrec c
      | Cast (c,_,_)   -> hrec c
      | _              -> true
    in
    hrec c

  let matches_mode sigma args mode =
    if Array.length mode == Array.length args then
      let exception Mismatch in
      begin try
        (* Forbid all evars appearing in arguments with [ModeFrozen],
           unconditionally, even when they appear in other arguments. *)
        let f forbid m arg =
          match m with
          | ModeNoHeadEvar when not (has_no_head_evar sigma arg) -> raise Mismatch
          | ModeInput when occur_existential sigma arg -> raise Mismatch
          | ModeFrozen -> Evar.Set.union forbid (Evd.evars_of_term sigma arg)
          | ModeNoHeadEvar | ModeInput | ModeOutput -> forbid
        in
        Some (Array.fold_left2 f Evar.Set.empty mode args)
      with Mismatch -> None
      end
    else None

  let matches_modes sigma args modes =
    if List.is_empty modes then
      Some [{ mode_match = NoMode; mode_frozen_evars = Evar.Set.empty }]
    else
      (* Modes are alternatives. Keep their restrictions separate: merging the
         sets of allowed evars could permit an application that satisfies none
         of the declared modes. *)
      let rec aux forbids = function
        | [] ->
          let to_restriction forbid =
            let allowed =
              if Evar.Set.is_empty forbid then Evarsolve.AllowedEvars.all
              else Evarsolve.AllowedEvars.except forbid
            in
            { mode_match = WithMode allowed; mode_frozen_evars = forbid }
          in
          List.rev_map to_restriction forbids
        | mode :: modes ->
          match matches_mode sigma args mode with
          | None -> aux forbids modes
          | Some forbid ->
            if List.exists (Evar.Set.equal forbid) forbids then aux forbids modes
            else aux (forbid :: forbids) modes
      in
      match aux [] modes with
      | [] -> None
      | modes -> Some modes

  let merge_entry secvars db nopat pat =
    let fold uid accu = UID.Map.get uid db.hintdb_data :: accu in
    let h = List.sort pri_order_int (UID.Set.fold fold db.hintdb_nopat []) in
    let h = List.merge pri_order_int h nopat in
    let h = List.merge pri_order_int h pat in
    List.map_filter (realize_tac secvars) h

  let map_none ~secvars db =
    merge_entry secvars db [] []

  let map_all env ~secvars k db =
    let se = find env k db in
    let data = db.hintdb_data in
    let fold uid accu = UID.Map.get uid db.hintdb_data :: accu in
    let h = List.sort pri_order_int (UID.Set.fold fold db.hintdb_nopat []) in
    let h = merge_set data (StoredData.elements se.sentry_nopat) h in
    let h = merge_set data (StoredData.elements se.sentry_pat) h in
    List.map_filter (realize_tac secvars) h

  (* Precondition: concl has no existentials *)
  let map_auto env sigma ~secvars (k,args) concl db =
    let se = find env k db in
    let pat = lookup_tacs env sigma concl db.hintdb_data se in
    merge_entry secvars db [] pat

  (* [c] contains an existential *)
  let map_eauto_modes env sigma ~secvars (k,args) concl db =
    let se = find env k db in
    match matches_modes sigma args se.sentry_mode with
    | Some modes ->
      let pat = lookup_tacs env sigma concl db.hintdb_data se in
      Some (modes, merge_entry secvars db [] pat)
    | None -> None

  let map_eauto env sigma ~secvars hdc concl db =
    match map_eauto_modes env sigma ~secvars hdc concl db with
    | Some ({ mode_match } :: _, hints) -> ModeMatch (mode_match, hints)
    | Some ([], _) -> assert false
    | None -> ModeMismatch

  let is_exact = function
    | Give_exact _ -> true
    | _ -> false

  (* gr must be canonical *)
  let addkv env gr id v db =
    let idv = { v with db = db.hintdb_name } in
    let hintdb_data =
      (* XXX this is a hack for backwards compatibility, we should refresh the
         insertion order to implement a properly scoped Import behaviour *)
      if UID.Map.mem v.code.uid db.hintdb_data then db.hintdb_data
      else UID.Map.add v.code.uid (id, idv) db.hintdb_data
    in
    let hintdb_names = match v.name with
    | None -> db.hintdb_names
    | Some name ->
      let name = QGlobRef.canonize env name in
      let old = match GlobRef.Map_env.find_opt name db.hintdb_names with
      | None -> UID.Set.empty
      | Some old -> old
      in
      let map = UID.Set.add v.code.uid old in
      GlobRef.Map_env.add name map db.hintdb_names
    in
    match gr with
    | None ->
      if not (UID.Set.mem v.code.uid db.hintdb_nopat) then
        { db with hintdb_nopat = UID.Set.add v.code.uid db.hintdb_nopat; hintdb_data; hintdb_names }
      else db
    | Some gr ->
      let pat =
        if not db.use_dn && is_exact v.code.obj then None
        else v.pat
      in
      let oval = find0 gr db in
      { db with hintdb_map = GlobRef.Map_env.add gr (add_tac pat idv oval) db.hintdb_map; hintdb_data; hintdb_names }

  let rebuild_db st' db =
    let db' =
      let map se = rebuild_dn (Some st') db.hintdb_data se in
      { db with hintdb_map = GlobRef.Map_env.map map db.hintdb_map; hintdb_state = st'; hintdb_nopat = UID.Set.empty }
    in
    let fold id db =
      if not (UID.Set.mem id db.hintdb_nopat) then
        { db with hintdb_nopat = UID.Set.add id db.hintdb_nopat }
      else db
    in
    UID.Set.fold fold db.hintdb_nopat db'

  let add_one env sigma (k, v) db =
    let v = instantiate_hint env sigma v in
    let db = match v.code.obj with
    | Unfold_nth egr ->
      let open TransparentState in
      let ts = db.hintdb_state in
      let (ids, csts, prjs) = db.hintdb_unfolds in
      let state, unfs = match egr with
      | Evaluable.EvalVarRef id ->
        { ts with tr_var = Id.Pred.add id ts.tr_var }, (Id.Set.add id ids, csts, prjs)
      | Evaluable.EvalConstRef cst ->
        (* TODO: do we really want to canonize? *)
        let cst = QConstant.canonize env cst in
        { ts with tr_cst = Cpred.add cst ts.tr_cst }, (ids, Cset_env.add cst csts, prjs)
      | Evaluable.EvalProjectionRef p ->
        (* TODO: do we really want to canonize? *)
        let p = QProjection.Repr.canonize env p in
        { ts with tr_prj = PRpred.add p ts.tr_prj }, (ids, csts, PRset_env.add p prjs)
      in
      let db = { db with hintdb_unfolds = unfs } in
      if db.use_dn then rebuild_db state db else db
    | _ -> db
    in
    let db, id = next_hint_id db in
    let k = Option.map (fun gr -> QGlobRef.canonize env gr) k in
    addkv env k id v db

  let add_list env sigma l db = List.fold_left (fun db k -> add_one env sigma k db) db l

  let remove env st uids data se =
    let fold uid accu = StoredData.remove uid accu in
    let nopat = UID.Set.fold fold uids se.sentry_nopat in
    let pat = UID.Set.fold fold uids se.sentry_pat in
    if pat == se.sentry_pat && nopat == se.sentry_nopat then se
    else
      let se = { se with sentry_nopat = nopat; sentry_pat = pat } in
      rebuild_dn st data se

  let remove_list env grs db =
    let fold (grs, uids) gr =
      let gr = Environ.QGlobRef.canonize env gr in
      let uids  = match GlobRef.Map_env.find_opt gr db.hintdb_names with
      | None -> uids
      | Some uids' -> UID.Set.union uids' uids
      in
      (GlobRef.Set_env.add gr grs, uids)
    in
    let (grs, uids) = List.fold_left fold (GlobRef.Set_env.empty, UID.Set.empty) grs in
    let hintdb_map = GlobRef.Map_env.map (fun se -> remove env (dn_ts db) uids db.hintdb_data se) db.hintdb_map in
    let hintdb_nopat = UID.Set.diff db.hintdb_nopat uids in
    let fold uid accu = UID.Map.remove uid accu in
    let hintdb_data = UID.Set.fold fold uids db.hintdb_data in
    let fold gr accu = GlobRef.Map_env.remove gr accu in
    let hintdb_names = GlobRef.Set_env.fold fold grs db.hintdb_names in
    { db with hintdb_map; hintdb_nopat; hintdb_data; hintdb_names }

  let remove_one env gr db = remove_list env [gr] db

  let get_entry data se =
    let h = merge_set data (StoredData.elements se.sentry_nopat) (merge_set data (StoredData.elements se.sentry_pat) []) in
    List.map snd h

  let iter f db =
    let iter_se k se = f (Some k) se.sentry_mode (get_entry db.hintdb_data se) in
    let fold uid accu = snd (UID.Map.get uid db.hintdb_data) :: accu in
    let () = f None [] (UID.Set.fold fold db.hintdb_nopat []) in
    GlobRef.Map_env.iter iter_se db.hintdb_map

  let fold f db accu =
    let fold uid accu = snd (UID.Map.get uid db.hintdb_data) :: accu in
    let accu = f None [] (UID.Set.fold fold db.hintdb_nopat []) accu in
    GlobRef.Map_env.fold (fun k se -> f (Some k) se.sentry_mode (get_entry db.hintdb_data se)) db.hintdb_map accu

  let transparent_state db = db.hintdb_state

  let set_transparent_state db st =
    if db.use_dn then rebuild_db st db
    else { db with hintdb_state = st }

  let add_cut env path db =
    { db with hintdb_cut = normalize_path env (PathOr (db.hintdb_cut, path)) }

  let add_mode env gr m db =
    let se = find env gr db in
    let se = { se with sentry_mode = m :: List.remove (Array.equal hint_mode_eq) m se.sentry_mode } in
    { db with hintdb_map = GlobRef.Map_env.add gr se db.hintdb_map }

  let cut db = db.hintdb_cut

  let unfolds db = db.hintdb_unfolds

  let add_modes modes db =
    let f gr e me =
      Some { e with sentry_mode = me.sentry_mode @ e.sentry_mode }
    in
    let mode_entries = GlobRef.Map_env.map (fun m -> { (empty_se (dn_ts db)) with sentry_mode = m }) modes.Modes.modes in
    { db with hintdb_map = GlobRef.Map_env.union f db.hintdb_map mode_entries }

  let modes db = { Modes.modes = GlobRef.Map_env.map (fun se -> se.sentry_mode) db.hintdb_map }

  let find_mode _env gr db = (GlobRef.Map_env.find gr db.hintdb_map).sentry_mode

  let use_dn db = db.use_dn

end

module Hintdbmap = String.Map

type hint_db = Hint_db.t

let searchtable = Summary.ref ~name:"searchtable" Hintdbmap.empty

let searchtable_map name =
  let open Summary.Ref in
  Hintdbmap.find name !searchtable
let searchtable_add (name, db) =
  let open Summary.Ref in
  (* XXX see #21114 *)
(*   let () = assert (Hintdbmap.mem name !searchtable) in *)
  searchtable := Hintdbmap.add name db !searchtable
let searchtable_create (name, db) =
  let open Summary.Ref in
(*   let () = assert (not @@ Hintdbmap.mem name !searchtable) in *)
  searchtable := Hintdbmap.add name db !searchtable
let current_db_names () =
  let open Summary.Ref in
  Hintdbmap.domain !searchtable
let current_db () =
  let open Summary.Ref in
  Hintdbmap.bindings !searchtable

let current_pure_db () = List.map snd (current_db ())

let error_no_such_hint_database x =
  user_err (str "No such Hint database: " ++ str x ++ str ".")

(**************************************************************************)
(*             Auxiliary functions to prepare AUTOHINT objects            *)
(**************************************************************************)

(* adding and removing tactics in the search table *)

let with_uid c = { obj = c; uid = UID.fresh_key () }

(* if [x] is a local variable sharing a name with a cleared section
   variable, [secvars_of_global _ (VarRef x)] should return the empty set *)
let secvars_of_idset env s =
  Id.Set.fold (fun id p ->
      if is_section_variable_env env id then
        Id.Pred.add id p
      else p) s Id.Pred.empty

let secvars_of_global env gr =
  secvars_of_idset env (vars_of_global env gr)

let fresh_global_hint env sigma gr =
  let (c, ctx) = UnivGen.fresh_global_instance env gr in
  let _, u = Constr.destRef c in
  let u = EInstance.make u in
  let ctx = if Environ.is_polymorphic env gr then Some ctx else None in
  let cty = Retyping.get_type_of env sigma (mkRef (gr, u)) in
  ((gr, u), cty, ctx)

let make_exact_entry env sigma info gr =
  let (c, cty, ctx) = fresh_global_hint env sigma gr in
  let secvars = secvars_of_global env gr in
  let cty = strip_outer_cast sigma cty in
    match EConstr.kind sigma cty with
    | Prod _ -> failwith "make_exact_entry"
    | _ ->
        let hd =
          try head_bound env sigma cty
          with Bound -> failwith "make_exact_entry"
        in
        let pri = match info.hint_priority with None -> 0 | Some p -> p in
        let pat = match info.hint_pattern with
        | Some pat -> ConstrPattern (snd pat)
        | None -> DefaultPattern
        in
        let h = { rhint_term = c; rhint_type = cty; rhint_uctx = ctx; rhint_arty = 0 } in
        (Some hd,
         { pri; pat = Some pat; name = Some gr;
           db = (); secvars;
           code = with_uid (Give_exact h); })

let make_apply_entry env sigma hnf info gr =
  let (c, cty, ctx) = fresh_global_hint env sigma gr in
  let cty = if hnf then hnf_constr0 env sigma cty else cty in
  match EConstr.kind sigma cty with
  | Prod _ ->
    let cty = if hnf then Reductionops.nf_betaiota env sigma cty else cty in
    let sigma' = merge_context_set_opt sigma ctx in
    let ce = Clenv.mk_clenv_from env sigma' (mkRef c, cty) in
    let c' = Clenv.clenv_type (* ~reduce:false *) ce in
    let hd =
      try head_bound env (Clenv.clenv_evd ce) c'
      with Bound -> failwith "make_apply_entry" in
    let miss, hyps = Clenv.clenv_missing ce in
    let nmiss = List.length miss in
    let secvars = secvars_of_global env (fst c) in
    let pri = match info.hint_priority with None -> hyps + nmiss | Some p -> p in
    let pat = match info.hint_pattern with
    | Some p -> ConstrPattern (snd p)
    | None -> DefaultPattern
    in
    let h = { rhint_term = c; rhint_type = cty; rhint_uctx = ctx; rhint_arty = hyps; } in
    if Int.equal nmiss 0 then
      (Some hd,
       { pri; pat = Some pat; name = Some gr;
         db = ();
         secvars;
         code = with_uid (Res_pf h); })
    else
      (Some hd,
       { pri; pat = Some pat; name = Some gr;
         db = (); secvars;
         code = with_uid (ERes_pf h); })
  | _ -> failwith "make_apply_entry"

(* flags is (e,h,v) with e=true if eapply and h=true if hnf and v=true if verbose
   c is a constr
   cty is the type of constr *)

let make_resolves env sigma (eapply, hnf) info ~check cr =
  let try_apply f =
    try
      let (_, hint) as ans = f cr in
      match hint.code.obj with
      | ERes_pf _ -> if not eapply then None else Some ans
      | _ -> Some ans
    with Failure _ -> None
  in
  let ents = List.map_filter try_apply
                             [make_exact_entry env sigma info;
                              make_apply_entry env sigma hnf info]
  in
  if check && List.is_empty ents then
    user_err
      (Printer.pr_global cr ++ spc() ++
        (if eapply then str"cannot be used as a hint."
        else str "can be used as a hint only for eauto."));
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma hname =
  try
    [make_apply_entry env sigma true empty_hint_info (GlobRef.VarRef hname)]
  with
    | Failure _ -> []
    | e when noncritical e -> anomaly (Pp.str "make_resolve_hyp.")

(* REM : in most cases hintname = id *)

let make_unfold env eref =
  let g = global_of_evaluable_reference env eref in
  (Some g,
   { pri = 4;
     pat = None;
     name = Some g;
     db = ();
     secvars = secvars_of_global env g;
     code = with_uid (Unfold_nth eref) })

let make_extern pri pat tacast =
  let hdconstr = match pat with
  | None -> None
  | Some c ->
    try Some (head_pattern_bound c)
    with BoundPattern ->
      user_err (Pp.str "Head pattern or sub-pattern must be a global constant, a section variable, \
                        an if, case, or let expression, an application, or a projection.")
  in
  (hdconstr,
   { pri = pri;
     pat = Option.map (fun p -> SyntacticPattern p) pat;
     name = None;
     db = ();
     secvars = Id.Pred.empty; (* Approximation *)
     code = with_uid (Extern (pat, tacast)) })

let make_mode ref m =
  let open Term in
  let ty, _ = Typeops.type_of_global_in_context (Global.env ()) ref in
  let ctx, t = decompose_prod_decls ty in
  let n = Context.Rel.nhyps ctx in
  let m' = Array.of_list m in
    if not (n == Array.length m') then
      user_err
        (pr_global ref ++ str" has " ++ int n ++
           str" arguments while the mode declares " ++ int (Array.length m') ++ str ".")
    else m'

let make_trivial env sigma r =
  let c, cty, ctx = fresh_global_hint env sigma r in
  let sigma = merge_context_set_opt sigma ctx in
  let t = hnf_constr env sigma cty in
  let hd = head_constr env sigma t in
  let h = { rhint_term = c; rhint_type = t; rhint_uctx = ctx; rhint_arty = 0 } in
  (Some hd,
   { pri=1;
     pat = Some DefaultPattern;
     name = Some r;
     db = ();
     secvars = secvars_of_global env r;
     code= with_uid (Res_pf_THEN_trivial_fail h) })



(**************************************************************************)
(*               declaration of the AUTOHINT library object               *)
(**************************************************************************)

(* If the database does not exist, it is created *)
(* TODO: should a warning be printed in this case ?? *)

let get_db dbname =
  try searchtable_map dbname
  with Not_found -> Hint_db.empty ~name:dbname TransparentState.empty false

let add_hint dbname hintlist =
  let db = get_db dbname in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let db' = Hint_db.add_list env sigma hintlist db in
  searchtable_add (dbname, db')

let add_transparency dbname target b =
  let open TransparentState in
  let db = get_db dbname in
  let st = Hint_db.transparent_state db in
  let st' =
    match target with
    | HintsVariables -> { st with tr_var = (if b then Id.Pred.full else Id.Pred.empty) }
    | HintsConstants -> { st with tr_cst = (if b then Cpred.full else Cpred.empty) }
    | HintsProjections -> { st with tr_prj = (if b then PRpred.full else PRpred.empty) }
    | HintsReferences grs ->
      List.fold_left (fun st gr ->
        match gr with
        | Evaluable.EvalConstRef c -> { st with tr_cst = (if b then Cpred.add else Cpred.remove) c st.tr_cst }
        | Evaluable.EvalVarRef v -> { st with tr_var = (if b then Id.Pred.add else Id.Pred.remove) v st.tr_var }
        | Evaluable.EvalProjectionRef p -> { st with tr_prj = (if b then PRpred.add else PRpred.remove) p st.tr_prj } )
        st grs
  in
  searchtable_add (dbname, Hint_db.set_transparent_state db st')

let remove_hint dbname grs =
  let env = Global.env () in
  let db = get_db dbname in
  let db' = Hint_db.remove_list env grs db in
  searchtable_add (dbname, db')

let add_cut dbname path =
  let env = Global.env () in
  let db = get_db dbname in
  let db' = Hint_db.add_cut env path db in
  searchtable_add (dbname, db')

let add_mode env dbname l m =
  let db = get_db dbname in
  let db' = Hint_db.add_mode env l m db in
  searchtable_add (dbname, db')

type db_obj = {
  db_local : bool;
  db_name : string;
  db_use_dn : bool;
  db_ts : TransparentState.t;
}

let warn_mismatch_create_hintdb = CWarnings.create ~name:"mismatched-hint-db" ~category:CWarnings.CoreCategories.automation
    Pp.(fun {db_name;db_use_dn} ->
        str "Hint Db " ++ str db_name ++ str " already exists and " ++
        (if db_use_dn then str "is not" else str "is") ++ str " discriminated.")

let cache_db ({db_name=name; db_use_dn=b; db_ts=ts} as o) =
  match searchtable_map name with
  | exception Not_found -> searchtable_create (name, Hint_db.empty ~name ts b)
  | db ->
    (* Explicit DBs start with full TS, implicit DBs start with empty TS
       This should probably be controllable in Create Hint Db,
       otherwise we have to do eg "Create HintDb foo. Hint Constants Opaque : foo."
       and if someone else creates foo and puts some transparency hints they will be overwritten. *)
    if Hint_db.use_dn db <> b then warn_mismatch_create_hintdb o

let load_db _ x = cache_db x

let classify_db db = if db.db_local then Dispose else Substitute

let inDB : db_obj -> obj =
  declare_object {(default_object "AUTOHINT_DB") with
                  cache_function = cache_db;
                  load_function = load_db;
                  subst_function = (fun (_,x) -> x);
                  classify_function = classify_db; }

let create_hint_db l n ts b =
  let hint = {db_local=l; db_name=n; db_use_dn=b; db_ts=ts} in
  Lib.add_leaf (inDB hint)

type hint_action =
  | AddTransparency of {
      grefs : Evaluable.t hints_transparency_target;
      state : bool;
    }
  | AddHints of hint_entry list
  | RemoveHints of GlobRef.t list
  | AddCut of hints_path
  | AddMode of { gref : GlobRef.t; mode : hint_mode array }

type hint_locality = Libobject.locality = Local | Export | SuperGlobal

type hint_obj = {
  hint_local : hint_locality;
  hint_name : string;
  hint_action : hint_action;
}

let is_trivial_action = function
| AddTransparency { grefs } ->
  begin match grefs with
  | HintsVariables | HintsConstants | HintsProjections -> false
  | HintsReferences l -> List.is_empty l
  end
| AddHints l -> List.is_empty l
| RemoveHints l -> List.is_empty l
| AddCut _ | AddMode _ -> false

let rec is_section_path = function
| PathAtom PathAny -> false
| PathAtom (PathHints grs) ->
  let check c = isVarRef c && Global.is_in_section c in
  List.exists check grs
| PathStar p -> is_section_path p
| PathSeq (p, q) | PathOr (p, q) -> is_section_path p || is_section_path q
| PathEmpty | PathEpsilon -> false

let superglobal h = match h.hint_local with
  | SuperGlobal -> true
  | Local | Export -> false

let load_autohint _ h =
  let name = h.hint_name in
  let superglobal = superglobal h in
  match h.hint_action with
  | AddTransparency { grefs; state } ->
    if superglobal then add_transparency name grefs state
  | AddHints hints ->
    if superglobal then add_hint name hints
  | RemoveHints hints ->
    if superglobal then remove_hint name hints
  | AddCut paths ->
    if superglobal then add_cut name paths
  | AddMode { gref; mode } ->
    if superglobal then add_mode (Global.env ()) name gref mode

let open_autohint h =
  let superglobal = superglobal h in
  match h.hint_action with
  | AddHints hints ->
    if not superglobal then add_hint h.hint_name hints
  | AddCut paths ->
    if not superglobal then add_cut h.hint_name paths
  | AddTransparency { grefs; state } ->
    if not superglobal then add_transparency h.hint_name grefs state
  | RemoveHints hints ->
    if not superglobal then remove_hint h.hint_name hints
  | AddMode { gref; mode } ->
    if not superglobal then add_mode (Global.env ()) h.hint_name gref mode

let cache_autohint o =
  load_autohint 1 o; open_autohint o

let subst_autohint (subst, obj) =
  let subst_key gr =
    let (gr', t) = subst_global subst gr in
    match t with
    | None -> gr'
    | Some t ->
      (try head_bound (Global.env ()) Evd.empty (EConstr.of_constr t.UVars.univ_abstracted_value)
       with Bound -> gr')
  in
  let subst_mps subst c = EConstr.of_constr (subst_mps subst (EConstr.Unsafe.to_constr c)) in
  let subst_aux ({ rhint_term = (gr, u); rhint_type = t; rhint_uctx = ctx; rhint_arty = ar } as h) =
    let gr' = subst_global_reference subst gr in
    let t' = subst_mps subst t in
    if gr==gr' && t'==t then h else { rhint_term = (gr', u); rhint_type = t'; rhint_uctx = ctx; rhint_arty = ar }
  in
  let subst_hint (k,data as hint) =
    let k' = Option.Smart.map subst_key k in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let subst_hint_pattern = function
    | DefaultPattern -> DefaultPattern
    | ConstrPattern p as p0 ->
      let p' = subst_pattern env sigma subst p in
      if p' == p then p0 else ConstrPattern p'
    | SyntacticPattern p as p0 ->
      let p' = subst_pattern env sigma subst p in
      if p' == p then p0 else SyntacticPattern p'
    in
    let pat' = Option.Smart.map subst_hint_pattern data.pat in
    let code' = match data.code.obj with
      | Res_pf h ->
        let h' = subst_aux h in
        if h == h' then data.code.obj else Res_pf h'
      | ERes_pf h ->
        let h' = subst_aux h in
        if h == h' then data.code.obj else ERes_pf h'
      | Give_exact h ->
        let h' = subst_aux h in
        if h == h' then data.code.obj else Give_exact h'
      | Res_pf_THEN_trivial_fail h ->
        let h' = subst_aux h in
        if h == h' then data.code.obj else Res_pf_THEN_trivial_fail h'
      | Unfold_nth ref ->
          let ref' = subst_evaluable_reference subst ref in
          if ref==ref' then data.code.obj else Unfold_nth ref'
      | Extern (pat, tac) ->
          let pat' = Option.Smart.map (subst_pattern env sigma subst) pat in
          let tac' = Gentactic.subst subst tac in
          if pat==pat' && tac==tac' then data.code.obj else Extern (pat', tac')
    in
    let name' = Option.Smart.map (subst_global_reference subst) data.name in
    let uid' = UID.subst subst data.code.uid in
    let data' =
      if data.code.uid == uid' && data.pat == pat' &&
        data.name == name' && data.code.obj == code' then data
      else { data with pat = pat'; name = name'; code = { obj = code'; uid = uid' } }
    in
    if k' == k && data' == data then hint else (k',data')
  in
  let action = match obj.hint_action with
    | AddTransparency { grefs = target; state = b } ->
      let target' =
        match target with
        | HintsVariables -> target
        | HintsConstants -> target
        | HintsProjections -> target
        | HintsReferences grs ->
          let grs' = List.Smart.map (subst_evaluable_reference subst) grs in
          if grs == grs' then target
          else HintsReferences grs'
      in
      if target' == target then obj.hint_action else AddTransparency { grefs = target'; state = b }
    | AddHints hints ->
      let hints' = List.Smart.map subst_hint hints in
      if hints' == hints then obj.hint_action else AddHints hints'
    | RemoveHints grs ->
      let grs' = List.Smart.map (subst_global_reference subst) grs in
      if grs == grs' then obj.hint_action else RemoveHints grs'
    | AddCut path ->
      let path' = subst_hints_path subst path in
      if path' == path then obj.hint_action else AddCut path'
    | AddMode { gref = l; mode = m } ->
      let l' = subst_global_reference subst l in
      if l' == l then obj.hint_action else AddMode { gref = l'; mode = m }
  in
  if action == obj.hint_action then obj else { obj with hint_action = action }

let is_hint_local = function Local -> true | Export | SuperGlobal -> false

let classify_autohint obj =
  if is_hint_local obj.hint_local || is_trivial_action obj.hint_action then Dispose
  else Substitute

let discharge_autohint obj =
  if is_hint_local obj.hint_local then None
  else
    let action = match obj.hint_action with
    | AddTransparency { grefs; state } ->
      let grefs = match grefs with
      | HintsVariables | HintsConstants | HintsProjections -> grefs
      | HintsReferences grs ->
        let filter e = match e with
        | Evaluable.EvalConstRef c -> Some e
        | Evaluable.EvalProjectionRef p ->
          let p = Global.discharge_proj_repr p in
          Some (Evaluable.EvalProjectionRef p)
        | Evaluable.EvalVarRef id ->
          if Global.is_in_section (GlobRef.VarRef id) then None else Some e
        in
        let grs = List.filter_map filter grs in
        HintsReferences grs
      in
      AddTransparency { grefs; state }
    | AddHints _ | RemoveHints _ ->
      (* not supported yet *)
      assert false
    | AddCut path ->
      if is_section_path path then AddHints [] (* dummy *) else obj.hint_action
    | AddMode { gref; mode } ->
      if Global.is_in_section gref then
        if isVarRef gref then AddHints [] (* dummy *)
        else
          let inst = Global.section_instance gref in
          (* Default mode for discharged parameters is output *)
          let mode = Array.append (Array.make (Array.length inst) ModeOutput) mode in
          AddMode { gref; mode }
      else obj.hint_action
    in
    if is_trivial_action action then None
    else Some { obj with hint_action = action }

let hint_cat = create_category "hints"

let inAutoHint : hint_obj -> obj =
  declare_object
    {(default_object "AUTOHINT") with
     cache_function = cache_autohint;
     load_function = load_autohint;
     open_function = simple_open ~cat:hint_cat open_autohint;
     subst_function = subst_autohint;
     classify_function = classify_autohint;
     discharge_function = discharge_autohint;
    }

let check_locality locality =
  let not_local what =
    CErrors.user_err
        Pp.(str "This command does not support the " ++
            str what ++ str " attribute in sections.")
  in
  if Lib.sections_are_opened () then
    match locality with
    | Local -> ()
    | SuperGlobal -> not_local "global"
    | Export -> not_local "export"

let make_hint ~locality name action =
  {
  hint_local = locality;
  hint_name = name;
  hint_action = action;
}

let remove_hints ~locality dbnames grs =
  let () = check_locality locality in
  let dbnames = if List.is_empty dbnames then ["core"] else dbnames in
    List.iter
      (fun dbname ->
        let hint = make_hint ~locality dbname (RemoveHints grs) in
        Lib.add_leaf (inAutoHint hint))
      dbnames

(**************************************************************************)
(*                     The "Hint" vernacular command                      *)
(**************************************************************************)

let add_resolves env sigma clist ~locality dbnames =
  List.iter
    (fun dbname ->
      let r =
        List.flatten (List.map (fun (pri, hnf, gr) ->
          make_resolves env sigma (true, hnf) pri ~check:true gr) clist)
      in
      let check (_, hint) = match hint.code.obj with
      | ERes_pf { rhint_term = c; rhint_type = cty; rhint_uctx = ctx } ->
        let sigma' = merge_context_set_opt sigma ctx in
        let ce = Clenv.mk_clenv_from env sigma' (mkRef c, cty) in
        let miss, _ = Clenv.clenv_missing ce in
        let nmiss = List.length miss in
        let variables = str (CString.plural nmiss "variable") in
        Feedback.msg_info (
          strbrk "The hint " ++
          pr_global (fst c) ++
          strbrk " will only be used by eauto, because applying " ++
          pr_global (fst c) ++
          strbrk " would leave " ++ variables ++ Pp.spc () ++
          Pp.prlist_with_sep Pp.pr_comma Name.print miss ++
          strbrk " as unresolved existential " ++ variables ++ str "."
        )
      | _ -> ()
      in
      let () = if not !Flags.quiet then List.iter check r in
      let hint = make_hint ~locality dbname (AddHints r) in
      Lib.add_leaf (inAutoHint hint))
    dbnames

let add_unfolds env l ~locality dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~locality dbname (AddHints (List.map (fun u -> make_unfold env u) l)) in
      Lib.add_leaf (inAutoHint hint))
    dbnames

let add_cuts l ~locality dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~locality dbname (AddCut l) in
      Lib.add_leaf (inAutoHint hint))
    dbnames

let add_mode l m ~locality dbnames =
  List.iter
    (fun dbname ->
      let m' = make_mode l m in
      let hint = make_hint ~locality dbname (AddMode { gref = l; mode = m' }) in
      Lib.add_leaf (inAutoHint hint))
    dbnames

let add_transparency l b ~locality dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~locality dbname (AddTransparency { grefs = l; state = b }) in
      Lib.add_leaf (inAutoHint hint))
    dbnames

let add_extern info tacast ~locality dbname =
  let pat = match info.hint_pattern with
  | None -> None
  | Some (_, pat) -> Some pat
  in
  let hint = make_hint ~locality dbname
                       (AddHints [make_extern (Option.get info.hint_priority) pat tacast]) in
  Lib.add_leaf (inAutoHint hint)

let add_externs info tacast ~locality dbnames =
  List.iter (add_extern info tacast ~locality) dbnames

let add_trivials env sigma l ~locality dbnames =
  List.iter
    (fun dbname ->
      let l = List.map (fun c -> make_trivial env sigma c) l in
      let hint = make_hint ~locality dbname (AddHints l) in
      Lib.add_leaf (inAutoHint hint))
    dbnames

type hnf = bool

type nonrec hint_info = hint_info

type hints_entry =
  | HintsResolveEntry of (hint_info * hnf * GlobRef.t) list
  | HintsImmediateEntry of GlobRef.t list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of Evaluable.t list
  | HintsTransparencyEntry of Evaluable.t hints_transparency_target * bool
  | HintsModeEntry of GlobRef.t * hint_mode list
  | HintsExternEntry of hint_info * Gentactic.glob_generic_tactic

let warn_non_local_section_hint =
  CWarnings.create ~name:"non-local-section-hint" ~category:CWarnings.CoreCategories.automation
    (fun () -> strbrk "This hint is not local but depends on a section variable. It will disappear when the section is closed.")

let is_notlocal = function
| Local -> false
| Export | SuperGlobal -> true

let add_hints ~locality dbnames h =
  let () = match h with
  | HintsResolveEntry _ | HintsImmediateEntry _ | HintsUnfoldEntry _ | HintsExternEntry _ ->
    check_locality locality
  | HintsTransparencyEntry ((HintsVariables | HintsConstants | HintsProjections), _) -> ()
  | HintsTransparencyEntry (HintsReferences grs, _) ->
    let iter gr =
      let gr = global_of_evaluable_reference (Global.env ()) gr in
      if is_notlocal locality && isVarRef gr && Global.is_in_section gr then warn_non_local_section_hint ()
    in
    List.iter iter grs
  | HintsCutEntry p ->
    if is_notlocal locality && is_section_path p then warn_non_local_section_hint ()
  | HintsModeEntry (gr, _) ->
    if is_notlocal locality && isVarRef gr && Global.is_in_section gr then warn_non_local_section_hint ()
  in
  if String.List.mem "nocore" dbnames then
    user_err Pp.(str "The hint database \"nocore\" is meant to stay empty.");
  assert (not (List.is_empty dbnames));
  let env = Global.env() in
  let sigma = Evd.from_env env in
  match h with
  | HintsResolveEntry lhints -> add_resolves env sigma lhints ~locality dbnames
  | HintsImmediateEntry lhints -> add_trivials env sigma lhints ~locality dbnames
  | HintsCutEntry lhints -> add_cuts lhints ~locality dbnames
  | HintsModeEntry (l,m) -> add_mode l m ~locality dbnames
  | HintsUnfoldEntry lhints -> add_unfolds env lhints ~locality dbnames
  | HintsTransparencyEntry (lhints, b) ->
      add_transparency lhints b ~locality dbnames
  | HintsExternEntry (info, tacexp) ->
      add_externs info tacexp ~locality dbnames

let expand_constructor_hints env sigma lems =
  List.map_append (fun lem ->
    match lem with
    | GlobRef.IndRef ind ->
        List.init (nconstructors env ind)
                  (fun i -> GlobRef.ConstructRef ((ind,i+1)))
    | GlobRef.ConstRef cst -> [GlobRef.ConstRef cst]
    | GlobRef.VarRef id -> [GlobRef.VarRef id]
    | GlobRef.ConstructRef cstr -> [GlobRef.ConstructRef cstr]) lems
(* builds a hint database from a constr signature *)
(* typically used with (lid, ltyp) = pf_hyps_types <some goal> *)

let constructor_hints env sigma eapply lems =
  let lems = expand_constructor_hints env sigma lems in
  List.map_append (fun lem ->
      make_resolves env sigma (eapply, true) empty_hint_info ~check:true lem) lems

let make_local_hint_db env sigma ts eapply lems =
  let sign = EConstr.named_context env in
  let ts = match ts with
    | None -> Hint_db.transparent_state (searchtable_map "core")
    | Some ts -> ts
  in
  let hintlist = List.map_append (fun decl -> make_resolve_hyp env sigma (Named.Declaration.get_id decl)) sign in
  Hint_db.empty ts false
  |> Hint_db.add_list env sigma hintlist
  |> Hint_db.add_list env sigma (constructor_hints env sigma eapply lems)

let make_local_hint_db env sigma ?ts eapply lems =
  make_local_hint_db env sigma ts eapply lems

let make_db_list dbnames =
  let fold (core, nocore) db =
    if String.equal db "core" then (true, nocore)
    else if String.equal db "nocore" then (core, true)
    else (core, nocore)
  in
  let has_core, has_nocore = List.fold_left fold (false, false) dbnames in
  let dbnames = match has_core, has_nocore with
  | true, true -> user_err Pp.(str "The core and nocore databases are mutually exclusive")
  | true, false -> dbnames
  | false, true -> List.remove String.equal "nocore" dbnames
  | false, false -> "core" :: dbnames
  in
  let lookup db =
    try searchtable_map db with Not_found -> error_no_such_hint_database db
  in
  List.map lookup dbnames

let push_resolves env sigma hint db =
  let entries = make_resolves env sigma (true, false) empty_hint_info ~check:false hint in
  Hint_db.add_list env sigma entries db

let push_resolve_hyp env sigma decl db =
  let entries = make_resolve_hyp env sigma decl in
  Hint_db.add_list env sigma entries db

(**************************************************************************)
(*                    Functions for printing the hints                    *)
(**************************************************************************)

let pr_hint_elt env sigma h = pr_global (fst h.hint_term)

let pr_hint env sigma h = match h.obj with
  | Res_pf c -> (str"simple apply " ++ pr_hint_elt env sigma c)
  | ERes_pf c -> (str"simple eapply " ++ pr_hint_elt env sigma c)
  | Give_exact c -> (str"exact " ++ pr_hint_elt env sigma c)
  | Res_pf_THEN_trivial_fail c ->
      (str"simple apply " ++ pr_hint_elt env sigma c ++ str" ; trivial")
  | Unfold_nth c ->
    str"unfold " ++  pr_evaluable_reference env c
  | Extern (_, tac) ->
    str "(*external*) " ++ Gentactic.print_glob env sigma ~level:(LevelLe 0) tac

let pr_default_pattern env sigma = function
| Give_exact h ->
  pr_leconstr_env env sigma h.hint_type
| Res_pf h | ERes_pf h | Res_pf_THEN_trivial_fail h ->
  let sigma, f = Clenv.replace_clenv_metas env sigma h.hint_clnv in
  pr_leconstr_env env sigma (f (Clenv.clenv_type h.hint_clnv))
| Unfold_nth _ | Extern _ ->
  (* These hints cannot contain DefaultPattern *)
  assert false

let pr_id_hint env sigma (id, v) =
  let pr_pat p = match p.pat with
  | None -> mt ()
  | Some (ConstrPattern p | SyntacticPattern p) -> str", pattern " ++ pr_lconstr_pattern_env env sigma p
  | Some DefaultPattern -> str", pattern " ++ (pr_default_pattern env sigma v.code.obj)
  in
  (pr_hint env sigma v.code ++ str" (cost " ++ int v.pri ++ pr_pat v
   ++ str", id " ++ int id ++ str ")")

let pr_hint_list env sigma hintlist =
  (str "  " ++ hov 0 (prlist_with_sep fnl (pr_id_hint env sigma) hintlist) ++ fnl ())

let pr_hints_db env sigma (name,db,hintlist) =
  (str "In the database " ++ str name ++ str ":" ++
     if List.is_empty hintlist then (str " nothing" ++ fnl ())
     else (fnl () ++ pr_hint_list env sigma hintlist))

(* Print all hints associated to head c in any database *)
let pr_hint_list_for_head env sigma c =
  let dbs = current_db () in
  let validate (name, db) =
    let hints = List.map (fun v -> 0, v) (Hint_db.map_all env ~secvars:Id.Pred.full c db) in
    (name, db, hints)
  in
  let valid_dbs = List.map validate dbs in
  if List.is_empty valid_dbs then
    (str "No hint declared for :" ++ pr_global c)
  else
    hov 0
      (str"For " ++ pr_global c ++ str" -> " ++ fnl () ++
         hov 0 (prlist (pr_hints_db env sigma) valid_dbs))

let pr_hint_ref ref = pr_hint_list_for_head ref

(* Print all hints associated to head id in any database *)

let pr_hint_term env sigma cl =
  try
    let dbs = current_db () in
    let valid_dbs =
      let fn = try
          let hdc = decompose_app_bound env sigma cl in
            if occur_existential sigma cl then
              (fun db -> match Hint_db.map_eauto env sigma ~secvars:Id.Pred.full hdc cl db with
              | ModeMatch (_, l) -> l
              | ModeMismatch -> [])
            else Hint_db.map_auto env sigma ~secvars:Id.Pred.full hdc cl
        with Bound -> Hint_db.map_none ~secvars:Id.Pred.full
      in
      let fn db = List.map (fun x -> 0, x) (fn db) in
      List.map (fun (name, db) -> (name, db, fn db)) dbs
    in
      if List.is_empty valid_dbs then
        (str "No hint applicable for current goal")
      else
        (str "Applicable Hints :" ++ fnl () ++
            hov 0 (prlist (pr_hints_db env sigma) valid_dbs))
  with Match_failure _ | Failure _ ->
    (str "No hint applicable for current goal")

(* print all hints that apply to the concl of the current goal *)
let pr_applicable_hint pf =
  let env = Global.env () in
  let Proof.{goals;sigma} = Proof.data pf in
  match goals with
  | [] -> CErrors.user_err Pp.(str "No focused goal.")
  | g::_ ->
    pr_hint_term env sigma (Evd.evar_concl (Evd.find_undefined sigma g))

let parse_mode s =
  match s with
  | "+" -> ModeInput
  | "=" -> ModeFrozen
  | "-" -> ModeOutput
  | "!" -> ModeNoHeadEvar
  | _ -> CErrors.user_err Pp.(str"Unrecognized hint mode " ++ str s)

let parse_modes s =
  let modes = String.split_on_char ' ' s in
  List.map parse_mode modes

let string_of_mode = function
  | ModeInput -> "+"
  | ModeFrozen -> "="
  | ModeOutput -> "-"
  | ModeNoHeadEvar -> "!"

let pp_hint_mode m = str (string_of_mode m)

(* displays the whole hint database db *)
let pr_hint_db_env env sigma db =
  let pr_mode = prvect_with_sep spc pp_hint_mode in
  let pr_modes l =
    if List.is_empty l then mt ()
    else str" (modes " ++ prlist_with_sep pr_comma pr_mode l ++ str")"
  in
  let content =
    let pr_one (head, modes, hintlist) =
      let goal_descr = match head with
      | None -> str "For any goal"
      | Some head -> str "For " ++ pr_global head ++ pr_modes modes
      in
      (* sort because db.hintdb_nopat isn't kept in priority sorted order;
         "auto" sorts on priority before using the hintdb *)
      let sorted = List.stable_sort (fun a b -> Int.compare a.pri b.pri) hintlist in
      (* always prints "id 0" in Print HintDb *)
      let hints = pr_hint_list env sigma (List.map (fun x -> (0, x)) sorted) in
      hov 0 (goal_descr ++ str " -> " ++ hints)
    in
    let hints =
      let name x = Nametab.shortest_qualid_of_global Id.Set.empty x in
      let order (h1, _, _) (h2, _, _) =
        Option.compare (fun a b ->
            let a = name a and b = name b in
            let rv = Id.compare (qualid_basename a) (qualid_basename b) in
            if rv <> 0 then rv else
              String.compare (string_of_qualid a) (string_of_qualid b))
          h1 h2
      in
      let hints = Hint_db.fold (fun h m hl l -> (h, m, hl) :: l) db [] in
      List.stable_sort order hints in
    Pp.prlist pr_one hints
  in
  let { TransparentState.tr_var = ids; tr_cst = csts; tr_prj = ps } =
    Hint_db.transparent_state db
  in
  hov 0
    ((if Hint_db.use_dn db then str"Discriminated database"
      else str"Non-discriminated database")) ++ fnl () ++
  hov 2 (str"Unfoldable variable definitions: " ++ pr_idpred ids) ++ fnl () ++
  hov 2 (str"Unfoldable constant definitions: " ++ pr_cpred csts) ++ fnl () ++
  hov 2 (str"Unfoldable projection definitions: " ++ pr_prpred ps) ++ fnl () ++
  hov 2 (str"Cut: " ++ pp_hints_path (Hint_db.cut db)) ++ fnl () ++
  content

let pr_hint_db_by_name env sigma dbname =
  try
    let db = searchtable_map dbname in pr_hint_db_env env sigma db
  with Not_found ->
    error_no_such_hint_database dbname

(* displays all the hints of all databases *)
let pr_searchtable env sigma =
  let open Summary.Ref in
  let fold name db accu =
    accu ++ str "In the database " ++ str name ++ str ":" ++ fnl () ++
    pr_hint_db_env env sigma db ++ fnl ()
  in
  Hintdbmap.fold fold !searchtable (mt ())

type hint_ast =
  | Res_pf     of hint (* Hint Apply *)
  | ERes_pf    of hint (* Hint EApply *)
  | Give_exact of hint
  | Res_pf_THEN_trivial_fail of hint (* Hint Immediate *)
  | Unfold_nth of Evaluable.t (* Hint Unfold *)
  | Extern of Pattern.constr_pattern option * Gentactic.glob_generic_tactic (* Hint Extern *)

let to_user_ast = function
| Internal.Res_pf h -> Res_pf h
| Internal.ERes_pf h -> ERes_pf h
| Internal.Give_exact h -> Give_exact h
| Internal.Res_pf_THEN_trivial_fail h -> Res_pf_THEN_trivial_fail h
| Internal.Unfold_nth h -> Unfold_nth h
| Internal.Extern (pat, tac) -> Extern (pat, tac)

module FullHint =
struct
  type t = full_hint
  let priority (h : t) = h.pri
  let database (h : t) = h.db
  let pattern (h : t) = match h.pat with
  | None -> None
  | Some (ConstrPattern p | SyntacticPattern p) -> Some p
  | Some DefaultPattern -> None
  let run (h : t) k = k (to_user_ast h.code.obj)
  let print env sigma (h : t) = pr_hint env sigma h.code
  let name (h : t) = h.name

  let subgoals (h : t) = match h.code.obj with
  | Res_pf h | ERes_pf h | Give_exact h | Res_pf_THEN_trivial_fail h -> Some h.hint_arty
  | Unfold_nth _ -> Some 1
  | Extern _ -> None

  let repr (h : t) = to_user_ast h.code.obj
end

let connect_hint_clenv h gl =
  let { hint_uctx = ctx; hint_clnv = clenv } = h in
  (* [clenv] has been generated by a hint-making function, so the only relevant
     data in its evarmap is the set of metas. The function
     below just replaces the metas of sigma by those coming from the clenv. *)
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  Clenv.clenv_refresh env sigma ctx clenv

let fresh_hint env sigma h =
  let { hint_term = c; hint_uctx = ctx } = h in
  match h.hint_uctx with
  | None -> sigma, mkRef c
  | Some ctx ->
    (* Refresh the instance of the hint *)
    let (subst, ctx) = UnivGen.fresh_sort_context_instance ctx in
    let c = Vars.subst_univs_level_constr subst (mkRef c) in
    let sigma = Evd.merge_sort_context_set Evd.univ_flexible ~src:UState.Internal sigma ctx in
    sigma, c

let hint_res_pf ?with_evars ?with_classes ?flags h =
  Proofview.Goal.enter begin fun gl ->
    let clenv = connect_hint_clenv h gl in
    Clenv.res_pf ?with_evars ?with_classes ?flags clenv
  end
