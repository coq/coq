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
open Util
open CErrors
open Names
open Constr
open Context
open Evd
open EConstr
open Vars
open Environ
open Mod_subst
open Globnames
open Libobject
open Namegen
open Libnames
open Termops
open Inductiveops
open Typeclasses
open Pattern
open Patternops
open Clenv
open Tacred
open Printer

module NamedDecl = Context.Named.Declaration

(****************************************)
(* General functions                    *)
(****************************************)

type debug = Debug | Info | Off

exception Bound

let rec head_bound sigma t = match EConstr.kind sigma t with
| Prod (_, _, b)  -> head_bound sigma b
| LetIn (_, _, _, b) -> head_bound sigma b
| App (c, _) -> head_bound sigma c
| Case (_, _, _, _, _, c, _) -> head_bound sigma c
| Ind (ind, _) -> GlobRef.IndRef ind
| Const (c, _) -> GlobRef.ConstRef c
| Construct (c, _) -> GlobRef.ConstructRef c
| Var id -> GlobRef.VarRef id
| Proj (p, _) -> GlobRef.ConstRef (Projection.constant p)
| Cast (c, _, _) -> head_bound sigma c
| Evar _ | Rel _ | Meta _ | Sort _ | Fix _ | Lambda _
| CoFix _ | Int _ | Float _ | Array _ -> raise Bound

let head_constr sigma c =
  try head_bound sigma c
  with Bound -> user_err (Pp.str "Head identifier must be a constant, section variable, \
                                  (co)inductive type, (co)inductive type constructor, or projection.")

let decompose_app_bound sigma t =
  let t = strip_outer_cast sigma t in
  let _,ccl = decompose_prod_assum sigma t in
  let hd,args = decompose_app_vect sigma ccl in
  let open GlobRef in
  match EConstr.kind sigma hd with
    | Const (c,u) -> ConstRef c, args
    | Ind (i,u) -> IndRef i, args
    | Construct (c,u) -> ConstructRef c, args
    | Var id -> VarRef id, args
    | Proj (p, c) -> ConstRef (Projection.constant p), Array.cons c args
    | _ -> raise Bound

(** Compute the set of section variables that remain in the named context.
    Starts from the top to the bottom of the context, stops at the first
    different declaration between the named hyps and the section context. *)
let secvars_of_hyps hyps =
  let secctx = Global.named_context () in
  let open Context.Named.Declaration in
  let pred, all =
    List.fold_left (fun (pred,all) decl ->
        try let _ = Context.Named.lookup (get_id decl) hyps in
          (* Approximation, it might be an hypothesis reintroduced with same name and unconvertible types,
             we must allow it currently, as comparing the declarations for syntactic equality is too
             strong a check (e.g. an unfold in a section variable would make it unusable). *)
          (Id.Pred.add (get_id decl) pred, all)
        with Not_found -> (pred, false))
      (Id.Pred.empty,true) secctx
  in
  if all then Id.Pred.full (* If the whole section context is available *)
  else pred

let empty_hint_info =
  { hint_priority = None; hint_pattern = None }

(************************************************************************)
(*           The Type of Constructions Autotactic Hints                 *)
(************************************************************************)

type 'a hint_ast =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference       (* Hint Unfold *)
  | Extern     of Pattern.constr_pattern option * Genarg.glob_generic_argument (* Hint Extern *)


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

type hint_term =
  | IsGlobRef of GlobRef.t
  | IsConstr of constr * Univ.ContextSet.t option (* None if monomorphic *)

type 'a with_uid = {
  obj : 'a;
  uid : KerName.t;
}

type raw_hint = constr * types * Univ.ContextSet.t option

type hint = {
  hint_term : constr;
  hint_type : types;
  hint_uctx : Univ.ContextSet.t option; (* None if monomorphic *)
  hint_clnv : clausenv;
}

type 'a with_metadata =
  { pri     : int
  (** A number lower is higher priority *)
  ; pat     : constr_pattern option
  (** A pattern for the concl of the Goal *)
  ; name    : hints_path_atom
  (** A potential name to refer to the hint *)
  ; db : string option
  (** The database from which the hint comes *)
  ; secvars : Id.Pred.t
  (** The set of section variables the hint depends on *)
  ; code    : 'a
  (** the tactic to apply when the concl matches pat *)
  }

type full_hint = hint hint_ast with_uid with_metadata

type hint_entry = GlobRef.t option *
  raw_hint hint_ast with_uid with_metadata

type hint_mode =
  | ModeInput (* No evars *)
  | ModeNoHeadEvar (* No evar at the head *)
  | ModeOutput (* Anything *)

type 'a hints_transparency_target =
  | HintsVariables
  | HintsConstants
  | HintsReferences of 'a list

type import_level = HintLax | HintWarn | HintStrict

let warn_hint_to_string = function
| HintLax -> "Lax"
| HintWarn -> "Warn"
| HintStrict -> "Strict"

let string_to_warn_hint = function
| "Lax" -> HintLax
| "Warn" -> HintWarn
| "Strict" -> HintStrict
| _ -> user_err Pp.(str "Only the following values are accepted: Lax, Warn, Strict.")

let warn_hint =
  Goptions.declare_interpreted_string_option_and_ref
    ~depr:false
    ~key:["Loose"; "Hint"; "Behavior"]
    ~value:HintLax
    string_to_warn_hint
    warn_hint_to_string

let fresh_key =
  let id = Summary.ref ~name:"HINT-COUNTER" 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, _) = KerName.repr kn in
    (* We embed the full path of the kernel name in the label so that
       the identifier should be unique. This ensures that including
       two modules together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%i"
      (ModPath.to_string mp) cur)
    in
    KerName.make mp (Label.of_id lbl)

let pri_order_int (id1, {pri=pri1}) (id2, {pri=pri2}) =
  let d = pri1 - pri2 in
    if Int.equal d 0 then id2 - id1
    else d

let pri_order t1 t2 = pri_order_int t1 t2 <= 0

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
  val empty : t
  val add : TransparentState.t option -> t -> Pattern.constr_pattern -> stored_data -> t
  val lookup : Environ.env -> Evd.evar_map -> TransparentState.t option -> t -> EConstr.constr -> stored_data list
end =
struct
  module Data = struct type t = stored_data let compare = pri_order_int end
  module Bnet = Btermdn.Make(Data)

  type diff = Pattern.constr_pattern * stored_data
  type data = Bnet of Bnet.t | Diff of diff * data ref
  type t = data ref

  let empty = ref (Bnet Bnet.empty)

  let add _st net p v = ref (Diff ((p, v), net))

  let rec force env st net = match !net with
  | Bnet dn -> dn
  | Diff ((p, v), rem) ->
    let dn = force env st rem in
    let p = Bnet.pattern env st p in
    let dn = Bnet.add dn p v in
    let () = net := (Bnet dn) in
    dn

  let lookup env sigma st net p =
    let dn = force env st net in
    Bnet.lookup env sigma st dn p
end

type search_entry = {
  sentry_nopat : stored_data list;
  sentry_pat : stored_data list;
  sentry_bnet : Bounded_net.t;
  sentry_mode : hint_mode array list;
}

let empty_se = {
  sentry_nopat = [];
  sentry_pat = [];
  sentry_bnet = Bounded_net.empty;
  sentry_mode = [];
}

let eq_pri_auto_tactic (_, x) (_, y) = KerName.equal x.code.uid y.code.uid

let add_tac pat t se =
  match pat with
  | None ->
    if List.exists (eq_pri_auto_tactic t) se.sentry_nopat then se
    else { se with sentry_nopat = List.insert pri_order t se.sentry_nopat }
  | Some (st, pat) ->
    if List.exists (eq_pri_auto_tactic t) se.sentry_pat then se
    else { se with
        sentry_pat = List.insert pri_order t se.sentry_pat;
        sentry_bnet = Bounded_net.add st se.sentry_bnet pat t; }

let rebuild_dn st se =
  let dn' =
    List.fold_left
      (fun dn (id, t) ->
        Bounded_net.add (Some st) dn (Option.get t.pat) (id, t))
      Bounded_net.empty se.sentry_pat
  in
  { se with sentry_bnet = dn' }

let lookup_tacs env sigma concl st se =
  let l'  = Bounded_net.lookup env sigma st se.sentry_bnet concl in
  let sl' = List.stable_sort pri_order_int l' in
  List.merge pri_order_int se.sentry_nopat sl'

let is_transparent_gr ts = let open GlobRef in function
  | VarRef id -> TransparentState.is_transparent_variable ts id
  | ConstRef cst -> TransparentState.is_transparent_constant ts cst
  | IndRef _ | ConstructRef _ -> false

let strip_params env sigma c =
  match EConstr.kind sigma c with
  | App (f, args) ->
    (match EConstr.kind sigma f with
    | Const (cst,_) ->
      (match Recordops.find_primitive_projection cst with
       | Some p ->
         let p = Projection.make p false in
         let npars = Projection.npars p in
         if Array.length args > npars then
           mkApp (mkProj (p, args.(npars)),
                  Array.sub args (npars+1) (Array.length args - (npars + 1)))
         else c
       | None -> c)
    | _ -> c)
  | _ -> c

let merge_context_set_opt sigma ctx = match ctx with
| None -> sigma
| Some ctx -> Evd.merge_context_set Evd.univ_flexible sigma ctx

let instantiate_hint env sigma p =
  let mk_clenv (c, cty, ctx) =
    let sigma = merge_context_set_opt sigma ctx in
    let cl = mk_clenv_from_env env sigma None (c,cty) in
    let templval = { cl.templval with rebus = strip_params env sigma cl.templval.rebus } in
    let cl = mk_clausenv empty_env cl.evd templval cl.templtyp in
    { hint_term = c; hint_type = cty; hint_uctx = ctx; hint_clnv = cl; }
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

let hints_path_atom_eq h1 h2 = match h1, h2 with
| PathHints l1, PathHints l2 -> List.equal GlobRef.equal l1 l2
| PathAny, PathAny -> true
| _ -> false

let rec hints_path_eq h1 h2 = match h1, h2 with
| PathAtom h1, PathAtom h2 -> hints_path_atom_eq h1 h2
| PathStar h1, PathStar h2 -> hints_path_eq h1 h2
| PathSeq (l1, r1), PathSeq (l2, r2) ->
  hints_path_eq l1 l2 && hints_path_eq r1 r2
| PathOr (l1, r1), PathOr (l2, r2) ->
  hints_path_eq l1 l2 && hints_path_eq r1 r2
| PathEmpty, PathEmpty -> true
| PathEpsilon, PathEpsilon -> true
| _ -> false

let path_matches hp hints =
  let rec aux hp hints k =
    match hp, hints with
    | PathAtom _, [] -> false
    | PathAtom PathAny, (_ :: hints') -> k hints'
    | PathAtom p, (h :: hints') ->
      if hints_path_atom_eq p h then k hints' else false
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

let rec path_derivate hp hint =
  let rec derivate_atoms hints hints' =
    match hints, hints' with
    | gr :: grs, gr' :: grs' when GlobRef.equal gr gr' -> derivate_atoms grs grs'
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
      | hints, PathHints hints' -> derivate_atoms hints hints'
      | _, _ -> assert false)
  | PathStar p -> if path_matches p [hint] then hp else PathEpsilon
  | PathSeq (hp, hp') ->
     let hpder = path_derivate hp hint in
     if matches_epsilon hp then
       PathOr (path_seq hpder hp', path_derivate hp' hint)
     else if is_empty hpder then PathEmpty
     else path_seq hpder hp'
  | PathOr (hp, hp') ->
     PathOr (path_derivate hp hint, path_derivate hp' hint)
  | PathEmpty -> PathEmpty
  | PathEpsilon -> PathEmpty

let rec normalize_path h =
  match h with
  | PathStar PathEpsilon -> PathEpsilon
  | PathSeq (PathEmpty, _) | PathSeq (_, PathEmpty) -> PathEmpty
  | PathSeq (PathEpsilon, p) | PathSeq (p, PathEpsilon) -> normalize_path p
  | PathOr (PathEmpty, p) | PathOr (p, PathEmpty) -> normalize_path p
  | PathOr (p, q) ->
    let p', q' = normalize_path p, normalize_path q in
      if hints_path_eq p p' && hints_path_eq q q' then h
      else normalize_path (PathOr (p', q'))
  | PathSeq (p, q) ->
    let p', q' = normalize_path p, normalize_path q in
      if hints_path_eq p p' && hints_path_eq q q' then h
      else normalize_path (PathSeq (p', q'))
  | _ -> h

let path_derivate hp hint = normalize_path (path_derivate hp hint)

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

type hint_db_name = string

type mode_match =
  | NoMode
  | WithMode of hint_mode array

type 'a with_mode =
  | ModeMatch of mode_match * 'a
  | ModeMismatch

module Hint_db :
sig
type t
val empty : ?name:hint_db_name -> TransparentState.t -> bool -> t
val map_none : secvars:Id.Pred.t -> t -> full_hint list
val map_all : secvars:Id.Pred.t -> GlobRef.t -> t -> full_hint list
val map_existential : evar_map -> secvars:Id.Pred.t ->
                      (GlobRef.t * constr array) -> constr -> t -> full_hint list with_mode
val map_eauto : Environ.env -> evar_map -> secvars:Id.Pred.t ->
                (GlobRef.t * constr array) -> constr -> t -> full_hint list with_mode
val map_auto : Environ.env -> evar_map -> secvars:Id.Pred.t ->
               (GlobRef.t * constr array) -> constr -> t -> full_hint list
val add_one : env -> evar_map -> hint_entry -> t -> t
val add_list : env -> evar_map -> hint_entry list -> t -> t
val remove_one : Environ.env -> GlobRef.t -> t -> t
val remove_list : Environ.env -> GlobRef.t list -> t -> t
val iter : (GlobRef.t option -> hint_mode array list -> full_hint list -> unit) -> t -> unit
val use_dn : t -> bool
val transparent_state : t -> TransparentState.t
val set_transparent_state : t -> TransparentState.t -> t
val add_cut : hints_path -> t -> t
val add_mode : GlobRef.t -> hint_mode array -> t -> t
val cut : t -> hints_path
val unfolds : t -> Id.Set.t * Cset.t
val add_modes : hint_mode array list GlobRef.Map.t -> t -> t
val modes : t -> hint_mode array list GlobRef.Map.t
val fold : (GlobRef.t option -> hint_mode array list -> full_hint list -> 'a -> 'a) ->
  t -> 'a -> 'a
end =
struct

  type t = {
    hintdb_state : TransparentState.t;
    hintdb_cut : hints_path;
    hintdb_unfolds : Id.Set.t * Cset.t;
    hintdb_max_id : int;
    use_dn : bool;
    hintdb_map : search_entry GlobRef.Map.t;
    (* A list of unindexed entries starting with an unfoldable constant
       or with no associated pattern. *)
    hintdb_nopat : (GlobRef.t option * stored_data) list;
    hintdb_name : string option;
  }

  let next_hint_id db =
    let h = db.hintdb_max_id in
    { db with hintdb_max_id = succ db.hintdb_max_id }, h

  let empty ?name st use_dn = { hintdb_state = st;
                          hintdb_cut = PathEmpty;
                          hintdb_unfolds = (Id.Set.empty, Cset.empty);
                          hintdb_max_id = 0;
                          use_dn = use_dn;
                          hintdb_map = GlobRef.Map.empty;
                          hintdb_nopat = [];
                          hintdb_name = name; }

  let find key db =
    try GlobRef.Map.find key db.hintdb_map
    with Not_found -> empty_se

  let realize_tac secvars (id,tac) =
    if Id.Pred.subset tac.secvars secvars then Some tac
    else
      (* Warn about no longer typable hint? *)
      None

  let head_evar sigma c =
    let rec hrec c = match EConstr.kind sigma c with
      | Evar (evk,_)   -> evk
      | Case (_,_,_,_,_,c,_) -> hrec c
      | App (c,_)      -> hrec c
      | Cast (c,_,_)   -> hrec c
      | Proj (p, c)    -> hrec c
      | _              -> raise Evarutil.NoHeadEvar
    in
    hrec c

  let match_mode sigma m arg =
    match m with
    | ModeInput -> not (occur_existential sigma arg)
    | ModeNoHeadEvar ->
       (try ignore(head_evar sigma arg); false
                 with Evarutil.NoHeadEvar -> true)
    | ModeOutput -> true

  let matches_mode sigma args mode =
    if Array.length mode == Array.length args &&
        Array.for_all2 (match_mode sigma) mode args then Some mode
    else None

  let matches_modes sigma args modes =
    if List.is_empty modes then Some NoMode
    else
      try Some (WithMode (List.find_map (matches_mode sigma args) modes))
      with Not_found -> None

  let merge_entry secvars db nopat pat =
    let h = List.sort pri_order_int (List.map snd db.hintdb_nopat) in
    let h = List.merge pri_order_int h nopat in
    let h = List.merge pri_order_int h pat in
    List.map_filter (realize_tac secvars) h

  let map_none ~secvars db =
    merge_entry secvars db [] []

  let map_all ~secvars k db =
    let se = find k db in
    merge_entry secvars db se.sentry_nopat se.sentry_pat

  (* Precondition: concl has no existentials *)
  let map_auto env sigma ~secvars (k,args) concl db =
    let se = find k db in
    let st = if db.use_dn then  (Some db.hintdb_state) else None in
    let pat = lookup_tacs env sigma concl st se in
    merge_entry secvars db [] pat

  let map_existential sigma ~secvars (k,args) concl db =
    let se = find k db in
      match matches_modes sigma args se.sentry_mode with
      | Some m ->
        ModeMatch (m, merge_entry secvars db se.sentry_nopat se.sentry_pat)
      | None -> ModeMismatch

  (* [c] contains an existential *)
  let map_eauto env sigma ~secvars (k,args) concl db =
    let se = find k db in
      match matches_modes sigma args se.sentry_mode with
      | Some m ->
        let st = if db.use_dn then Some db.hintdb_state else None in
        let pat = lookup_tacs env sigma concl st se in
        ModeMatch (m, merge_entry secvars db [] pat)
      | None -> ModeMismatch

  let is_exact = function
    | Give_exact _ -> true
    | _ -> false

  let is_unfold = function
    | Unfold_nth _ -> true
    | _ -> false

  let addkv gr id v db =
    let idv = id, { v with db = db.hintdb_name } in
    let k = match gr with
      | Some gr -> if db.use_dn && is_transparent_gr db.hintdb_state gr &&
          is_unfold v.code.obj then None else Some gr
      | None -> None
    in
      match k with
      | None ->
          let is_present (_, (_, v')) = KerName.equal v.code.uid v'.code.uid in
          if not (List.exists is_present db.hintdb_nopat) then
            (* FIXME *)
            { db with hintdb_nopat = (gr,idv) :: db.hintdb_nopat }
          else db
      | Some gr ->
        let pat =
          if not db.use_dn && is_exact v.code.obj then None
          else
            let dnst = if db.use_dn then Some db.hintdb_state else None in
            Option.map (fun p -> (dnst, p)) v.pat
        in
          let oval = find gr db in
            { db with hintdb_map = GlobRef.Map.add gr (add_tac pat idv oval) db.hintdb_map }

  let rebuild_db st' db =
    let db' =
      { db with hintdb_map = GlobRef.Map.map (rebuild_dn st') db.hintdb_map;
        hintdb_state = st'; hintdb_nopat = [] }
    in
      List.fold_left (fun db (gr,(id,v)) -> addkv gr id v db) db' db.hintdb_nopat

  let add_one env sigma (k, v) db =
    let v = instantiate_hint env sigma v in
    let st',db,rebuild =
      match v.code.obj with
      | Unfold_nth egr ->
          let addunf ts (ids, csts) =
            let open TransparentState in
            match egr with
            | EvalVarRef id ->
              { ts with tr_var = Id.Pred.add id ts.tr_var }, (Id.Set.add id ids, csts)
            | EvalConstRef cst ->
              { ts with tr_cst = Cpred.add cst ts.tr_cst }, (ids, Cset.add cst csts)
          in
          let state, unfs = addunf db.hintdb_state db.hintdb_unfolds in
            state, { db with hintdb_unfolds = unfs }, true
      | _ -> db.hintdb_state, db, false
    in
    let db = if db.use_dn && rebuild then rebuild_db st' db else db in
    let db, id = next_hint_id db in
    addkv k id v db

  let add_list env sigma l db = List.fold_left (fun db k -> add_one env sigma k db) db l

  let remove_sdl p sdl = List.filter p sdl

  let remove_he st p se =
    let sl1' = remove_sdl p se.sentry_nopat in
    let sl2' = remove_sdl p se.sentry_pat in
    if sl1' == se.sentry_nopat && sl2' == se.sentry_pat then se
    else rebuild_dn st { se with sentry_nopat = sl1'; sentry_pat = sl2' }

  let remove_list env grs db =
    let filter (_, h) =
      match h.name with PathHints [gr] -> not (List.mem_f GlobRef.equal gr grs) | _ -> true in
    let hintmap = GlobRef.Map.map (remove_he db.hintdb_state filter) db.hintdb_map in
    let hintnopat = List.filter (fun (ge, sd) -> filter sd) db.hintdb_nopat in
      { db with hintdb_map = hintmap; hintdb_nopat = hintnopat }

  let remove_one env gr db = remove_list env [gr] db

  let get_entry se =
    let h = List.merge pri_order_int se.sentry_nopat se.sentry_pat in
    List.map snd h

  let iter f db =
    let iter_se k se = f (Some k) se.sentry_mode (get_entry se) in
    f None [] (List.map (fun x -> snd (snd x)) db.hintdb_nopat);
    GlobRef.Map.iter iter_se db.hintdb_map

  let fold f db accu =
    let accu = f None [] (List.map (fun x -> snd (snd x)) db.hintdb_nopat) accu in
    GlobRef.Map.fold (fun k se -> f (Some k) se.sentry_mode (get_entry se)) db.hintdb_map accu

  let transparent_state db = db.hintdb_state

  let set_transparent_state db st =
    if db.use_dn then rebuild_db st db
    else { db with hintdb_state = st }

  let add_cut path db =
    { db with hintdb_cut = normalize_path (PathOr (db.hintdb_cut, path)) }

  let add_mode gr m db =
    let se = find gr db in
    let se = { se with sentry_mode = m :: se.sentry_mode } in
    { db with hintdb_map = GlobRef.Map.add gr se db.hintdb_map }

  let cut db = db.hintdb_cut

  let unfolds db = db.hintdb_unfolds

  let add_modes modes db =
    let f gr e me =
      Some { e with sentry_mode = me.sentry_mode @ e.sentry_mode }
    in
    let mode_entries = GlobRef.Map.map (fun m -> { empty_se with sentry_mode = m }) modes in
    { db with hintdb_map = GlobRef.Map.union f db.hintdb_map mode_entries }

  let modes db = GlobRef.Map.map (fun se -> se.sentry_mode) db.hintdb_map

  let use_dn db = db.use_dn

end

module Hintdbmap = String.Map

type hint_db = Hint_db.t

let searchtable = Summary.ref ~name:"searchtable" Hintdbmap.empty
let statustable = Summary.ref ~name:"statustable" KNmap.empty

let searchtable_map name =
  Hintdbmap.find name !searchtable
let searchtable_add (name,db) =
  searchtable := Hintdbmap.add name db !searchtable
let current_db_names () = Hintdbmap.domain !searchtable
let current_db () = Hintdbmap.bindings !searchtable

let current_pure_db () = List.map snd (current_db ())

let error_no_such_hint_database x =
  user_err ~hdr:"Hints" (str "No such Hint database: " ++ str x ++ str ".")

(**************************************************************************)
(*             Auxiliary functions to prepare AUTOHINT objects            *)
(**************************************************************************)

let rec nb_hyp sigma c = match EConstr.kind sigma c with
  | Prod(_,_,c2) -> if noccurn sigma 1 c2 then 1+(nb_hyp sigma c2) else nb_hyp sigma c2
  | _ -> 0

(* adding and removing tactics in the search table *)

let with_uid c = { obj = c; uid = fresh_key () }

let secvars_of_idset s =
  Id.Set.fold (fun id p ->
      if is_section_variable id then
        Id.Pred.add id p
      else p) s Id.Pred.empty

let secvars_of_constr env sigma c =
  secvars_of_idset (Termops.global_vars_set env sigma c)

let secvars_of_global env gr =
  secvars_of_idset (vars_of_global env gr)

let make_exact_entry env sigma info ?(name=PathAny) (c, cty, ctx) =
  let secvars = secvars_of_constr env sigma c in
  let cty = strip_outer_cast sigma cty in
    match EConstr.kind sigma cty with
    | Prod _ -> failwith "make_exact_entry"
    | _ ->
        let hd =
          try head_bound sigma cty
          with Bound -> failwith "make_exact_entry"
        in
        let pri = match info.hint_priority with None -> 0 | Some p -> p in
        let pat = match info.hint_pattern with
        | Some pat -> snd pat
        | None ->
          Patternops.pattern_of_constr env sigma (EConstr.to_constr ~abort_on_undefined_evars:false sigma cty)
        in
        (Some hd,
         { pri; pat = Some pat; name;
           db = None; secvars;
           code = with_uid (Give_exact (c, cty, ctx)); })

let make_apply_entry env sigma hnf info ?(name=PathAny) (c, cty, ctx) =
  let cty = if hnf then hnf_constr env sigma cty else cty in
  match EConstr.kind sigma cty with
  | Prod _ ->
    let sigma' = merge_context_set_opt sigma ctx in
    let ce = mk_clenv_from_env env sigma' None (c,cty) in
    let c' = clenv_type (* ~reduce:false *) ce in
    let hd =
      try head_bound ce.evd c'
      with Bound -> failwith "make_apply_entry" in
    let miss = clenv_missing ce in
    let nmiss = List.length miss in
    let secvars = secvars_of_constr env sigma c in
    let pri = match info.hint_priority with None -> nb_hyp sigma' cty + nmiss | Some p -> p in
    let pat = match info.hint_pattern with
    | Some p -> snd p
    | None ->
      Patternops.pattern_of_constr env ce.evd (EConstr.to_constr ~abort_on_undefined_evars:false sigma c')
    in
    if Int.equal nmiss 0 then
      (Some hd,
       { pri; pat = Some pat; name;
         db = None;
         secvars;
         code = with_uid (Res_pf(c,cty,ctx)); })
    else
      (Some hd,
       { pri; pat = Some pat; name;
         db = None; secvars;
         code = with_uid (ERes_pf(c,cty,ctx)); })
  | _ -> failwith "make_apply_entry"

(* flags is (e,h,v) with e=true if eapply and h=true if hnf and v=true if verbose
   c is a constr
   cty is the type of constr *)

let fresh_global_or_constr env sigma cr = match cr with
| IsGlobRef gr ->
  let (c, ctx) = UnivGen.fresh_global_instance env gr in
  let ctx = if Environ.is_polymorphic env gr then Some ctx else None in
  (EConstr.of_constr c, ctx)
| IsConstr (c, ctx) -> (c, ctx)

let make_resolves env sigma (eapply, hnf) info ~check ?name cr =
  let c, ctx = fresh_global_or_constr env sigma cr in
  let cty = Retyping.get_type_of env sigma c in
  let try_apply f =
    try
      let (_, hint) as ans = f (c, cty, ctx) in
      match hint.code.obj with
      | ERes_pf _ -> if not eapply then None else Some ans
      | _ -> Some ans
    with Failure _ -> None
  in
  let ents = List.map_filter try_apply
                             [make_exact_entry env sigma info ?name;
                              make_apply_entry env sigma hnf info ?name]
  in
  if check && List.is_empty ents then
    user_err ~hdr:"Hint"
      (pr_leconstr_env env sigma c ++ spc() ++
        (if eapply then str"cannot be used as a hint."
        else str "can be used as a hint only for eauto."));
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma decl =
  let hname = NamedDecl.get_id decl in
  let c = mkVar hname in
  try
    [make_apply_entry env sigma true empty_hint_info
       ~name:(PathHints [GlobRef.VarRef hname])
       (c, NamedDecl.get_type decl, None)]
  with
    | Failure _ -> []
    | e when noncritical e -> anomaly (Pp.str "make_resolve_hyp.")

(* REM : in most cases hintname = id *)

let make_unfold eref =
  let g = global_of_evaluable_reference eref in
  (Some g,
   { pri = 4;
     pat = None;
     name = PathHints [g];
     db = None;
     secvars = secvars_of_global (Global.env ()) g;
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
     pat = pat;
     name = PathAny;
     db = None;
     secvars = Id.Pred.empty; (* Approximation *)
     code = with_uid (Extern (pat, tacast)) })

let make_mode ref m =
  let open Term in
  let ty, _ = Typeops.type_of_global_in_context (Global.env ()) ref in
  let ctx, t = decompose_prod ty in
  let n = List.length ctx in
  let m' = Array.of_list m in
    if not (n == Array.length m') then
      user_err ~hdr:"Hint"
        (pr_global ref ++ str" has " ++ int n ++
           str" arguments while the mode declares " ++ int (Array.length m'))
    else m'

let make_trivial env sigma ?(name=PathAny) r =
  let c,ctx = fresh_global_or_constr env sigma r in
  let sigma = merge_context_set_opt sigma ctx in
  let t = hnf_constr env sigma (Retyping.get_type_of env sigma c) in
  let hd = head_constr sigma t in
  let ce = mk_clenv_from_env env sigma None (c,t) in
  (Some hd,
   { pri=1;
     pat = Some (Patternops.pattern_of_constr env ce.evd (EConstr.to_constr sigma (clenv_type ce)));
     name = name;
     db = None;
     secvars = secvars_of_constr env sigma c;
     code= with_uid (Res_pf_THEN_trivial_fail(c,t,ctx)) })



(**************************************************************************)
(*               declaration of the AUTOHINT library object               *)
(**************************************************************************)

(* If the database does not exist, it is created *)
(* TODO: should a warning be printed in this case ?? *)

let get_db dbname =
  try searchtable_map dbname
  with Not_found -> Hint_db.empty ~name:dbname TransparentState.empty false

let add_hint dbname hintlist =
  let check (_, h) =
    let () = if KNmap.mem h.code.uid !statustable then
      user_err Pp.(str "Conflicting hint keys. This can happen when including \
      twice the same module.")
    in
    statustable := KNmap.add h.code.uid false !statustable
  in
  let () = List.iter check hintlist in
  let db = get_db dbname in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let db' = Hint_db.add_list env sigma hintlist db in
    searchtable_add (dbname,db')

let add_transparency dbname target b =
  let open TransparentState in
  let db = get_db dbname in
  let st = Hint_db.transparent_state db in
  let st' =
    match target with
    | HintsVariables -> { st with tr_var = (if b then Id.Pred.full else Id.Pred.empty) }
    | HintsConstants -> { st with tr_cst = (if b then Cpred.full else Cpred.empty) }
    | HintsReferences grs ->
      List.fold_left (fun st gr ->
        match gr with
        | EvalConstRef c -> { st with tr_cst = (if b then Cpred.add else Cpred.remove) c st.tr_cst }
        | EvalVarRef v -> { st with tr_var = (if b then Id.Pred.add else Id.Pred.remove) v st.tr_var })
        st grs
  in searchtable_add (dbname, Hint_db.set_transparent_state db st')

let remove_hint dbname grs =
  let env = Global.env () in
  let db = get_db dbname in
  let db' = Hint_db.remove_list env grs db in
    searchtable_add (dbname, db')

let add_cut dbname path =
  let db = get_db dbname in
  let db' = Hint_db.add_cut path db in
    searchtable_add (dbname, db')

let add_mode dbname l m =
  let db = get_db dbname in
  let db' = Hint_db.add_mode l m db in
    searchtable_add (dbname, db')

type db_obj = {
  db_local : bool;
  db_name : string;
  db_use_dn : bool;
  db_ts : TransparentState.t;
}

let cache_db (_, {db_name=name; db_use_dn=b; db_ts=ts}) =
  searchtable_add (name, Hint_db.empty ~name ts b)

let load_db _ x = cache_db x

let classify_db db = if db.db_local then Dispose else Substitute db

let inDB : db_obj -> obj =
  declare_object {(default_object "AUTOHINT_DB") with
                  cache_function = cache_db;
                  load_function = load_db;
                  subst_function = (fun (_,x) -> x);
                  classify_function = classify_db; }

let create_hint_db l n ts b =
  let hint = {db_local=l; db_name=n; db_use_dn=b; db_ts=ts} in
  Lib.add_anonymous_leaf (inDB hint)

type hint_action =
  | AddTransparency of {
      grefs : evaluable_global_reference hints_transparency_target;
      state : bool;
    }
  | AddHints of hint_entry list
  | RemoveHints of GlobRef.t list
  | AddCut of hints_path
  | AddMode of { gref : GlobRef.t; mode : hint_mode array }

type hint_locality = Local | Export | SuperGlobal

type hint_obj = {
  hint_local : hint_locality;
  hint_name : string;
  hint_action : hint_action;
}

let superglobal h = match h.hint_local with
  | SuperGlobal -> true
  | Local | Export -> false

let load_autohint _ (kn, h) =
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
    if superglobal then add_mode name gref mode

let open_autohint i (kn, h) =
  let superglobal = superglobal h in
  if Int.equal i 1 then match h.hint_action with
  | AddHints hints ->
    let () =
      if not superglobal then
        (* Import-bound hints must be declared when not imported yet *)
        let filter (_, h) = not @@ KNmap.mem h.code.uid !statustable in
        add_hint h.hint_name (List.filter filter hints)
    in
    let add (_, hint) = statustable := KNmap.add hint.code.uid true !statustable in
    List.iter add hints
  | AddCut paths ->
    if not superglobal then add_cut h.hint_name paths
  | AddTransparency { grefs; state } ->
    if not superglobal then add_transparency h.hint_name grefs state
  | RemoveHints hints ->
    if not superglobal then remove_hint h.hint_name hints
  | AddMode { gref; mode } ->
    if not superglobal then add_mode h.hint_name gref mode

let cache_autohint (kn, obj) =
  load_autohint 1 (kn, obj); open_autohint 1 (kn, obj)

let subst_autohint (subst, obj) =
  let subst_key gr =
    let (gr', t) = subst_global subst gr in
    match t with
    | None -> gr'
    | Some t ->
      (try head_bound Evd.empty (EConstr.of_constr t.Univ.univ_abstracted_value)
       with Bound -> gr')
  in
  let subst_mps subst c = EConstr.of_constr (subst_mps subst (EConstr.Unsafe.to_constr c)) in
  let subst_aux ((c, t, ctx) as h) =
    let c' = subst_mps subst c in
    let t' = subst_mps subst t in
    if c==c' && t'==t then h else (c', t', ctx)
  in
  let subst_hint (k,data as hint) =
    let k' = Option.Smart.map subst_key k in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let pat' = Option.Smart.map (subst_pattern env sigma subst) data.pat in
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
          let pat' = Option.Smart.map (subst_pattern env sigma subst) data.pat in
          let tac' = Genintern.generic_substitute subst tac in
          if pat==pat' && tac==tac' then data.code.obj else Extern (pat', tac')
    in
    let name' = subst_path_atom subst data.name in
    let uid' = subst_kn subst data.code.uid in
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

let classify_autohint obj =
  match obj.hint_action with
  | AddHints [] -> Dispose
  | _ -> match obj.hint_local with
    | Local -> Dispose
    | Export | SuperGlobal -> Substitute obj

let inAutoHint : hint_obj -> obj =
  declare_object {(default_object "AUTOHINT") with
                    cache_function = cache_autohint;
                    load_function = load_autohint;
                    open_function = simple_open open_autohint;
                    subst_function = subst_autohint;
                    classify_function = classify_autohint; }

let make_hint ~local name action = {
  hint_local = local;
  hint_name = name;
  hint_action = action;
}

let warn_deprecated_hint_without_locality =
  CWarnings.create ~name:"deprecated-hint-without-locality" ~category:"deprecated"
    (fun () -> strbrk "The default value for hint locality is currently \
    \"local\" in a section and \"global\" otherwise, but is scheduled to change \
    in a future release. For the time being, adding hints outside of sections \
    without specifying an explicit locality is therefore deprecated. It is \
    recommended to use \"export\" whenever possible.")

let check_hint_locality = let open Goptions in function
| OptGlobal ->
  if Global.sections_are_opened () then
  CErrors.user_err Pp.(str
    "This command does not support the global attribute in sections.");
| OptExport ->
  if Global.sections_are_opened () then
  CErrors.user_err Pp.(str
    "This command does not support the export attribute in sections.");
| OptDefault ->
  if not @@ Global.sections_are_opened () then
    warn_deprecated_hint_without_locality ()
| OptLocal -> ()

let interp_locality = function
| Goptions.OptDefault | Goptions.OptGlobal -> SuperGlobal
| Goptions.OptExport -> Export
| Goptions.OptLocal -> Local

let remove_hints ~locality dbnames grs =
  let local = interp_locality locality in
  let dbnames = if List.is_empty dbnames then ["core"] else dbnames in
    List.iter
      (fun dbname ->
        let hint = make_hint ~local dbname (RemoveHints grs) in
        Lib.add_anonymous_leaf (inAutoHint hint))
      dbnames

(**************************************************************************)
(*                     The "Hint" vernacular command                      *)
(**************************************************************************)

let add_resolves env sigma clist ~local dbnames =
  List.iter
    (fun dbname ->
      let r =
        List.flatten (List.map (fun (pri, hnf, path, gr) ->
          make_resolves env sigma (true, hnf)
            pri ~check:true ~name:path gr) clist)
      in
      let check (_, hint) = match hint.code.obj with
      | ERes_pf (c, cty, ctx) ->
        let sigma' = merge_context_set_opt sigma ctx in
        let ce = mk_clenv_from_env env sigma' None (c,cty) in
        let miss = clenv_missing ce in
        let nmiss = List.length miss in
        let variables = str (CString.plural nmiss "variable") in
        Feedback.msg_info (
          strbrk "The hint " ++
          pr_leconstr_env env sigma' c ++
          strbrk " will only be used by eauto, because applying " ++
          pr_leconstr_env env sigma' c ++
          strbrk " would leave " ++ variables ++ Pp.spc () ++
          Pp.prlist_with_sep Pp.pr_comma Name.print (List.map (Evd.meta_name ce.evd) miss) ++
          strbrk " as unresolved existential " ++ variables ++ str "."
        )
      | _ -> ()
      in
      let () = if not !Flags.quiet then List.iter check r in
      let hint = make_hint ~local dbname (AddHints r) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_unfolds l ~local dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~local dbname (AddHints (List.map make_unfold l)) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_cuts l ~local dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~local dbname (AddCut l) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_mode l m ~local dbnames =
  List.iter
    (fun dbname ->
      let m' = make_mode l m in
      let hint = make_hint ~local dbname (AddMode { gref = l; mode = m' }) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_transparency l b ~local dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~local dbname (AddTransparency { grefs = l; state = b }) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_extern info tacast ~local dbname =
  let pat = match info.hint_pattern with
  | None -> None
  | Some (_, pat) -> Some pat
  in
  let hint = make_hint ~local dbname
                       (AddHints [make_extern (Option.get info.hint_priority) pat tacast]) in
  Lib.add_anonymous_leaf (inAutoHint hint)

let add_externs info tacast ~local dbnames =
  List.iter (add_extern info tacast ~local) dbnames

let add_trivials env sigma l ~local dbnames =
  List.iter
    (fun dbname ->
      let l = List.map (fun (name, c) -> make_trivial env sigma ~name c) l in
      let hint = make_hint ~local dbname (AddHints l) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

type hnf = bool

type nonrec hint_info = hint_info

type hints_entry =
  | HintsResolveEntry of (hint_info * hnf * hints_path_atom * hint_term) list
  | HintsImmediateEntry of (hints_path_atom * hint_term) list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference hints_transparency_target * bool
  | HintsModeEntry of GlobRef.t * hint_mode list
  | HintsExternEntry of hint_info * Genarg.glob_generic_argument

let default_prepare_hint_ident = Id.of_string "H"

exception Found of constr * types

let prepare_hint check env init (sigma,c) =
  let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
  (* We re-abstract over uninstantiated evars and universes.
     It is actually a bit stupid to generalize over evars since the first
     thing make_resolves will do is to re-instantiate the products *)
  let sigma, _ = Evd.nf_univ_variables sigma in
  let c = Evarutil.nf_evar sigma c in
  let c = drop_extra_implicit_args sigma c in
  let vars = ref (collect_vars sigma c) in
  let subst = ref [] in
  let rec find_next_evar c = match EConstr.kind sigma c with
    | Evar (evk,args as ev) ->
      (* We skip the test whether args is the identity or not *)
      let t = Evarutil.nf_evar sigma (existential_type sigma ev) in
      let t = List.fold_right (fun (e,id) c -> replace_term sigma e id c) !subst t in
      if not (closed0 sigma c) then
        user_err Pp.(str "Hints with holes dependent on a bound variable not supported.");
      if occur_existential sigma t then
        (* Not clever enough to construct dependency graph of evars *)
        user_err Pp.(str "Not clever enough to deal with evars dependent in other evars.");
      raise (Found (c,t))
    | _ -> EConstr.iter sigma find_next_evar c in
  let rec iter c =
    try find_next_evar c; c
    with Found (evar,t) ->
      let id = next_ident_away_from default_prepare_hint_ident (fun id -> Id.Set.mem id !vars) in
      vars := Id.Set.add id !vars;
      subst := (evar,mkVar id)::!subst;
      mkNamedLambda (make_annot id Sorts.Relevant) t (iter (replace_term sigma evar (mkVar id) c)) in
  let c' = iter c in
    let env = Global.env () in
    if check then Pretyping.check_evars env sigma c';
    let diff = Univ.ContextSet.diff (Evd.universe_context_set sigma) (Evd.universe_context_set init) in
    (c', diff)

let add_hints ~locality dbnames h =
  let local = interp_locality locality in
  if String.List.mem "nocore" dbnames then
    user_err Pp.(str "The hint database \"nocore\" is meant to stay empty.");
  assert (not (List.is_empty dbnames));
  let env = Global.env() in
  let sigma = Evd.from_env env in
  match h with
  | HintsResolveEntry lhints -> add_resolves env sigma lhints ~local dbnames
  | HintsImmediateEntry lhints -> add_trivials env sigma lhints ~local dbnames
  | HintsCutEntry lhints -> add_cuts lhints ~local dbnames
  | HintsModeEntry (l,m) -> add_mode l m ~local dbnames
  | HintsUnfoldEntry lhints -> add_unfolds lhints ~local dbnames
  | HintsTransparencyEntry (lhints, b) ->
      add_transparency lhints b ~local dbnames
  | HintsExternEntry (info, tacexp) ->
      add_externs info tacexp ~local dbnames

let hint_globref gr = IsGlobRef gr

let hint_constr (c, diff) = IsConstr (c, diff)

let expand_constructor_hints env sigma lems =
  List.map_append (fun (evd,lem) ->
    match EConstr.kind sigma lem with
    | Ind (ind,u) ->
        List.init (nconstructors env ind)
                  (fun i -> IsGlobRef (GlobRef.ConstructRef ((ind,i+1))))
    | _ ->
      let (c, ctx) = prepare_hint false env sigma (evd,lem) in
      let ctx = if Univ.ContextSet.is_empty ctx then None else Some ctx in
      [IsConstr (c, ctx)]) lems
(* builds a hint database from a constr signature *)
(* typically used with (lid, ltyp) = pf_hyps_types <some goal> *)

let constructor_hints env sigma eapply lems =
  let lems = expand_constructor_hints env sigma lems in
  List.map_append (fun lem ->
      make_resolves env sigma (eapply, true) empty_hint_info ~check:true lem) lems

let make_resolves env sigma info hint =
  let name = PathHints [hint] in
  make_resolves env sigma (true, false) info ~check:false ~name (IsGlobRef hint)

let make_local_hint_db env sigma ts eapply lems =
  let map c = c env sigma in
  let lems = List.map map lems in
  let sign = EConstr.named_context env in
  let ts = match ts with
    | None -> Hint_db.transparent_state (searchtable_map "core")
    | Some ts -> ts
  in
  let hintlist = List.map_append (make_resolve_hyp env sigma) sign in
  Hint_db.empty ts false
  |> Hint_db.add_list env sigma hintlist
  |> Hint_db.add_list env sigma (constructor_hints env sigma eapply lems)

let make_local_hint_db env sigma ?ts eapply lems =
  make_local_hint_db env sigma ts eapply lems

let make_db_list dbnames =
  let use_core = not (List.mem "nocore" dbnames) in
  let dbnames = List.remove String.equal "nocore" dbnames in
  let dbnames = if use_core then "core"::dbnames else dbnames in
  let lookup db =
    try searchtable_map db with Not_found -> error_no_such_hint_database db
  in
  List.map lookup dbnames

(**************************************************************************)
(*                    Functions for printing the hints                    *)
(**************************************************************************)

let pr_hint_elt env sigma h = pr_econstr_env env sigma h.hint_term

let pr_hint env sigma h = match h.obj with
  | Res_pf c -> (str"simple apply " ++ pr_hint_elt env sigma c)
  | ERes_pf c -> (str"simple eapply " ++ pr_hint_elt env sigma c)
  | Give_exact c -> (str"exact " ++ pr_hint_elt env sigma c)
  | Res_pf_THEN_trivial_fail c ->
      (str"simple apply " ++ pr_hint_elt env sigma c ++ str" ; trivial")
  | Unfold_nth c ->
    str"unfold " ++  pr_evaluable_reference c
  | Extern (_, tac) ->
    str "(*external*) " ++ Pputils.pr_glb_generic env sigma tac

let pr_id_hint env sigma (id, v) =
  let pr_pat p = str", pattern " ++ pr_lconstr_pattern_env env sigma p in
  (pr_hint env sigma v.code ++ str"(level " ++ int v.pri ++ pr_opt_no_spc pr_pat v.pat
   ++ str", id " ++ int id ++ str ")" ++ spc ())

let pr_hint_list env sigma hintlist =
  (str "  " ++ hov 0 (prlist (pr_id_hint env sigma) hintlist) ++ fnl ())

let pr_hints_db env sigma (name,db,hintlist) =
  (str "In the database " ++ str name ++ str ":" ++
     if List.is_empty hintlist then (str " nothing" ++ fnl ())
     else (fnl () ++ pr_hint_list env sigma hintlist))

(* Print all hints associated to head c in any database *)
let pr_hint_list_for_head env sigma c =
  let dbs = current_db () in
  let validate (name, db) =
    let hints = List.map (fun v -> 0, v) (Hint_db.map_all ~secvars:Id.Pred.full c db) in
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
          let hdc = decompose_app_bound sigma cl in
            if occur_existential sigma cl then
              (fun db -> match Hint_db.map_existential sigma ~secvars:Id.Pred.full hdc cl db with
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
    pr_hint_term env sigma (Goal.V82.concl sigma g)

let pp_hint_mode = function
  | ModeInput -> str"+"
  | ModeNoHeadEvar -> str"!"
  | ModeOutput -> str"-"

(* displays the whole hint database db *)
let pr_hint_db_env env sigma db =
  let pr_mode = prvect_with_sep spc pp_hint_mode in
  let pr_modes l =
    if List.is_empty l then mt ()
    else str" (modes " ++ prlist_with_sep pr_comma pr_mode l ++ str")"
  in
  let content =
    let fold head modes hintlist accu =
      let goal_descr = match head with
      | None -> str "For any goal"
      | Some head -> str "For " ++ pr_global head ++ pr_modes modes
      in
      let hints = pr_hint_list env sigma (List.map (fun x -> (0, x)) hintlist) in
      let hint_descr = hov 0 (goal_descr ++ str " -> " ++ hints) in
      accu ++ hint_descr
    in
    Hint_db.fold fold db (mt ())
  in
  let { TransparentState.tr_var = ids; tr_cst = csts } = Hint_db.transparent_state db in
  hov 0
    ((if Hint_db.use_dn db then str"Discriminated database"
      else str"Non-discriminated database")) ++ fnl () ++
  hov 2 (str"Unfoldable variable definitions: " ++ pr_idpred ids) ++ fnl () ++
  hov 2 (str"Unfoldable constant definitions: " ++ pr_cpred csts) ++ fnl () ++
  hov 2 (str"Cut: " ++ pp_hints_path (Hint_db.cut db)) ++ fnl () ++
  content

let pr_hint_db_by_name env sigma dbname =
  try
    let db = searchtable_map dbname in pr_hint_db_env env sigma db
  with Not_found ->
    error_no_such_hint_database dbname

(* displays all the hints of all databases *)
let pr_searchtable env sigma =
  let fold name db accu =
    accu ++ str "In the database " ++ str name ++ str ":" ++ fnl () ++
    pr_hint_db_env env sigma db ++ fnl ()
  in
  Hintdbmap.fold fold !searchtable (mt ())

let print_mp mp =
  try
    let qid = Nametab.shortest_qualid_of_module mp in
    str " from "  ++ pr_qualid qid
  with Not_found -> mt ()

let is_imported h = try KNmap.find h.uid !statustable with Not_found -> true

let hint_trace = Evd.Store.field ()

let log_hint h =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = get_extra_data sigma in
  match Store.get store hint_trace with
  | None ->
    (* All calls to hint logging should be well-scoped *)
    assert false
  | Some trace ->
    let trace = KNmap.add h.uid h trace in
    let store = Store.set store hint_trace trace in
    Proofview.Unsafe.tclEVARS (set_extra_data store sigma)

let warn_non_imported_hint =
  CWarnings.create ~name:"non-imported-hint" ~category:"automation"
         (fun (hint,mp) ->
          strbrk "Hint used but not imported: " ++ hint ++ print_mp mp)

let warn env sigma h =
  let hint = pr_hint env sigma h in
  let mp = KerName.modpath h.uid in
  warn_non_imported_hint (hint,mp)

let wrap_hint_warning t =
  let open Proofview.Notations in
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = get_extra_data sigma in
  let old = Store.get store hint_trace in
  let store = Store.set store hint_trace KNmap.empty in
  Proofview.Unsafe.tclEVARS (set_extra_data store sigma) >>= fun () ->
  t >>= fun ans ->
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = get_extra_data sigma in
  let hints = match Store.get store hint_trace with
  | None -> assert false
  | Some hints -> hints
  in
  let () = KNmap.iter (fun _ h -> warn env sigma h) hints in
  let store = match old with
  | None -> Store.remove store hint_trace
  | Some v -> Store.set store hint_trace v
  in
  Proofview.Unsafe.tclEVARS (set_extra_data store sigma) >>= fun () ->
  Proofview.tclUNIT ans

let wrap_hint_warning_fun env sigma t =
  let store = get_extra_data sigma in
  let old = Store.get store hint_trace in
  let store = Store.set store hint_trace KNmap.empty in
  let (ans, sigma) = t (set_extra_data store sigma) in
  let store = get_extra_data sigma in
  let hints = match Store.get store hint_trace with
  | None -> assert false
  | Some hints -> hints
  in
  let () = KNmap.iter (fun _ h -> warn env sigma h) hints in
  let store = match old with
  | None -> Store.remove store hint_trace
  | Some v -> Store.set store hint_trace v
  in
  (ans, set_extra_data store sigma)

let run_hint tac k = match warn_hint () with
| HintLax -> k tac.obj
| HintWarn ->
  if is_imported tac then k tac.obj
  else Proofview.tclTHEN (log_hint tac) (k tac.obj)
| HintStrict ->
  if is_imported tac then k tac.obj
  else
    let info = Exninfo.reify () in
    Proofview.tclZERO ~info (UserError (None, (str "Tactic failure.")))

module FullHint =
struct
  type t = full_hint
  let priority (h : t) = h.pri
  let pattern (h : t) = h.pat
  let database (h : t) = h.db
  let run (h : t) k = run_hint h.code k
  let print env sigma (h : t) = pr_hint env sigma h.code
  let name (h : t) = h.name

  let repr (h : t) = h.code.obj
end

let connect_hint_clenv h gl =
  let { hint_uctx = ctx; hint_clnv = clenv } = h in
  (* [clenv] has been generated by a hint-making function, so the only relevant
     data in its evarmap is the set of metas. The [evar_reset_evd] function
     below just replaces the metas of sigma by those coming from the clenv. *)
  let sigma = Tacmach.New.project gl in
  let evd = Evd.evars_reset_evd ~with_conv_pbs:true ~with_univs:false sigma clenv.evd in
  (* Still, we need to update the universes *)
  match h.hint_uctx with
  | Some ctx ->
    (* Refresh the instance of the hint *)
    let (subst, ctx) = UnivGen.fresh_universe_context_set_instance ctx in
    let emap c = Vars.subst_univs_level_constr subst c in
    let evd = Evd.merge_context_set Evd.univ_flexible evd ctx in
    (* Only metas are mentioning the old universes. *)
    Clenv.mk_clausenv
      (Proofview.Goal.env gl)
      (Evd.map_metas emap evd)
      (Evd.map_fl emap clenv.templval)
      (Evd.map_fl emap clenv.templtyp)
  | None ->
    Clenv.mk_clausenv
      (Proofview.Goal.env gl)
      evd
      clenv.templval
      clenv.templtyp

let fresh_hint env sigma h =
  let { hint_term = c; hint_uctx = ctx } = h in
  match h.hint_uctx with
  | None -> sigma, c
  | Some ctx ->
    (* Refresh the instance of the hint *)
    let (subst, ctx) = UnivGen.fresh_universe_context_set_instance ctx in
    let c = Vars.subst_univs_level_constr subst c in
    let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
    sigma, c

let hint_res_pf ?with_evars ?with_classes ?flags h =
  Proofview.Goal.enter begin fun gl ->
    let clenv = connect_hint_clenv h gl in
    Clenv.res_pf ?with_evars ?with_classes ?flags clenv
  end
