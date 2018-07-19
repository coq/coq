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
open CErrors
open Names
open Constr
open Evd
open EConstr
open Vars
open Environ
open Mod_subst
open Globnames
open Libobject
open Namegen
open Libnames
open Smartlocate
open Termops
open Inductiveops
open Typing
open Decl_kinds
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

let head_constr_bound sigma t =
  let t = strip_outer_cast sigma t in
  let _,ccl = decompose_prod_assum sigma t in
  let hd,args = decompose_app sigma ccl in
  match EConstr.kind sigma hd with
  | Const (c, _) -> ConstRef c
  | Ind (i, _) -> IndRef i
  | Construct (c, _) -> ConstructRef c
  | Var id -> VarRef id
  | Proj (p, _) -> ConstRef (Projection.constant p)
  | _ -> raise Bound

let head_constr sigma c =
  try head_constr_bound sigma c
  with Bound -> user_err (Pp.str "Head identifier must be a constant, section variable, \
                                  (co)inductive type, (co)inductive type constructor, or projection.")

let decompose_app_bound sigma t =
  let t = strip_outer_cast sigma t in
  let _,ccl = decompose_prod_assum sigma t in
  let hd,args = decompose_app_vect sigma ccl in
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

type hint_info_expr = Constrexpr.constr_pattern_expr hint_info_gen

type 'a hint_ast =
  | Res_pf     of 'a (* Hint Apply *)
  | ERes_pf    of 'a (* Hint EApply *)
  | Give_exact of 'a
  | Res_pf_THEN_trivial_fail of 'a (* Hint Immediate *)
  | Unfold_nth of evaluable_global_reference       (* Hint Unfold *)
  | Extern     of Genarg.glob_generic_argument (* Hint Extern *)


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
  | IsConstr of constr * Univ.ContextSet.t

type 'a with_uid = {
  obj : 'a;
  uid : KerName.t;
}

type raw_hint = constr * types * Univ.ContextSet.t

type hint = (raw_hint * clausenv) hint_ast with_uid

type 'a with_metadata = {
  pri     : int;            (* A number lower is higher priority *)
  poly    : polymorphic;    (** Is the hint polymorpic and hence should be refreshed at each application *)
  pat     : constr_pattern option; (* A pattern for the concl of the Goal *)
  name    : hints_path_atom; (* A potential name to refer to the hint *)
  db : string option; (** The database from which the hint comes *)
  secvars : Id.Pred.t; (* The set of section variables the hint depends on *)
  code    : 'a;     (* the tactic to apply when the concl matches pat *)
}

type full_hint = hint with_metadata

type hint_entry = GlobRef.t option *
  raw_hint hint_ast with_uid with_metadata

type reference_or_constr =
  | HintsReference of qualid
  | HintsConstr of Constrexpr.constr_expr

type hint_mode =
  | ModeInput (* No evars *)
  | ModeNoHeadEvar (* No evar at the head *)
  | ModeOutput (* Anything *)

type 'a hints_transparency_target =
  | HintsVariables
  | HintsConstants
  | HintsReferences of 'a list

type hints_expr =
  | HintsResolve of (hint_info_expr * bool * reference_or_constr) list
  | HintsResolveIFF of bool * qualid list * int option
  | HintsImmediate of reference_or_constr list
  | HintsUnfold of qualid list
  | HintsTransparency of qualid hints_transparency_target * bool
  | HintsMode of qualid * hint_mode list
  | HintsConstructors of qualid list
  | HintsExtern of int * Constrexpr.constr_expr option * Genarg.raw_generic_argument

type import_level = [ `LAX | `WARN | `STRICT ]

let warn_hint : import_level ref = ref `LAX
let read_warn_hint () = match !warn_hint with
| `LAX -> "Lax"
| `WARN -> "Warn"
| `STRICT -> "Strict"

let write_warn_hint = function
| "Lax" -> warn_hint := `LAX
| "Warn" -> warn_hint := `WARN
| "Strict" -> warn_hint := `STRICT
| _ -> user_err Pp.(str "Only the following flags are accepted: Lax, Warn, Strict.")

let _ =
  Goptions.declare_string_option
    { Goptions.optdepr  = false;
      Goptions.optname  = "behavior of non-imported hints";
      Goptions.optkey   = ["Loose"; "Hint"; "Behavior"];
      Goptions.optread  = read_warn_hint;
      Goptions.optwrite = write_warn_hint;
    }

let fresh_key =
  let id = Summary.ref ~name:"HINT-COUNTER" 0 in
  fun () ->
    let cur = incr id; !id in
    let lbl = Id.of_string ("_" ^ string_of_int cur) in
    let kn = Lib.make_kn lbl in
    let (mp, dir, _) = KerName.repr kn in
    (** We embed the full path of the kernel name in the label so that the
        identifier should be unique. This ensures that including two modules
        together won't confuse the corresponding labels. *)
    let lbl = Id.of_string_soft (Printf.sprintf "%s#%s#%i"
      (ModPath.to_string mp) (DirPath.to_string dir) cur)
    in
    KerName.make mp dir (Label.of_id lbl)

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

module Bounded_net = Btermdn.Make(struct
				    type t = stored_data
				    let compare = pri_order_int
				  end)

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

let add_tac pat t st se =
  match pat with
  | None -> 
    if List.exists (eq_pri_auto_tactic t) se.sentry_nopat then se
    else { se with sentry_nopat = List.insert pri_order t se.sentry_nopat }
  | Some pat -> 
    if List.exists (eq_pri_auto_tactic t) se.sentry_pat then se
    else { se with
        sentry_pat = List.insert pri_order t se.sentry_pat;
        sentry_bnet = Bounded_net.add st se.sentry_bnet (pat, t); }

let rebuild_dn st se =
  let dn' = 
    List.fold_left 
      (fun dn (id, t) -> Bounded_net.add (Some st) dn (Option.get t.pat, (id, t)))
      Bounded_net.empty se.sentry_pat
  in
  { se with sentry_bnet = dn' }

let lookup_tacs sigma concl st se =
  let l'  = Bounded_net.lookup sigma st se.sentry_bnet concl in
  let sl' = List.stable_sort pri_order_int l' in
  List.merge pri_order_int se.sentry_nopat sl'

module Constr_map = Map.Make(RefOrdered)

let is_transparent_gr (ids, csts) = function
  | VarRef id -> Id.Pred.mem id ids
  | ConstRef cst -> Cpred.mem cst csts
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

let instantiate_hint env sigma p =
  let mk_clenv (c, cty, ctx) =
    let sigma = Evd.merge_context_set univ_flexible sigma ctx in
    let cl = mk_clenv_from_env env sigma None (c,cty) in 
      {cl with templval = 
	  { cl.templval with rebus = strip_params env sigma cl.templval.rebus };
	env = empty_env}
  in
  let code = match p.code.obj with
    | Res_pf c -> Res_pf (c, mk_clenv c)
    | ERes_pf c -> ERes_pf (c, mk_clenv c)
    | Res_pf_THEN_trivial_fail c ->
      Res_pf_THEN_trivial_fail (c, mk_clenv c)
    | Give_exact c -> Give_exact (c, mk_clenv c)
    | Unfold_nth e -> Unfold_nth e
    | Extern t -> Extern t
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

module Hint_db :
sig
type t
val empty : ?name:hint_db_name -> transparent_state -> bool -> t
val find : GlobRef.t -> t -> search_entry
val map_none : secvars:Id.Pred.t -> t -> full_hint list
val map_all : secvars:Id.Pred.t -> GlobRef.t -> t -> full_hint list
val map_existential : evar_map -> secvars:Id.Pred.t ->
                      (GlobRef.t * constr array) -> constr -> t -> full_hint list
val map_eauto : evar_map -> secvars:Id.Pred.t ->
                (GlobRef.t * constr array) -> constr -> t -> full_hint list
val map_auto : evar_map -> secvars:Id.Pred.t ->
               (GlobRef.t * constr array) -> constr -> t -> full_hint list
val add_one : env -> evar_map -> hint_entry -> t -> t
val add_list : env -> evar_map -> hint_entry list -> t -> t
val remove_one : GlobRef.t -> t -> t
val remove_list : GlobRef.t list -> t -> t
val iter : (GlobRef.t option -> hint_mode array list -> full_hint list -> unit) -> t -> unit
val use_dn : t -> bool
val transparent_state : t -> transparent_state
val set_transparent_state : t -> transparent_state -> t
val add_cut : hints_path -> t -> t
val add_mode : GlobRef.t -> hint_mode array -> t -> t
val cut : t -> hints_path
val unfolds : t -> Id.Set.t * Cset.t
val fold : (GlobRef.t option -> hint_mode array list -> full_hint list -> 'a -> 'a) ->
  t -> 'a -> 'a

end =
struct

  type t = {
    hintdb_state : Names.transparent_state;
    hintdb_cut : hints_path;
    hintdb_unfolds : Id.Set.t * Cset.t;
    hintdb_max_id : int;
    use_dn : bool;
    hintdb_map : search_entry Constr_map.t;
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
			  hintdb_map = Constr_map.empty;
			  hintdb_nopat = [];
			  hintdb_name = name; }

  let find key db =
    try Constr_map.find key db.hintdb_map
    with Not_found -> empty_se
 
  let realize_tac secvars (id,tac) =
    if Id.Pred.subset tac.secvars secvars then Some tac
    else
      (** Warn about no longer typable hint? *)
      None

  let head_evar sigma c =
    let rec hrec c = match EConstr.kind sigma c with
      | Evar (evk,_)   -> evk
      | Case (_,_,c,_) -> hrec c
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
    Array.length mode == Array.length args &&
      Array.for_all2 (match_mode sigma) mode args
      
  let matches_modes sigma args modes =
    if List.is_empty modes then true
    else List.exists (matches_mode sigma args) modes

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
	
  (** Precondition: concl has no existentials *)
  let map_auto sigma ~secvars (k,args) concl db =
    let se = find k db in
    let st = if db.use_dn then  (Some db.hintdb_state) else None in
    let pat = lookup_tacs sigma concl st se in
    merge_entry secvars db [] pat

  let map_existential sigma ~secvars (k,args) concl db =
    let se = find k db in
      if matches_modes sigma args se.sentry_mode then
        merge_entry secvars db se.sentry_nopat se.sentry_pat
      else merge_entry secvars db [] []

  (* [c] contains an existential *)
  let map_eauto sigma ~secvars (k,args) concl db =
    let se = find k db in
      if matches_modes sigma args se.sentry_mode then
        let st = if db.use_dn then Some db.hintdb_state else None in
        let pat = lookup_tacs sigma concl st se in
        merge_entry secvars db [] pat
      else merge_entry secvars db [] []

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
    let dnst = if db.use_dn then Some db.hintdb_state else None in
    let pat = if not db.use_dn && is_exact v.code.obj then None else v.pat in
      match k with
      | None ->
          let is_present (_, (_, v')) = KerName.equal v.code.uid v'.code.uid in
	  if not (List.exists is_present db.hintdb_nopat) then
	    (** FIXME *)
	    { db with hintdb_nopat = (gr,idv) :: db.hintdb_nopat }
	  else db
      | Some gr ->
	  let oval = find gr db in
	    { db with hintdb_map = Constr_map.add gr (add_tac pat idv dnst oval) db.hintdb_map }

  let rebuild_db st' db =
    let db' =
      { db with hintdb_map = Constr_map.map (rebuild_dn st') db.hintdb_map;
	hintdb_state = st'; hintdb_nopat = [] }
    in
      List.fold_left (fun db (gr,(id,v)) -> addkv gr id v db) db' db.hintdb_nopat

  let add_one env sigma (k, v) db =
    let v = instantiate_hint env sigma v in
    let st',db,rebuild =
      match v.code.obj with
      | Unfold_nth egr ->
	  let addunf (ids,csts) (ids',csts') =
	    match egr with
	    | EvalVarRef id -> (Id.Pred.add id ids, csts), (Id.Set.add id ids', csts')
	    | EvalConstRef cst -> (ids, Cpred.add cst csts), (ids', Cset.add cst csts')
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

  let remove_list grs db =
    let filter (_, h) =
      match h.name with PathHints [gr] -> not (List.mem_f GlobRef.equal gr grs) | _ -> true in
    let hintmap = Constr_map.map (remove_he db.hintdb_state filter) db.hintdb_map in
    let hintnopat = List.filter (fun (ge, sd) -> filter sd) db.hintdb_nopat in
      { db with hintdb_map = hintmap; hintdb_nopat = hintnopat }

  let remove_one gr db = remove_list [gr] db

  let get_entry se =
    let h = List.merge pri_order_int se.sentry_nopat se.sentry_pat in
    List.map snd h

  let iter f db =
    let iter_se k se = f (Some k) se.sentry_mode (get_entry se) in
    f None [] (List.map (fun x -> snd (snd x)) db.hintdb_nopat);
    Constr_map.iter iter_se db.hintdb_map

  let fold f db accu =
    let accu = f None [] (List.map (fun x -> snd (snd x)) db.hintdb_nopat) accu in
    Constr_map.fold (fun k se -> f (Some k) se.sentry_mode (get_entry se)) db.hintdb_map accu

  let transparent_state db = db.hintdb_state

  let set_transparent_state db st =
    if db.use_dn then rebuild_db st db
    else { db with hintdb_state = st }

  let add_cut path db =
    { db with hintdb_cut = normalize_path (PathOr (db.hintdb_cut, path)) }

  let add_mode gr m db =
    let se = find gr db in
    let se = { se with sentry_mode = m :: se.sentry_mode } in
    { db with hintdb_map = Constr_map.add gr se db.hintdb_map }

  let cut db = db.hintdb_cut

  let unfolds db = db.hintdb_unfolds

  let use_dn db = db.use_dn

end

module Hintdbmap = String.Map

type hint_db = Hint_db.t

type hint_db_table = hint_db Hintdbmap.t ref

(** Initially created hint databases, for typeclasses and rewrite *)

let typeclasses_db = "typeclass_instances"
let rewrite_db = "rewrite"

let auto_init_db =
  Hintdbmap.add typeclasses_db (Hint_db.empty full_transparent_state true)
    (Hintdbmap.add rewrite_db (Hint_db.empty cst_full_transparent_state true)
       Hintdbmap.empty)

let searchtable : hint_db_table = ref auto_init_db
let statustable = ref KNmap.empty

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
(*                       Definition of the summary                        *)
(**************************************************************************)

let hints_init : (unit -> unit) ref = ref (fun () -> ())
let add_hints_init f =
  let init = !hints_init in
  hints_init := (fun () -> init (); f ())

let init     () =
  searchtable := auto_init_db; statustable := KNmap.empty; !hints_init ()
let freeze   _ = (!searchtable, !statustable)
let unfreeze (fs, st) = searchtable := fs; statustable := st

let _ = Summary.declare_summary "search"
	  { Summary.freeze_function   = freeze;
	    Summary.unfreeze_function = unfreeze;
	    Summary.init_function     = init }

(**************************************************************************)
(*             Auxiliary functions to prepare AUTOHINT objects            *)
(**************************************************************************)

let rec nb_hyp sigma c = match EConstr.kind sigma c with
  | Prod(_,_,c2) -> if noccurn sigma 1 c2 then 1+(nb_hyp sigma c2) else nb_hyp sigma c2
  | _ -> 0

(* adding and removing tactics in the search table *)

let try_head_pattern c =
  try head_pattern_bound c
  with BoundPattern ->
    user_err (Pp.str "Head pattern or sub-pattern must be a global constant, a section variable, \
                      an if, case, or let expression, an application, or a projection.")

let with_uid c = { obj = c; uid = fresh_key () }

let secvars_of_idset s =
  Id.Set.fold (fun id p ->
      if is_section_variable id then
        Id.Pred.add id p
      else p) s Id.Pred.empty

let secvars_of_constr env sigma c =
  secvars_of_idset (Termops.global_vars_set env sigma c)

let secvars_of_global env gr =
  secvars_of_idset (vars_of_global_reference env gr)

let make_exact_entry env sigma info poly ?(name=PathAny) (c, cty, ctx) =
  let secvars = secvars_of_constr env sigma c in
  let cty = strip_outer_cast sigma cty in
    match EConstr.kind sigma cty with
    | Prod _ -> failwith "make_exact_entry"
    | _ ->
        let pat = Patternops.pattern_of_constr env sigma (EConstr.to_constr ~abort_on_undefined_evars:false sigma cty) in
	let hd =
	  try head_pattern_bound pat
	  with BoundPattern -> failwith "make_exact_entry"
	in
	let pri = match info.hint_priority with None -> 0 | Some p -> p in
	let pat = match info.hint_pattern with
	| Some pat -> snd pat
	| None -> pat
	in
        (Some hd,
	 { pri; poly; pat = Some pat; name;
	   db = None; secvars;
	   code = with_uid (Give_exact (c, cty, ctx)); })

let make_apply_entry env sigma (eapply,hnf,verbose) info poly ?(name=PathAny) (c, cty, ctx) =
  let cty = if hnf then hnf_constr env sigma cty else cty in
  match EConstr.kind sigma cty with
  | Prod _ ->
    let sigma' = Evd.merge_context_set univ_flexible sigma ctx in
    let ce = mk_clenv_from_env env sigma' None (c,cty) in
    let c' = clenv_type (* ~reduce:false *) ce in
    let pat = Patternops.pattern_of_constr env ce.evd (EConstr.to_constr ~abort_on_undefined_evars:false sigma c') in
    let hd =
      try head_pattern_bound pat
      with BoundPattern -> failwith "make_apply_entry" in
    let miss = clenv_missing ce in
    let nmiss = List.length miss in
    let secvars = secvars_of_constr env sigma c in
    let pri = match info.hint_priority with None -> nb_hyp sigma' cty + nmiss | Some p -> p in
    let pat = match info.hint_pattern with
      | Some p -> snd p | None -> pat
    in
    if Int.equal nmiss 0 then
      (Some hd,
       { pri; poly; pat = Some pat; name;
         db = None;
         secvars;
         code = with_uid (Res_pf(c,cty,ctx)); })
    else begin
      if not eapply then failwith "make_apply_entry";
      if verbose then begin
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
      end;
      (Some hd,
       { pri; poly; pat = Some pat; name;
         db = None; secvars;
         code = with_uid (ERes_pf(c,cty,ctx)); })
    end
  | _ -> failwith "make_apply_entry"

(* flags is (e,h,v) with e=true if eapply and h=true if hnf and v=true if verbose
   c is a constr
   cty is the type of constr *)

let pr_hint_term env sigma ctx = function
  | IsGlobRef gr -> pr_global gr
  | IsConstr (c, ctx) ->
     let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
     pr_econstr_env env sigma c

let warn_polymorphic_hint =
  CWarnings.create ~name:"polymorphic-hint" ~category:"automation"
         (fun hint -> strbrk"Using polymorphic hint " ++ hint ++
                        str" monomorphically" ++
                        strbrk" use Polymorphic Hint to use it polymorphically.")

let fresh_global_or_constr env sigma poly cr =
  let isgr, (c, ctx) =
    match cr with
    | IsGlobRef gr ->
      let (c, ctx) = UnivGen.fresh_global_instance env gr in
       true, (EConstr.of_constr c, ctx)
    | IsConstr (c, ctx) -> false, (c, ctx)
  in
    if poly then (c, ctx)
    else if Univ.ContextSet.is_empty ctx then (c, ctx)
    else begin
      if isgr then
        warn_polymorphic_hint (pr_hint_term env sigma ctx cr);
      Declare.declare_universe_context false ctx;
      (c, Univ.ContextSet.empty)
    end

let make_resolves env sigma flags info poly ?name cr =
  let c, ctx = fresh_global_or_constr env sigma poly cr in
  let cty = Retyping.get_type_of env sigma c in
  let try_apply f =
    try Some (f (c, cty, ctx)) with Failure _ -> None in
  let ents = List.map_filter try_apply
			     [make_exact_entry env sigma info poly ?name;
			      make_apply_entry env sigma flags info poly ?name]
  in
  if List.is_empty ents then
    user_err ~hdr:"Hint"
      (pr_leconstr_env env sigma c ++ spc() ++
        (if pi1 flags then str"cannot be used as a hint."
	else str "can be used as a hint only for eauto."));
  ents

(* used to add an hypothesis to the local hint database *)
let make_resolve_hyp env sigma decl =
  let hname = NamedDecl.get_id decl in
  let c = mkVar hname in
  try
    [make_apply_entry env sigma (true, true, false) empty_hint_info false
       ~name:(PathHints [VarRef hname])
       (c, NamedDecl.get_type decl, Univ.ContextSet.empty)]
  with
    | Failure _ -> []
    | e when Logic.catchable_exception e -> anomaly (Pp.str "make_resolve_hyp.")

(* REM : in most cases hintname = id *)

let make_unfold eref =
  let g = global_of_evaluable_reference eref in
  (Some g,
   { pri = 4;
     poly = false;
     pat = None;
     name = PathHints [g];
     db = None;
     secvars = secvars_of_global (Global.env ()) g;
     code = with_uid (Unfold_nth eref) })

let make_extern pri pat tacast =
  let hdconstr = Option.map try_head_pattern pat in
  (hdconstr,
   { pri = pri;
     poly = false;
     pat = pat;
     name = PathAny;
     db = None;
     secvars = Id.Pred.empty; (* Approximation *)
     code = with_uid (Extern tacast) })  

let make_mode ref m = 
  let open Term in
  let ty, _ = Global.type_of_global_in_context (Global.env ()) ref in
  let ctx, t = decompose_prod ty in
  let n = List.length ctx in
  let m' = Array.of_list m in
    if not (n == Array.length m') then
      user_err ~hdr:"Hint"
	(pr_global ref ++ str" has " ++ int n ++ 
	   str" arguments while the mode declares " ++ int (Array.length m'))
    else m'
      
let make_trivial env sigma poly ?(name=PathAny) r =
  let c,ctx = fresh_global_or_constr env sigma poly r in
  let sigma = Evd.merge_context_set univ_flexible sigma ctx in
  let t = hnf_constr env sigma (unsafe_type_of env sigma c) in
  let hd = head_constr sigma t in
  let ce = mk_clenv_from_env env sigma None (c,t) in
  (Some hd, { pri=1;
	      poly = poly;
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
  with Not_found -> Hint_db.empty ~name:dbname empty_transparent_state false

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
  let db = get_db dbname in
  let (ids, csts as st) = Hint_db.transparent_state db in
  let st' =
    match target with
    | HintsVariables -> (if b then Id.Pred.full else Id.Pred.empty), csts
    | HintsConstants -> ids, if b then Cpred.full else Cpred.empty
    | HintsReferences grs ->
       List.fold_left (fun (ids, csts) gr ->
       match gr with
       | EvalConstRef c -> (ids, (if b then Cpred.add else Cpred.remove) c csts)
       | EvalVarRef v -> (if b then Id.Pred.add else Id.Pred.remove) v ids, csts)
                      st grs
  in searchtable_add (dbname, Hint_db.set_transparent_state db st')

let remove_hint dbname grs =
  let db = get_db dbname in
  let db' = Hint_db.remove_list grs db in
    searchtable_add (dbname, db')

type hint_action =
  | CreateDB of bool * transparent_state
  | AddTransparency of evaluable_global_reference hints_transparency_target * bool
  | AddHints of hint_entry list
  | RemoveHints of GlobRef.t list
  | AddCut of hints_path
  | AddMode of GlobRef.t * hint_mode array

let add_cut dbname path =
  let db = get_db dbname in
  let db' = Hint_db.add_cut path db in
    searchtable_add (dbname, db')

let add_mode dbname l m =
  let db = get_db dbname in
  let db' = Hint_db.add_mode l m db in
    searchtable_add (dbname, db')

type hint_obj = {
  hint_local : bool;
  hint_name : string;
  hint_action : hint_action;
}

let load_autohint _ (kn, h) =
  let name = h.hint_name in
  match h.hint_action with
  | CreateDB (b, st) -> searchtable_add (name, Hint_db.empty ~name st b)
  | AddTransparency (grs, b) -> add_transparency name grs b
  | AddHints hints -> add_hint name hints
  | RemoveHints grs -> remove_hint name grs
  | AddCut path -> add_cut name path
  | AddMode (l, m) -> add_mode name l m

let open_autohint i (kn, h) =
  if Int.equal i 1 then match h.hint_action with
  | AddHints hints ->
    let add (_, hint) = statustable := KNmap.add hint.code.uid true !statustable in
    List.iter add hints
  | _ -> ()

let cache_autohint (kn, obj) =
  load_autohint 1 (kn, obj); open_autohint 1 (kn, obj)

let subst_autohint (subst, obj) =
  let subst_key gr =
    let (lab'', elab') = subst_global subst gr in
    let elab' = EConstr.of_constr elab' in
    let gr' =
      (try head_constr_bound Evd.empty elab'
       with Bound -> lab'')
    in if gr' == gr then gr else gr'
  in
  let subst_hint (k,data as hint) =
    let k' = Option.Smart.map subst_key k in
    let pat' = Option.Smart.map (subst_pattern subst) data.pat in
    let subst_mps subst c = EConstr.of_constr (subst_mps subst (EConstr.Unsafe.to_constr c)) in
    let code' = match data.code.obj with
      | Res_pf (c,t,ctx) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t'==t then data.code.obj else Res_pf (c', t',ctx)
      | ERes_pf (c,t,ctx) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t'==t then data.code.obj else ERes_pf (c',t',ctx)
      | Give_exact (c,t,ctx) ->
          let c' = subst_mps subst c in
	  let t' = subst_mps subst t in
          if c==c' && t'== t then data.code.obj else Give_exact (c',t',ctx)
      | Res_pf_THEN_trivial_fail (c,t,ctx) ->
          let c' = subst_mps subst c in
          let t' = subst_mps subst t in
          if c==c' && t==t' then data.code.obj else Res_pf_THEN_trivial_fail (c',t',ctx)
      | Unfold_nth ref ->
          let ref' = subst_evaluable_reference subst ref in
          if ref==ref' then data.code.obj else Unfold_nth ref'
      | Extern tac ->
	  let tac' = Genintern.generic_substitute subst tac in
	  if tac==tac' then data.code.obj else Extern tac'
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
    | CreateDB _ -> obj.hint_action
    | AddTransparency (target, b) ->
      let target' =
        match target with
        | HintsVariables -> target
        | HintsConstants -> target
        | HintsReferences grs ->
          let grs' = List.Smart.map (subst_evaluable_reference subst) grs in
          if grs == grs' then target
          else HintsReferences grs'
      in
      if target' == target then obj.hint_action else AddTransparency (target', b)
    | AddHints hintlist ->
      let hintlist' = List.Smart.map subst_hint hintlist in
      if hintlist' == hintlist then obj.hint_action else AddHints hintlist'
    | RemoveHints grs ->
      let grs' = List.Smart.map (subst_global_reference subst) grs in
      if grs == grs' then obj.hint_action else RemoveHints grs'
    | AddCut path ->
      let path' = subst_hints_path subst path in
      if path' == path then obj.hint_action else AddCut path'
    | AddMode (l,m) ->
      let l' = subst_global_reference subst l in
      if l' == l then obj.hint_action else AddMode (l', m)
  in
  if action == obj.hint_action then obj else { obj with hint_action = action }

let classify_autohint obj =
  match obj.hint_action with
  | AddHints [] -> Dispose
  | _ -> if obj.hint_local then Dispose else Substitute obj

let inAutoHint : hint_obj -> obj =
  declare_object {(default_object "AUTOHINT") with
                    cache_function = cache_autohint;
		    load_function = load_autohint;
		    open_function = open_autohint;
		    subst_function = subst_autohint;
		    classify_function = classify_autohint; }

let make_hint ?(local = false) name action = {
  hint_local = local;
  hint_name = name;
  hint_action = action;
}

let create_hint_db l n st b =
  let hint = make_hint ~local:l n (CreateDB (b, st)) in
  Lib.add_anonymous_leaf (inAutoHint hint)

let remove_hints local dbnames grs =
  let dbnames = if List.is_empty dbnames then ["core"] else dbnames in
    List.iter
      (fun dbname ->
        let hint = make_hint ~local dbname (RemoveHints grs) in
        Lib.add_anonymous_leaf (inAutoHint hint))
      dbnames

(**************************************************************************)
(*                     The "Hint" vernacular command                      *)
(**************************************************************************)
let add_resolves env sigma clist local dbnames =
  List.iter
    (fun dbname ->
      let r =
        List.flatten (List.map (fun (pri, poly, hnf, path, gr) ->
          make_resolves env sigma (true,hnf,not !Flags.quiet)
            pri poly ~name:path gr) clist)
      in
      let hint = make_hint ~local dbname (AddHints r) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_unfolds l local dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~local dbname (AddHints (List.map make_unfold l)) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_cuts l local dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~local dbname (AddCut l) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_mode l m local dbnames =
  List.iter
    (fun dbname ->
      let m' = make_mode l m in
      let hint = make_hint ~local dbname (AddMode (l, m')) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_transparency l b local dbnames =
  List.iter
    (fun dbname ->
      let hint = make_hint ~local dbname (AddTransparency (l, b)) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

let add_extern info tacast local dbname =
  let pat = match info.hint_pattern with
  | None -> None
  | Some (_, pat) -> Some pat
  in
  let hint = make_hint ~local dbname
		       (AddHints [make_extern (Option.get info.hint_priority) pat tacast]) in
  Lib.add_anonymous_leaf (inAutoHint hint)

let add_externs info tacast local dbnames =
  List.iter (add_extern info tacast local) dbnames

let add_trivials env sigma l local dbnames =
  List.iter
    (fun dbname ->
      let l = List.map (fun (name, poly, c) -> make_trivial env sigma poly ~name c) l in
      let hint = make_hint ~local dbname (AddHints l) in
      Lib.add_anonymous_leaf (inAutoHint hint))
    dbnames

type hnf = bool

type nonrec hint_info = hint_info

type hints_entry =
  | HintsResolveEntry of (hint_info * polymorphic * hnf * hints_path_atom * hint_term) list
  | HintsImmediateEntry of (hints_path_atom * polymorphic * hint_term) list
  | HintsCutEntry of hints_path
  | HintsUnfoldEntry of evaluable_global_reference list
  | HintsTransparencyEntry of evaluable_global_reference hints_transparency_target * bool
  | HintsModeEntry of GlobRef.t * hint_mode list
  | HintsExternEntry of hint_info * Genarg.glob_generic_argument

let default_prepare_hint_ident = Id.of_string "H"

exception Found of constr * types

let prepare_hint check (poly,local) env init (sigma,c) =
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
      mkNamedLambda id t (iter (replace_term sigma evar (mkVar id) c)) in
  let c' = iter c in
    let env = Global.env () in
    let empty_sigma = Evd.from_env env in
    if check then Pretyping.check_evars env empty_sigma sigma c';
    let diff = Univ.ContextSet.diff (Evd.universe_context_set sigma) (Evd.universe_context_set init) in
    if poly then IsConstr (c', diff)
    else if local then IsConstr (c', diff)
    else (Declare.declare_universe_context false diff;
	  IsConstr (c', Univ.ContextSet.empty))

let project_hint ~poly pri l2r r =
  let open EConstr in
  let open Coqlib in
  let gr = Smartlocate.global_with_alias r in
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  let t = Retyping.get_type_of env sigma c in
  let t =
    Tacred.reduce_to_quantified_ref env sigma (Lazy.force coq_iff_ref) t in
  let sign,ccl = decompose_prod_assum sigma t in
  let (a,b) = match snd (decompose_app sigma ccl) with
    | [a;b] -> (a,b)
    | _ -> assert false in
  let p =
    if l2r then build_coq_iff_left_proj () else build_coq_iff_right_proj () in
  let sigma, p = Evd.fresh_global env sigma p in
  let c = Reductionops.whd_beta sigma (mkApp (c, Context.Rel.to_extended_vect mkRel 0 sign)) in
  let c = it_mkLambda_or_LetIn
    (mkApp (p,[|mkArrow a (lift 1 b);mkArrow b (lift 1 a);c|])) sign in
  let id =
    Nameops.add_suffix (Nametab.basename_of_global gr) ("_proj_" ^ (if l2r then "l2r" else "r2l"))
  in
  let ctx = Evd.const_univ_entry ~poly sigma in
  let c = EConstr.to_constr sigma c in
  let c = Declare.declare_definition ~internal:Declare.InternalTacticRequest id (c,ctx) in
  let info = {Typeclasses.hint_priority = pri; hint_pattern = None} in
    (info,false,true,PathAny, IsGlobRef (Globnames.ConstRef c))

let interp_hints poly =
  fun h ->
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let f poly c =
    let evd,c = Constrintern.interp_open_constr env sigma c in
    let env = Global.env () in
    let sigma = Evd.from_env env in
      prepare_hint true (poly,false) env sigma (evd,c) in
  let fref r =
    let gr = global_with_alias r in
    Dumpglob.add_glob ?loc:r.CAst.loc gr;
    gr in
  let fr r = evaluable_of_global_reference env (fref r) in
  let fi c =
    match c with
    | HintsReference c ->
      let gr = global_with_alias c in
	(PathHints [gr], poly, IsGlobRef gr)
    | HintsConstr c -> (PathAny, poly, f poly c)
  in
  let fp = Constrintern.intern_constr_pattern env sigma in
  let fres (info, b, r) =
    let path, poly, gr = fi r in
    let info = { info with hint_pattern = Option.map fp info.hint_pattern } in
      (info, poly, b, path, gr)
  in
  let ft = function
    | HintsVariables -> HintsVariables
    | HintsConstants -> HintsConstants
    | HintsReferences lhints -> HintsReferences (List.map fr lhints)
  in
  let fp = Constrintern.intern_constr_pattern (Global.env()) in
  match h with
  | HintsResolve lhints -> HintsResolveEntry (List.map fres lhints)
  | HintsResolveIFF (l2r, lc, n) ->
    HintsResolveEntry (List.map (project_hint ~poly n l2r) lc)
  | HintsImmediate lhints -> HintsImmediateEntry (List.map fi lhints)
  | HintsUnfold lhints -> HintsUnfoldEntry (List.map fr lhints)
  | HintsTransparency (t, b) -> HintsTransparencyEntry (ft t, b)
  | HintsMode (r, l) -> HintsModeEntry (fref r, l)
  | HintsConstructors lqid ->
      let constr_hints_of_ind qid =
        let ind = global_inductive_with_alias qid in
	let mib,_ = Global.lookup_inductive ind in
        Dumpglob.dump_reference ?loc:qid.CAst.loc "<>" (string_of_qualid qid) "ind";
          List.init (nconstructors ind) 
	    (fun i -> let c = (ind,i+1) in
		      let gr = ConstructRef c in
			empty_hint_info, 
                        (Declareops.inductive_is_polymorphic mib), true,
			PathHints [gr], IsGlobRef gr)
      in HintsResolveEntry (List.flatten (List.map constr_hints_of_ind lqid))
  | HintsExtern (pri, patcom, tacexp) ->
      let pat =	Option.map (fp sigma) patcom in
      let l = match pat with None -> [] | Some (l, _) -> l in
      let ltacvars = List.fold_left (fun accu x -> Id.Set.add x accu) Id.Set.empty l in
      let env = Genintern.({ (empty_glob_sign env) with ltacvars }) in
      let _, tacexp = Genintern.generic_intern env tacexp in
      HintsExternEntry ({ hint_priority = Some pri; hint_pattern = pat }, tacexp)

let add_hints ~local dbnames0 h =
  if String.List.mem "nocore" dbnames0 then
    user_err Pp.(str "The hint database \"nocore\" is meant to stay empty.");
  let dbnames = if List.is_empty dbnames0 then ["core"] else dbnames0 in
  let env = Global.env() in
  let sigma = Evd.from_env env in
  match h with
  | HintsResolveEntry lhints -> add_resolves env sigma lhints local dbnames
  | HintsImmediateEntry lhints -> add_trivials env sigma lhints local dbnames
  | HintsCutEntry lhints -> add_cuts lhints local dbnames
  | HintsModeEntry (l,m) -> add_mode l m local dbnames
  | HintsUnfoldEntry lhints -> add_unfolds lhints local dbnames
  | HintsTransparencyEntry (lhints, b) ->
      add_transparency lhints b local dbnames
  | HintsExternEntry (info, tacexp) ->
      add_externs info tacexp local dbnames

let expand_constructor_hints env sigma lems =
  List.map_append (fun (evd,lem) ->
    match EConstr.kind sigma lem with
    | Ind (ind,u) ->
	List.init (nconstructors ind) 
		  (fun i ->
		   let ctx = Univ.ContextSet.diff (Evd.universe_context_set evd)
						  (Evd.universe_context_set sigma) in
		   not (Univ.ContextSet.is_empty ctx),
		   IsConstr (mkConstructU ((ind,i+1),u),ctx))
    | _ ->
       [match prepare_hint false (false,true) env sigma (evd,lem) with
	| IsConstr (c, ctx) ->
	   not (Univ.ContextSet.is_empty ctx), IsConstr (c, ctx)
	| IsGlobRef _ -> assert false (* Impossible return value *) ]) lems
(* builds a hint database from a constr signature *)
(* typically used with (lid, ltyp) = pf_hyps_types <some goal> *)

let constructor_hints env sigma eapply lems =
  let lems = expand_constructor_hints env sigma lems in
  List.map_append (fun (poly, lem) ->
      make_resolves env sigma (eapply,true,false) empty_hint_info poly lem) lems

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

let pr_hint_elt env sigma (c, _, _) = pr_econstr_env env sigma c

let pr_hint env sigma h = match h.obj with
  | Res_pf (c, _) -> (str"simple apply " ++ pr_hint_elt env sigma c)
  | ERes_pf (c, _) -> (str"simple eapply " ++ pr_hint_elt env sigma c)
  | Give_exact (c, _) -> (str"exact " ++ pr_hint_elt env sigma c)
  | Res_pf_THEN_trivial_fail (c, _) ->
      (str"simple apply " ++ pr_hint_elt env sigma c ++ str" ; trivial")
  | Unfold_nth c ->
    str"unfold " ++  pr_evaluable_reference c
  | Extern tac ->
    str "(*external*) " ++ Pputils.pr_glb_generic env tac

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
	      Hint_db.map_existential sigma ~secvars:Id.Pred.full hdc cl
	    else Hint_db.map_auto sigma ~secvars:Id.Pred.full hdc cl
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
let pr_applicable_hint () =
  let env = Global.env () in
  let pts = Proof_global.give_me_the_proof () in
  let glss,_,_,_,sigma = Proof.proof pts in
  match glss with
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
  let (ids, csts) = Hint_db.transparent_state db in
  hov 0
    ((if Hint_db.use_dn db then str"Discriminated database"
      else str"Non-discriminated database")) ++ fnl () ++
  hov 2 (str"Unfoldable variable definitions: " ++ pr_idpred ids) ++ fnl () ++
  hov 2 (str"Unfoldable constant definitions: " ++ pr_cpred csts) ++ fnl () ++
  hov 2 (str"Cut: " ++ pp_hints_path (Hint_db.cut db)) ++ fnl () ++
  content

(* Deprecated in the mli *)
let pr_hint_db db =
  let sigma, env = Pfedit.get_current_context () in
  pr_hint_db_env env sigma db

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

let warn_non_imported_hint =
  CWarnings.create ~name:"non-imported-hint" ~category:"automation"
         (fun (hint,mp) ->
          strbrk "Hint used but not imported: " ++ hint ++ print_mp mp)

let warn h x =
  let open Proofview in
  tclBIND tclENV     (fun env   ->
  tclBIND tclEVARMAP (fun sigma ->
          let hint = pr_hint env sigma h in
          let (mp, _, _) = KerName.repr h.uid in
          warn_non_imported_hint (hint,mp);
          Proofview.tclUNIT x))

let run_hint tac k = match !warn_hint with
| `LAX -> k tac.obj
| `WARN ->
  if is_imported tac then k tac.obj
  else Proofview.tclBIND (k tac.obj) (fun x -> warn tac x)
| `STRICT ->
  if is_imported tac then k tac.obj
  else Proofview.tclZERO (UserError (None, (str "Tactic failure.")))

let repr_hint h = h.obj
