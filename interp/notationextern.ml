(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Declaration of uninterpretation functions (i.e. printing rules)
    for notations *)

(*i*)
open Util
open Names
open Globnames
open Constrexpr
open Notation_term
open Glob_term
(*i*)

let notation_with_optional_scope_eq inscope1 inscope2 = match (inscope1,inscope2) with
  | LastLonelyNotation, LastLonelyNotation -> true
  | NotationInScope s1, NotationInScope s2 -> String.equal s1 s2
  | (LastLonelyNotation | NotationInScope _), _ -> false

let notation_with_optional_scope_compare inscope1 inscope2 = match inscope1, inscope2 with
  | LastLonelyNotation, LastLonelyNotation -> 0
  | LastLonelyNotation, _ -> -1
  | _, LastLonelyNotation -> 1
  | NotationInScope s1, NotationInScope s2 -> String.compare s1 s2

let entry_relative_level_eq t1 t2 = match t1, t2 with
  | LevelLt n1, LevelLt n2 -> Int.equal n1 n2
  | LevelLe n1, LevelLe n2 -> Int.equal n1 n2
  | LevelSome, LevelSome -> true
  | (LevelLt _ | LevelLe _ | LevelSome), _ -> false

let notation_entry_eq s1 s2 = match (s1,s2) with
  | InConstrEntry, InConstrEntry -> true
  | InCustomEntry s1, InCustomEntry s2 -> CustomName.equal s1 s2
  | (InConstrEntry | InCustomEntry _), _ -> false

let notation_entry_compare s1 s2 = match s1, s2 with
  | InConstrEntry, InConstrEntry -> 0
  | InConstrEntry, _ -> -1
  | _, InConstrEntry -> 1
  | InCustomEntry s1, InCustomEntry s2 -> CustomName.compare s1 s2

let notation_entry_level_eq
    { notation_entry = e1; notation_level = n1 }
    { notation_entry = e2; notation_level = n2 } =
  notation_entry_eq e1 e2 && Int.equal n1 n2

let notation_entry_relative_level_eq
    { notation_subentry = e1; notation_relative_level = n1; notation_position = s1 }
    { notation_subentry = e2; notation_relative_level = n2; notation_position = s2 } =
  notation_entry_eq e1 e2 && entry_relative_level_eq n1 n2 && s1 = s2

let notation_eq ntn1 ntn2 =
  notation_entry_eq ntn1.ntn_entry ntn2.ntn_entry
  && String.equal ntn1.ntn_key ntn2.ntn_key

let notation_compare ntn1 ntn2 =
  let c = notation_entry_compare ntn1.ntn_entry ntn2.ntn_entry in
  if c <> 0 then c else String.compare ntn1.ntn_key ntn2.ntn_key

let specific_notation_compare (scope1,ntn1) (scope2,ntn2) =
  let c = notation_with_optional_scope_compare scope1 scope2 in
  if c <> 0 then c
  else notation_compare ntn1 ntn2

let notation_binder_kind_eq k1 k2 = match k1, k2 with
| AsIdent, AsIdent -> true
| AsName, AsName -> true
| AsAnyPattern, AsAnyPattern -> true
| AsStrictPattern, AsStrictPattern -> true
| (AsIdent | AsName | AsAnyPattern | AsStrictPattern), _ -> false

let notation_binder_source_eq s1 s2 = match s1, s2 with
| NtnBinderParsedAsSomeBinderKind bk1, NtnBinderParsedAsSomeBinderKind bk2 -> notation_binder_kind_eq bk1 bk2
| NtnBinderParsedAsBinder, NtnBinderParsedAsBinder -> true
| NtnBinderParsedAsConstr bk1, NtnBinderParsedAsConstr bk2 -> notation_binder_kind_eq bk1 bk2
| (NtnBinderParsedAsSomeBinderKind _ | NtnBinderParsedAsBinder | NtnBinderParsedAsConstr _), _ -> false

let subscopes_eq (tmpscl1,scl1) (tmpscl2,scl2) =
  List.equal String.equal tmpscl1 tmpscl2 && List.equal String.equal scl1 scl2

let notation_var_constr_kind s1 s2 = match s1, s2 with
| NtnAlwaysConstr, NtnAlwaysConstr -> true
| NtnConstrForConstrAndPatternForPattern, NtnConstrForConstrAndPatternForPattern -> true
| (NtnAlwaysConstr | NtnConstrForConstrAndPatternForPattern), _ -> false

let ntpe_eq t1 t2 = match t1, t2 with
| NtnTypeVarConstr s1, NtnTypeVarConstr s2 -> notation_var_constr_kind s1 s2
| NtnTypeVarPattern s1, NtnTypeVarPattern s2 -> notation_binder_source_eq s1 s2
| NtnTypeVarBinders s1, NtnTypeVarBinders s2 -> notation_binder_source_eq s1 s2
| (NtnTypeVarConstr _ | NtnTypeVarPattern _ | NtnTypeVarBinders _), _ -> false

let var_attributes_eq ((entry1, sc1), binders1) ((entry2, sc2), binders2) =
  notation_entry_relative_level_eq entry1 entry2 &&
  subscopes_eq sc1 sc2 &&
  Id.Set.equal binders1 binders2

let rec notation_var_kind_eq t1 t2 = match t1, t2 with
| NtnTypeVar (attr1,t1), NtnTypeVar (attr2,t2) -> var_attributes_eq attr1 attr2 && ntpe_eq t1 t2
| NtnTypeVarList t1, NtnTypeVarList t2 -> notation_var_kind_eq t1 t2
| NtnTypeVarTuple l1, NtnTypeVarTuple l2 -> List.equal notation_var_kind_eq l1 l2
| (NtnTypeVar _ | NtnTypeVarList _ | NtnTypeVarTuple _), _ -> false

let vars_notation_type_eq (id1,t1) (id2,t2) =
(*  Id.equal id1 id2 && *) notation_var_kind_eq t1 t2

let interpretation_eq (vars1, t1 as x1) (vars2, t2 as x2) =
  x1 == x2 ||
  List.equal vars_notation_type_eq vars1 vars2 &&
  Notation_ops.eq_notation_constr (List.map fst vars1, List.map fst vars2) t1 t2

type level = notation_entry_level * entry_relative_level list

let level_eq ({ notation_entry = s1; notation_level = l1}, t1) ({ notation_entry = s2; notation_level = l2}, t2) =
  notation_entry_eq s1 s2 && Int.equal l1 l2 && List.equal entry_relative_level_eq t1 t2

(** Uninterpretation tables *)

type interp_rule =
  | NotationRule of Constrexpr.specific_notation
  | AbbrevRule of Globnames.abbreviation

let specific_notation_eq (sc1, ntn1) (sc2, ntn2) =
  notation_with_optional_scope_eq sc1 sc2 && notation_eq ntn1 ntn2

let interp_rule_eq r1 r2 = match r1, r2 with
| NotationRule n1, NotationRule n2 -> specific_notation_eq n1 n2
| AbbrevRule kn1, AbbrevRule kn2 -> KerName.equal kn1 kn2
| (AbbrevRule _ | NotationRule _), _ -> false

(* We define keys for glob_constr and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of GlobRef.t
  | Oth

module KeyOrd = struct
  type t = key
  let compare k1 k2 = match k1, k2 with
  | RefKey gr1, RefKey gr2 -> GlobRef.UserOrd.compare gr1 gr2
  | RefKey _, Oth -> -1
  | Oth, RefKey _ -> 1
  | Oth, Oth -> 0
  let canonize env k = match k with
  | Oth -> Oth
  | RefKey gr -> RefKey (Environ.QGlobRef.canonize env gr)
end

module KeyMap = Environ.QMap(Map.Make(KeyOrd))(KeyOrd)

type notation_applicative_status =
  | AppBoundedNotation of int
  | AppUnboundedNotation
  | NotAppNotation

let notation_applicative_status_eq s1 s2 = match s1, s2 with
| AppBoundedNotation n1, AppBoundedNotation n2 -> Int.equal n1 n2
| AppUnboundedNotation, AppUnboundedNotation -> true
| NotAppNotation, NotAppNotation -> true
| (AppBoundedNotation _ | AppUnboundedNotation | NotAppNotation), _ -> false

type notation_rule = {
  not_rule : interp_rule;
  not_patt : interpretation;
  not_status : notation_applicative_status;
}

let notation_rule_eq x1 x2 =
  x1 == x2 ||
    (interp_rule_eq x1.not_rule x2.not_rule &&
    interpretation_eq x1.not_patt x2.not_patt &&
    notation_applicative_status_eq x1.not_status x2.not_status)

module NotationSet :
sig

type t
val empty : t
val add : notation_rule -> t -> t
val remove : notation_rule -> t -> t
val repr : t -> notation_rule list

end =
struct

type diff = Add | Sub

type data = {
  ntn_todo : (diff * notation_rule) list;
  ntn_done : notation_rule list;
}

type t = data ref option

let empty = None

let push k r s = match s with
| None -> Some (ref { ntn_done = []; ntn_todo = [k, r] })
| Some { contents = s } ->
  Some (ref { ntn_done = s.ntn_done; ntn_todo = (k, r) :: s.ntn_todo })

let add r s = push Add r s

let remove r s = push Sub r s

let force s =
  if List.is_empty s.ntn_todo then None
  else
    let cmp r1 r2 = Notation_ops.strictly_finer_interpretation_than r1.not_patt r2.not_patt in
    (* strictly finer interpretation are kept in front *)
    let fold accu (knd, ntn) = match knd with
    | Add ->
      let finer, rest = List.partition (fun c -> cmp c ntn) accu in
      (finer @ ntn :: rest)
    | Sub ->
      List.remove_first (fun rule -> notation_rule_eq ntn rule) accu
    in
    Some (List.fold_left fold s.ntn_done (List.rev s.ntn_todo))

let repr s = match s with
| None -> []
| Some r ->
  match force !r with
  | None -> r.contents.ntn_done
  | Some ans ->
    let () = r := { ntn_done = ans; ntn_todo = [] } in
    ans

end

let keymap_add env key interp map =
  let old = try KeyMap.find env key map with Not_found -> NotationSet.empty in
  KeyMap.add env key (NotationSet.add interp old) map

let keymap_remove env key interp map =
  let old = try KeyMap.find env key map with Not_found -> NotationSet.empty in
  KeyMap.add env key (NotationSet.remove interp old) map

let keymap_find env key map =
  try NotationSet.repr (KeyMap.find env key map)
  with Not_found -> []

(* Scopes table : interpretation -> scope_name *)
let notations_key_table = Summary.ref
    ~stage:Summary.Stage.Interp
    ~name:"notation_uninterpretation"
    (KeyMap.empty : NotationSet.t KeyMap.t)

let glob_constr_keys c = match DAst.get c with
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> [RefKey (canonical_gr ref); Oth]
    | _ -> [Oth]
    end
  | GProj ((cst,_), _, _) -> [RefKey (canonical_gr (GlobRef.ConstRef cst))]
  | GRef (ref,_) -> [RefKey (canonical_gr ref)]
  | _ -> [Oth]

let cases_pattern_key c = match DAst.get c with
  | PatCstr (ref,_,_) -> RefKey (canonical_gr (GlobRef.ConstructRef ref))
  | _ -> Oth

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef (ref,_),args) -> RefKey(canonical_gr ref), AppBoundedNotation (List.length args)
  | NProj ((cst,_),args,_) -> RefKey(canonical_gr (GlobRef.ConstRef cst)), AppBoundedNotation (List.length args + 1)
  | NList (_,_,NApp (NRef (ref,_),args),_,_)
  | NBinderList (_,_,NApp (NRef (ref,_),args),_,_) ->
      RefKey (canonical_gr ref), AppBoundedNotation (List.length args)
  | NRef (ref,_) -> RefKey(canonical_gr ref), NotAppNotation
  | NApp (NList (_,_,NApp (NRef (ref,_),args),_,_), args') ->
      RefKey (canonical_gr ref), AppBoundedNotation (List.length args + List.length args')
  | NApp (NList (_,_,NApp (_,args),_,_), args') ->
      Oth, AppBoundedNotation (List.length args + List.length args')
  | NApp (NVar _,_) -> Oth, AppUnboundedNotation
  | NApp (_,args) -> Oth, AppBoundedNotation (List.length args)
  | NList (_,_,NApp (NVar x,_),_,_) when x = Notation_ops.ldots_var -> Oth, AppUnboundedNotation
  | _ -> Oth, NotAppNotation

let uninterp_notations env c =
  let open Summary.Ref in
  List.map_append (fun key -> keymap_find env key !notations_key_table)
    (glob_constr_keys c)

let uninterp_cases_pattern_notations env c =
  let open Summary.Ref in
  keymap_find env (cases_pattern_key c) !notations_key_table

let uninterp_ind_pattern_notations env ind =
  let open Summary.Ref in
  keymap_find env (RefKey (canonical_gr (GlobRef.IndRef ind))) !notations_key_table

let remove_uninterpretation env rule (metas,c as pat) =
  let open Summary.Ref in
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_remove env key { not_rule = rule; not_patt = pat; not_status = n } !notations_key_table

let declare_uninterpretation env rule (metas,c as pat) =
  let open Summary.Ref in
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_add env key { not_rule = rule; not_patt = pat; not_status = n } !notations_key_table

let freeze () =
  let open Summary.Ref in
  !notations_key_table

let unfreeze fkm =
  let open Summary.Ref in
  notations_key_table := fkm

let with_notation_uninterpretation_protection f x =
  let open Memprof_coq.Resource_bind in
  let& () = Util.protect_state ~freeze ~unfreeze in
  f x

(** Miscellaneous *)
type notation_use =
  | OnlyPrinting
  | OnlyParsing
  | ParsingAndPrinting
