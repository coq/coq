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

let entry_relative_level_eq t1 t2 = match t1, t2 with
  | LevelLt n1, LevelLt n2 -> Int.equal n1 n2
  | LevelLe n1, LevelLe n2 -> Int.equal n1 n2
  | LevelSome, LevelSome -> true
  | (LevelLt _ | LevelLe _ | LevelSome), _ -> false

let notation_entry_eq s1 s2 = match (s1,s2) with
  | InConstrEntry, InConstrEntry -> true
  | InCustomEntry s1, InCustomEntry s2 -> String.equal s1 s2
  | (InConstrEntry | InCustomEntry _), _ -> false

let notation_entry_level_eq
    { notation_entry = e1; notation_level = n1 }
    { notation_entry = e2; notation_level = n2 } =
  notation_entry_eq e1 e2 && Int.equal n1 n2

let notation_entry_relative_level_eq
    { notation_subentry = e1; notation_relative_level = n1; notation_position = s1 }
    { notation_subentry = e2; notation_relative_level = n2; notation_position = s2 } =
  notation_entry_eq e1 e2 && entry_relative_level_eq n1 n2 && s1 = s2

let notation_eq (from1,ntn1) (from2,ntn2) =
  notation_entry_eq from1 from2 && String.equal ntn1 ntn2

let pair_eq f g (x1, y1) (x2, y2) = f x1 x2 && g y1 y2

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

let ntpe_eq t1 t2 = match t1, t2 with
| NtnTypeConstr, NtnTypeConstr -> true
| NtnTypeBinder s1, NtnTypeBinder s2 -> notation_binder_source_eq s1 s2
| NtnTypeConstrList, NtnTypeConstrList -> true
| NtnTypeBinderList s1, NtnTypeBinderList s2 -> notation_binder_source_eq s1 s2
| (NtnTypeConstr | NtnTypeBinder _ | NtnTypeConstrList | NtnTypeBinderList _), _ -> false

let var_attributes_eq (_, ((entry1, sc1), binders1, tp1)) (_, ((entry2, sc2), binders2, tp2)) =
  notation_entry_relative_level_eq entry1 entry2 &&
  pair_eq (List.equal String.equal) (List.equal String.equal) sc1 sc2 &&
  Id.Set.equal binders1 binders2 &&
  ntpe_eq tp1 tp2

let interpretation_eq (vars1, t1 as x1) (vars2, t2 as x2) =
  x1 == x2 ||
  List.equal var_attributes_eq vars1 vars2 &&
  Notation_ops.eq_notation_constr (List.map fst vars1, List.map fst vars2) t1 t2

type level = notation_entry_level * entry_relative_level list

let level_eq ({ notation_entry = s1; notation_level = l1}, t1) ({ notation_entry = s2; notation_level = l2}, t2) =
  notation_entry_eq s1 s2 && Int.equal l1 l2 && List.equal entry_relative_level_eq t1 t2

(** Uninterpretation tables *)

type 'a interp_rule_gen =
  | NotationRule of Constrexpr.specific_notation
  | AbbrevRule of 'a

type interp_rule = KerName.t interp_rule_gen

let specific_notation_eq (sc1, (e1, s1)) (sc2, (e2, s2)) =
  notation_with_optional_scope_eq sc1 sc2 &&
  notation_entry_eq e1 e2 &&
  String.equal s1 s2

let interp_rule_eq r1 r2 = match r1, r2 with
| NotationRule n1, NotationRule n2 -> specific_notation_eq n1 n2
| AbbrevRule kn1, AbbrevRule kn2 -> KerName.equal kn1 kn2
| (AbbrevRule _ | NotationRule _), _ -> false

(* We define keys for glob_constr and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of GlobRef.t
  | Oth

let key_compare k1 k2 = match k1, k2 with
  | RefKey gr1, RefKey gr2 -> GlobRef.CanOrd.compare gr1 gr2
  | RefKey _, Oth -> -1
  | Oth, RefKey _ -> 1
  | Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

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

let keymap_add key interp map =
  let old = try KeyMap.find key map with Not_found -> NotationSet.empty in
  KeyMap.add key (NotationSet.add interp old) map

let keymap_remove key interp map =
  let old = try KeyMap.find key map with Not_found -> NotationSet.empty in
  KeyMap.add key (NotationSet.remove interp old) map

let keymap_find key map =
  try NotationSet.repr (KeyMap.find key map)
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

let uninterp_notations c =
  List.map_append (fun key -> keymap_find key !notations_key_table)
    (glob_constr_keys c)

let uninterp_cases_pattern_notations c =
  keymap_find (cases_pattern_key c) !notations_key_table

let uninterp_ind_pattern_notations ind =
  keymap_find (RefKey (canonical_gr (GlobRef.IndRef ind))) !notations_key_table

let remove_uninterpretation rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_remove key { not_rule = rule; not_patt = pat; not_status = n } !notations_key_table

let declare_uninterpretation rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_add key { not_rule = rule; not_patt = pat; not_status = n } !notations_key_table

let freeze () =
  !notations_key_table

let unfreeze fkm =
  notations_key_table := fkm

let with_notation_uninterpretation_protection f x =
  let fs = freeze () in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = unfreeze fs in
    Exninfo.iraise reraise

(** Miscellaneous *)
type notation_use =
  | OnlyPrinting
  | OnlyParsing
  | ParsingAndPrinting
