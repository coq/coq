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
open Nameops
open Libnames
open Glob_term
open Notationextern
open Constrexpr

(***********)
(* Universes *)

let expr_Type_sort = None, UAnonymous {rigid=UnivRigid}
let expr_SProp_sort = None, UNamed [CSProp, 0]
let expr_Prop_sort = None, UNamed [CProp, 0]
let expr_Set_sort = None, UNamed [CSet, 0]

let sort_name_expr_eq c1 c2 = match c1, c2 with
  | CSProp, CSProp
  | CProp, CProp
  | CSet, CSet -> true
  | CType q1, CType q2 -> Libnames.qualid_eq q1 q2
  | CRawType u1, CRawType u2 -> Univ.Level.equal u1 u2
  | (CSProp|CProp|CSet|CType _|CRawType _), _ -> false

let qvar_expr_eq c1 c2 = match c1, c2 with
  | CQVar q1, CQVar q2 -> Libnames.qualid_eq q1 q2
  | CQAnon _, CQAnon _ -> true
  | CRawQVar q1, CRawQVar q2 -> Sorts.QVar.equal q1 q2
  | (CQVar _ | CQAnon _ | CRawQVar _), _ -> false

let quality_expr_eq q1 q2 = match q1, q2 with
  | CQConstant q1, CQConstant q2 -> Sorts.Quality.Constants.equal q1 q2
  | CQualVar q1, CQualVar q2 -> qvar_expr_eq q1 q2
  | (CQConstant _ | CQualVar _), _ -> false

let relevance_expr_eq a b = match a, b with
  | CRelevant, CRelevant | CIrrelevant, CIrrelevant -> true
  | CRelevanceVar q1, CRelevanceVar q2 -> qvar_expr_eq q1 q2
  | (CRelevant | CIrrelevant | CRelevanceVar _), _ -> false

let relevance_info_expr_eq = Option.equal relevance_expr_eq

let univ_level_expr_eq u1 u2 =
  Glob_ops.glob_sort_gen_eq sort_name_expr_eq u1 u2

let sort_expr_eq (q1, l1) (q2, l2) =
  Option.equal qvar_expr_eq q1 q2 &&
  Glob_ops.glob_sort_gen_eq
    (List.equal (fun (x,m) (y,n) ->
      sort_name_expr_eq x y
      && Int.equal m n))
    l1 l2

let instance_expr_eq (q1,u1) (q2,u2) =
  List.equal quality_expr_eq q1 q2 && List.equal univ_level_expr_eq u1 u2

(***********************)
(* For binders parsing *)

let binder_kind_eq b1 b2 = match b1, b2 with
| Default bk1, Default bk2 -> Glob_ops.binding_kind_eq bk1 bk2
| Generalized (ck1, b1), Generalized (ck2, b2) ->
  Glob_ops.binding_kind_eq ck1 ck2 &&
  (if b1 then b2 else not b2)
| _ -> false

let default_binder_kind = Default Explicit

let names_of_local_assums bl =
  List.flatten (List.map (function CLocalAssum(l,_,_,_)->l|_->[]) bl)

let names_of_local_binders bl =
  List.flatten (List.map (function CLocalAssum(l,_,_,_)->l|CLocalDef(l,_,_,_)->[l]|CLocalPattern _ -> assert false) bl)

(**********************************************************************)
(* Functions on constr_expr *)

(* Note: redundant Number representations, such as -0 and +0 (and others),
   are considered different here. *)

let prim_token_eq t1 t2 = match t1, t2 with
| Number n1, Number n2 -> NumTok.Signed.equal n1 n2
| String s1, String s2 -> String.equal s1 s2
| (Number _ | String _), _ -> false

let explicitation_eq pos1 pos2 = match pos1, pos2 with
| ExplByName id1, ExplByName id2 -> Id.equal id1 id2
| ExplByPos n1, ExplByPos n2 -> Int.equal n1 n2
| (ExplByName _ | ExplByPos _), _ -> false

(* We use a functor to avoid passing the recursion all over the place *)
module EqGen (A:sig
    val constr_expr_eq : constr_expr -> constr_expr -> bool
    val cases_pattern_expr_eq : cases_pattern_expr -> cases_pattern_expr -> bool
  end) = struct

  open A

  let local_binder_eq l1 l2 = match l1, l2 with
    | CLocalDef (n1, _, e1, t1), CLocalDef (n2, _, e2, t2) ->
      CAst.eq Name.equal n1 n2 && constr_expr_eq e1 e2 && Option.equal constr_expr_eq t1 t2
    | CLocalAssum (n1, _, _, e1), CLocalAssum (n2, _, _, e2) ->
      (* Don't care about the metadata *)
      List.equal (CAst.eq Name.equal) n1 n2 && constr_expr_eq e1 e2
    | _ -> false

  let kinded_cases_pattern_expr_eq (p1,bk1) (p2,bk2) =
    cases_pattern_expr_eq p1 p2 && Glob_ops.binding_kind_eq bk1 bk2

  let notation_arg_kind_eq a1 a2 = match a1, a2 with
    | NtnTypeArgConstr a1, NtnTypeArgConstr a2 -> constr_expr_eq a1 a2
    | NtnTypeArgPattern b1, NtnTypeArgPattern b2 -> kinded_cases_pattern_expr_eq b1 b2
    | NtnTypeArgBinders bll1, NtnTypeArgBinders bll2 -> List.equal local_binder_eq bll1 bll2
    | (NtnTypeArgConstr _ | NtnTypeArgPattern _ | NtnTypeArgBinders _), _ -> false

  let rec notation_arg_type_eq a1 a2 = match a1, a2 with
    | NtnTypeArg v1, NtnTypeArg v2 -> notation_arg_kind_eq v1 v2
    | NtnTypeArgList l1, NtnTypeArgList l2 -> List.equal notation_arg_type_eq l1 l2
    | NtnTypeArgTuple l1, NtnTypeArgTuple l2 -> List.equal notation_arg_type_eq l1 l2
    | (NtnTypeArg _ | NtnTypeArgList _ | NtnTypeArgTuple _), _ -> false

  let notation_substitution_eq s1 s2 =
    List.equal notation_arg_type_eq s1 s2

  let rec cases_pattern_expr_eq p1 p2 =
    if CAst.(p1.v == p2.v) then true
    else match CAst.(p1.v, p2.v) with
    | CPatAlias(a1,i1), CPatAlias(a2,i2) ->
        CAst.eq Name.equal i1 i2 && cases_pattern_expr_eq a1 a2
    | CPatCstr(c1,a1,b1), CPatCstr(c2,a2,b2) ->
        qualid_eq c1 c2 &&
        Option.equal (List.equal cases_pattern_expr_eq) a1 a2 &&
        List.equal cases_pattern_expr_eq b1 b2
    | CPatAtom(r1), CPatAtom(r2) ->
      Option.equal qualid_eq r1 r2
    | CPatOr a1, CPatOr a2 ->
      List.equal cases_pattern_expr_eq a1 a2
    | CPatNotation (inscope1, n1, s1, l1), CPatNotation (inscope2, n2, s2, l2) ->
      Option.equal notation_with_optional_scope_eq inscope1 inscope2 &&
      notation_eq n1 n2 &&
      notation_substitution_eq s1 s2 &&
      List.equal cases_pattern_expr_eq l1 l2
    | CPatPrim i1, CPatPrim i2 ->
      prim_token_eq i1 i2
    | CPatRecord l1, CPatRecord l2 ->
      let equal (r1, e1) (r2, e2) =
        qualid_eq r1 r2 && cases_pattern_expr_eq e1 e2
      in
      List.equal equal l1 l2
    | CPatDelimiters(depth1,s1,e1), CPatDelimiters(depth2,s2,e2) ->
      depth1 = depth2 && String.equal s1 s2 && cases_pattern_expr_eq e1 e2
    | _ -> false

  let args_eq (a1,e1) (a2,e2) =
    Option.equal (CAst.eq explicitation_eq) e1 e2 &&
    constr_expr_eq a1 a2

  let case_expr_eq (e1, n1, p1) (e2, n2, p2) =
    constr_expr_eq e1 e2 &&
    Option.equal (CAst.eq Name.equal) n1 n2 &&
    Option.equal cases_pattern_expr_eq p1 p2

  let branch_expr_eq {CAst.v=(p1, e1)} {CAst.v=(p2, e2)} =
    List.equal (List.equal cases_pattern_expr_eq) p1 p2 &&
    constr_expr_eq e1 e2

  let recursion_order_expr_eq_r r1 r2 = match r1, r2 with
    | CStructRec i1, CStructRec i2 -> lident_eq i1 i2
    | CWfRec (i1,e1), CWfRec (i2,e2) ->
      constr_expr_eq e1 e2
    | CMeasureRec (i1, e1, o1), CMeasureRec (i2, e2, o2) ->
      Option.equal lident_eq i1 i2 &&
      constr_expr_eq e1 e2 && Option.equal constr_expr_eq o1 o2
    | _ -> false

  let recursion_order_expr_eq r1 r2 = CAst.eq recursion_order_expr_eq_r r1 r2

  let fix_expr_eq (id1,_,r1,bl1,a1,b1) (id2,_,r2,bl2,a2,b2) =
    (lident_eq id1 id2) &&
    Option.equal recursion_order_expr_eq r1 r2 &&
    List.equal local_binder_eq bl1 bl2 &&
    constr_expr_eq a1 a2 &&
    constr_expr_eq b1 b2

  let cofix_expr_eq (id1,_,bl1,a1,b1) (id2,_,bl2,a2,b2) =
    (lident_eq id1 id2) &&
    List.equal local_binder_eq bl1 bl2 &&
    constr_expr_eq a1 a2 &&
    constr_expr_eq b1 b2

  let instance_eq (x1,c1) (x2,c2) =
    Id.equal x1.CAst.v x2.CAst.v && constr_expr_eq c1 c2

  let constr_expr_eq e1 e2 =
    if CAst.(e1.v == e2.v) then true
    else match CAst.(e1.v, e2.v) with
      | CRef (r1,u1), CRef (r2,u2) -> qualid_eq r1 r2 && Option.equal instance_expr_eq u1 u2
      | CFix(id1,fl1), CFix(id2,fl2) ->
        lident_eq id1 id2 &&
        List.equal fix_expr_eq fl1 fl2
      | CCoFix(id1,fl1), CCoFix(id2,fl2) ->
        lident_eq id1 id2 &&
        List.equal cofix_expr_eq fl1 fl2
      | CProdN(bl1,a1), CProdN(bl2,a2) ->
        List.equal local_binder_eq bl1 bl2 &&
        constr_expr_eq a1 a2
      | CLambdaN(bl1,a1), CLambdaN(bl2,a2) ->
        List.equal local_binder_eq bl1 bl2 &&
        constr_expr_eq a1 a2
      | CLetIn(na1,a1,t1,b1), CLetIn(na2,a2,t2,b2) ->
        CAst.eq Name.equal na1 na2 &&
        constr_expr_eq a1 a2 &&
        Option.equal constr_expr_eq t1 t2 &&
        constr_expr_eq b1 b2
      | CAppExpl((r1,u1),al1), CAppExpl((r2,u2),al2) ->
        qualid_eq r1 r2 &&
        Option.equal instance_expr_eq u1 u2 &&
        List.equal constr_expr_eq al1 al2
      | CApp(e1,al1), CApp(e2,al2) ->
        constr_expr_eq e1 e2 &&
        List.equal args_eq al1 al2
      | CProj(e1,(p1,u1),al1,c1), CProj(e2,(p2,u2),al2,c2) ->
        e1 = (e2:bool) &&
        qualid_eq p1 p2 &&
        Option.equal instance_expr_eq u1 u2 &&
        List.equal args_eq al1 al2 &&
        constr_expr_eq c1 c2
      | CRecord l1, CRecord l2 ->
        let field_eq (r1, e1) (r2, e2) =
          qualid_eq r1 r2 && constr_expr_eq e1 e2
        in
        List.equal field_eq l1 l2
      | CCases(_,r1,a1,brl1), CCases(_,r2,a2,brl2) ->
        (* Don't care about the case_style *)
        Option.equal constr_expr_eq r1 r2 &&
        List.equal case_expr_eq a1 a2 &&
        List.equal branch_expr_eq brl1 brl2
      | CLetTuple (n1, (m1, e1), t1, b1), CLetTuple (n2, (m2, e2), t2, b2) ->
        List.equal (CAst.eq Name.equal) n1 n2 &&
        Option.equal (CAst.eq Name.equal) m1 m2 &&
        Option.equal constr_expr_eq e1 e2 &&
        constr_expr_eq t1 t2 &&
        constr_expr_eq b1 b2
      | CIf (e1, (n1, r1), t1, f1), CIf (e2, (n2, r2), t2, f2) ->
        constr_expr_eq e1 e2 &&
        Option.equal (CAst.eq Name.equal) n1 n2 &&
        Option.equal constr_expr_eq r1 r2 &&
        constr_expr_eq t1 t2 &&
        constr_expr_eq f1 f2
      | CHole _, CHole _ -> true
      | (CGenarg _ | CGenargGlob _), (CGenarg _ | CGenargGlob _) -> true
      | CPatVar i1, CPatVar i2 ->
        Id.equal i1 i2
      | CEvar (id1, c1), CEvar (id2, c2) ->
        Id.equal id1.CAst.v id2.CAst.v && List.equal instance_eq c1 c2
      | CSort s1, CSort s2 ->
        sort_expr_eq s1 s2
      | CCast(c1,k1,t1), CCast(c2,k2,t2) ->
        constr_expr_eq c1 c2 && Option.equal Glob_ops.cast_kind_eq k1 k2 && constr_expr_eq t1 t2
      | CNotation(inscope1, n1, s1), CNotation(inscope2, n2, s2) ->
        Option.equal notation_with_optional_scope_eq inscope1 inscope2 &&
        notation_eq n1 n2 &&
        notation_substitution_eq s1 s2
      | CPrim i1, CPrim i2 ->
        prim_token_eq i1 i2
      | CGeneralization (bk1, e1), CGeneralization (bk2, e2) ->
        Glob_ops.binding_kind_eq bk1 bk2 &&
        constr_expr_eq e1 e2
      | CDelimiters(depth1,s1,e1), CDelimiters(depth2,s2,e2) ->
        depth1 = depth2 &&
        String.equal s1 s2 &&
        constr_expr_eq e1 e2
      | CArray(u1,t1,def1,ty1), CArray(u2,t2,def2,ty2) ->
        Array.equal constr_expr_eq t1 t2 &&
        constr_expr_eq def1 def2 && constr_expr_eq ty1 ty2 &&
        Option.equal instance_expr_eq u1 u2
      | (CRef _ | CFix _ | CCoFix _ | CProdN _ | CLambdaN _ | CLetIn _ | CAppExpl _
        | CApp _ | CProj _ | CRecord _ | CCases _ | CLetTuple _ | CIf _ | CHole _
        | CGenarg _ | CGenargGlob _
        | CPatVar _ | CEvar _ | CSort _ | CCast _ | CNotation _ | CPrim _
        | CGeneralization _ | CDelimiters _ | CArray _), _ -> false

end

let constr_expr_eq_gen eq_constr eq_cases_pattern =
  let module Eq = EqGen(struct let constr_expr_eq = eq_constr let cases_pattern_expr_eq = eq_cases_pattern end) in
  Eq.constr_expr_eq

let cases_pattern_expr_eq_gen eq_constr eq_cases_pattern =
  let module Eq = EqGen(struct let constr_expr_eq = eq_constr let cases_pattern_expr_eq = eq_cases_pattern end) in
  Eq.cases_pattern_expr_eq

module Eq = EqGen(struct
    let rec constr_expr_eq c1 c2 = constr_expr_eq_gen constr_expr_eq cases_pattern_expr_eq c1 c2
    and cases_pattern_expr_eq c1 c2 = cases_pattern_expr_eq_gen constr_expr_eq cases_pattern_expr_eq c1 c2
  end)
include Eq

let rec cases_pattern_expr_eq_gen' eq_constr c = cases_pattern_expr_eq_gen eq_constr (cases_pattern_expr_eq_gen eq_constr (cases_pattern_expr_eq_gen' eq_constr)) c

let constr_expr_eq_gen eq_constr = constr_expr_eq_gen eq_constr (cases_pattern_expr_eq_gen' eq_constr)

let constr_loc c = CAst.(c.loc)
let cases_pattern_expr_loc cp = CAst.(cp.loc)

let local_binder_loc = let open CAst in function
  | CLocalAssum ({ loc } ::_,_,_,t)
  | CLocalDef ( { loc },_,t,None) -> Loc.merge_opt loc (constr_loc t)
  | CLocalDef ( { loc },_,b,Some t) -> Loc.merge_opt loc (Loc.merge_opt (constr_loc b) (constr_loc t))
  | CLocalAssum ([],_,_,_) -> assert false
  | CLocalPattern { loc } -> loc

let local_binders_loc bll = match bll with
  | []     -> None
  | h :: l -> Loc.merge_opt (local_binder_loc h) (local_binder_loc (List.last bll))

(** Folds and maps *)
let is_constructor id =
  match
    Smartlocate.global_of_extended_global
      (Nametab.locate_extended (qualid_of_ident id))
  with
  | exception Not_found -> false
  | None -> false
  | Some gref -> Globnames.isConstructRef gref

let notation_arg_kind_fold k1 k2 k3 acc = function
  | NtnTypeArgConstr a -> k1 acc a
  | NtnTypeArgPattern (pat,_) -> k2 acc pat
  | NtnTypeArgBinders binder -> k3 acc binder

let rec notation_arg_type_fold k1 k2 k3 acc = function
  | NtnTypeArg a -> notation_arg_kind_fold k1 k2 k3 acc a
  | NtnTypeArgList l -> List.fold_left (notation_arg_type_fold k1 k2 k3) acc l
  | NtnTypeArgTuple l -> List.fold_left (notation_arg_type_fold k1 k2 k3) acc l

let notation_arg_kind_fold_map k1 k2 k3 acc = function
  | NtnTypeArgConstr a -> let acc, a = k1 acc a in acc, NtnTypeArgConstr a
  | NtnTypeArgPattern (pat,kd) -> let acc, pat = k2 acc pat in acc, NtnTypeArgPattern (pat,kd)
  | NtnTypeArgBinders binder -> let acc, binder = k3 acc binder in acc, NtnTypeArgBinders binder

let rec notation_arg_type_fold_map k1 k2 k3 acc = function
  | NtnTypeArg a -> let acc, a = notation_arg_kind_fold_map k1 k2 k3 acc a in acc, NtnTypeArg a
  | NtnTypeArgList l -> let acc, l = List.fold_left_map (notation_arg_type_fold_map k1 k2 k3) acc l in acc, NtnTypeArgList l
  | NtnTypeArgTuple l -> let acc, l = List.fold_left_map (notation_arg_type_fold_map k1 k2 k3) acc l in acc, NtnTypeArgTuple l

let notation_arg_kind_map k1 k2 k3 = function
  | NtnTypeArgConstr a -> NtnTypeArgConstr (k1 a)
  | NtnTypeArgPattern (pat,kd) -> NtnTypeArgPattern (k2 pat,kd)
  | NtnTypeArgBinders binder -> NtnTypeArgBinders (k3 binder)

let rec notation_arg_type_map k1 k2 k3 = function
  | NtnTypeArg a -> NtnTypeArg (notation_arg_kind_map k1 k2 k3 a)
  | NtnTypeArgList l -> NtnTypeArgList (List.map (notation_arg_type_map k1 k2 k3) l)
  | NtnTypeArgTuple l -> NtnTypeArgTuple (List.map (notation_arg_type_map k1 k2 k3) l)

(* [eacc] is a pair [(e,acc)] where [e] is updated at traversal of a
   variable by [g] and [acc] is the result of map-folding constr subterms
   (i.e.  basically subterms in Cast and Notation) using [f];
   By map-folding is meant that [f] updates both [e] and [acc]. *)
let rec cases_pattern_fold_names g f eacc pt = match CAst.(pt.v) with
  | CPatRecord l ->
    List.fold_left (fun eacc (r, cp) -> cases_pattern_fold_names g f eacc cp) eacc l
  | CPatAlias (pat,{CAst.v=na}) -> Name.fold_right (fun na (e,acc) -> (g na e,acc)) na (cases_pattern_fold_names g f eacc pat)
  | CPatOr (patl) ->
    List.fold_left (cases_pattern_fold_names g f) eacc patl
  | CPatCstr (_,patl1,patl2) ->
    List.fold_left (cases_pattern_fold_names g f)
      (Option.fold_left (List.fold_left (cases_pattern_fold_names g f)) eacc patl1) patl2
  | CPatNotation (_,_,subst,patl') ->
    List.fold_left (cases_pattern_fold_names g f)
      (List.fold_right (fun a x ->
           notation_arg_type_fold f
             (cases_pattern_fold_names g f)
             (fun eacc _ -> eacc) x a)
           subst eacc) patl'
  | CPatDelimiters (_,_,pat) -> cases_pattern_fold_names g f eacc pat
  | CPatAtom (Some qid)
      when qualid_is_ident qid && not (is_constructor @@ qualid_basename qid) ->
      let (e, acc) = eacc in
      (g (qualid_basename qid) e, acc)
  | CPatPrim _ | CPatAtom _ -> eacc
  | CPatCast (p,t) ->
      cases_pattern_fold_names g f (f eacc t) p

let ids_of_pattern_list p =
  fst (List.fold_left
    (List.fold_left (cases_pattern_fold_names Id.Set.add (fun eacc _ -> eacc)))
    (Id.Set.empty,()) p)

let ids_of_cases_tomatch tms =
  List.fold_right
    (fun (_, ona, indnal) l ->
       Option.fold_right (fun t ids -> fst (cases_pattern_fold_names Id.Set.add (fun eacc _ -> eacc) (ids,()) t))
         indnal
         (Option.fold_right (CAst.with_val (Name.fold_right Id.Set.add)) ona l))
    tms Id.Set.empty

(* [e] collects data from binders using [g];
   [acc] accumulates over "constr" subterms using [f];
   [k] is a continuation, working on the updated [e] *)
let fold_local_binder k g f e acc = let open CAst in function
  | CLocalAssum (nal,_,bk,t) ->
    let nal = List.(map (fun {v} -> v) nal) in
    let e' = List.fold_right (Name.fold_right g) nal e in
    k e' (f e acc t)
  | CLocalDef ( { v = na },_,c,t) ->
    let e' = Name.fold_right g na e in
    k e' (Option.fold_left (f e) (f e acc c) t)
  | CLocalPattern pat ->
    let e, acc = cases_pattern_fold_names g (fun (e,acc) t -> (e,f e acc t)) (e,acc) pat in
    k e acc

let rec fold_local_binders g f e acc b = function
  | decl :: l ->
    fold_local_binder (fun e acc -> fold_local_binders g f e acc b l) g f e acc decl
  | [] ->
    f e acc b

(* [n] collects data from binders using [g];
   [acc] accumulates over subterms using [f] *)
let fold_constr_expr_with_binders g f e acc = CAst.with_val (function
    | CAppExpl ((_,_),l) -> List.fold_left (f e) acc l
    | CApp (t,l) -> List.fold_left (f e) (f e acc t) (List.map fst l)
    | CProj (_,_,l,t) -> f e (List.fold_left (f e) acc (List.map fst l)) t
    | CProdN (l,b) | CLambdaN (l,b) -> fold_local_binders g f e acc b l
    | CLetIn (na,a,t,b) ->
      f (Name.fold_right g (na.CAst.v) e) (Option.fold_left (f e) (f e acc a) t) b
    | CCast (a,_,b) -> f e (f e acc a) b
    | CNotation (_,_,subst) ->
      List.fold_left (notation_arg_type_fold
             (f e)
             (fun acc a -> snd (cases_pattern_fold_names g (fun (e,acc) t -> (e,f e acc t)) (e,acc) a))
             (fun acc a -> fold_local_binders g f e acc (CAst.make @@ CHole None) a))
        acc subst
    | CGeneralization (_,c) -> f e acc c
    | CDelimiters (_,_,a) -> f e acc a
    | CRecord l -> List.fold_left (fun acc (id, c) -> f e acc c) acc l
    | CCases (sty,rtnpo,al,bl) ->
      let ids = ids_of_cases_tomatch al in
      let acc = Option.fold_left (f (Id.Set.fold g ids e)) acc rtnpo in
      let acc = List.fold_left (f e) acc (List.map (fun (fst,_,_) -> fst) al) in
      List.fold_right (fun {CAst.v=(patl,rhs)} acc ->
          let (e,acc) = List.fold_left (List.fold_left (cases_pattern_fold_names g (fun (e,acc) t -> (e,f e acc t)))) (e,acc) patl in
          f e acc rhs) bl acc
    | CLetTuple (nal,(ona,po),b,c) ->
      let e' = List.fold_right (CAst.with_val (Name.fold_right g)) nal e in
      f (Option.fold_right (CAst.with_val (Name.fold_right g)) ona e') (f e acc b) c
    | CIf (c,(ona,po),b1,b2) ->
      let acc = f e (f e (f e acc b1) b2) c in
      Option.fold_left
        (f (Option.fold_right (CAst.with_val (Name.fold_right g)) ona e)) acc po
    | CFix (_,l) ->
      let e' = List.fold_right (fun ( { CAst.v = id },_,_,_,_,_) -> g id) l e in
      List.fold_right (fun (_,_,ro,lb,t,c) acc ->
          fold_local_binders g f e'
            (fold_local_binders g f e acc t lb) c lb) l acc
    | CCoFix (_,_) ->
      Feedback.msg_warning (strbrk "Capture check in multiple binders not done"); acc
    | CArray (_u,t,def,ty) -> f e (f e (Array.fold_left (f e) acc t) def) ty
    | CHole _ | CGenarg _ | CGenargGlob _ | CEvar _ | CPatVar _ | CSort _ | CPrim _ | CRef _ ->
      acc
  )

let rec free_vars_of_constr_expr_gen bdvars ids = function
  | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
    let id = qualid_basename qid in
    if Id.List.mem id bdvars then ids else Id.Set.add id ids
  | c -> fold_constr_expr_with_binders (fun a ids -> a::ids) free_vars_of_constr_expr_gen bdvars ids c

let free_vars_of_constr_expr c =
  free_vars_of_constr_expr_gen [] Id.Set.empty c

let free_vars_of_cases_pattern_expr c =
  snd (cases_pattern_fold_names (fun a ids -> a::ids)
    (fun (bdvars,ids) t -> (bdvars,free_vars_of_constr_expr_gen bdvars ids t))
    ([],Id.Set.empty) c)

let free_vars_of_local_binders bl =
  fold_local_binders (fun a ids -> a::ids)
    free_vars_of_constr_expr_gen
    [] Id.Set.empty (CAst.make @@ CHole (None)) bl

let names_of_constr_expr c =
  let vars = ref Id.Set.empty in
  let rec aux () () = function
    | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
      let id = qualid_basename qid in vars := Id.Set.add id !vars
    | c -> fold_constr_expr_with_binders (fun a () -> vars := Id.Set.add a !vars) aux () () c
  in aux () () c; !vars

let occur_var_constr_expr id c = Id.Set.mem id (free_vars_of_constr_expr c)

(* applies [f] on a cases pattern, where [f] depends on an "environent" [e]
   which is updated by [g] at each traversal of a binder *)
let rec fold_map_cases_pattern g f e (CAst.{v=pt;loc} as p) = match pt with
  | CPatRecord l ->
    let e, l = List.fold_left_map (fun e (r, cp) -> let e, cp = fold_map_cases_pattern g f e cp in e, (r, cp)) e l in
    e, CAst.make ?loc (CPatRecord l)
  | CPatAlias (pat,({CAst.v=na} as lna)) ->
    let e, p = fold_map_cases_pattern g f e pat in
    let e = Name.fold_right g na e in
    e, CAst.make ?loc (CPatAlias (pat,lna))
  | CPatOr patl ->
    let e, patl = List.fold_left_map (fold_map_cases_pattern g f) e patl in
    e, CAst.make ?loc (CPatOr patl)
  | CPatCstr (c,patl1,patl2) ->
    let e, patl1 = Option.fold_left_map (List.fold_left_map (fold_map_cases_pattern g f)) e patl1 in
    let e, patl2 = List.fold_left_map (fold_map_cases_pattern g f) e patl2 in
    e, CAst.make ?loc (CPatCstr (c,patl1,patl2))
  | CPatNotation (sc,ntn,subst,patl') ->
    let e, subst = List.fold_left_map
        (notation_arg_type_fold_map
          (fun e c -> (e, f e c))
          (fold_map_cases_pattern g f)
          (fun _ _ -> assert false))
        e subst in
    let e, patl' = List.fold_left_map (fold_map_cases_pattern g f) e patl' in
    e, CAst.make ?loc (CPatNotation (sc,ntn,subst,patl'))
  | CPatDelimiters (depth,d,pat) ->
    let e, p = fold_map_cases_pattern g f e pat in
    e, CAst.make ?loc (CPatDelimiters (depth,d,pat))
  | CPatAtom (Some qid)
      when qualid_is_ident qid && not (is_constructor @@ qualid_basename qid) ->
    g (qualid_basename qid) e, p
  | CPatPrim _ | CPatAtom _ -> (e,p)
  | CPatCast (pat,t) ->
    let e, pat = fold_map_cases_pattern g f e pat in
    let t = f e t in
    e, CAst.make ?loc (CPatCast (pat,t))

(* Used in correctness and interface *)
let map_binder g e nal = List.fold_right (CAst.with_val (Name.fold_right g)) nal e

(* applies [f] on a local binder, where [f] depends on an "environent" [e]
   which is updated by [g] at each traversal of a binder *)
let fold_map_local_binder g f e = function
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  | CLocalAssum(nal,r,k,ty) ->
    (map_binder g e nal, CLocalAssum(nal,r,k,f e ty))
  | CLocalDef( { loc ; v = na } as cna,r,c,ty) ->
    (Name.fold_right g na e, CLocalDef(cna,r,f e c,Option.map (f e) ty))
  | CLocalPattern pat ->
    let e, pat = fold_map_cases_pattern g f e pat in
    (e, CLocalPattern pat)

(* applies [f] on local binders, where [f] depends on an "environent" [e]
   which is updated by [g] at each traversal of a binder *)
let fold_map_local_binders g f e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let (e,rbl) = List.fold_left (fun (e,bl) b -> let (e, b) = fold_map_local_binder g f e b in (e,b::bl)) (e,[]) bl in
  (e, List.rev rbl)

(* applies [f] on an constr_expr, where [f] depends on an "environent" [e]
   which is updated by [g] at each traversal of a binder *)
let map_constr_expr_with_binders g f e = CAst.map (function
    | CAppExpl (r,l) -> CAppExpl (r,List.map (f e) l)
    | CApp (a,l) ->
      CApp (f e a,List.map (fun (a,i) -> (f e a,i)) l)
    | CProj (expl,p,l,a) ->
      CProj (expl,p,List.map (fun (a,i) -> (f e a,i)) l,f e a)
    | CProdN (bl,b) ->
      let (e,bl) = fold_map_local_binders g f e bl in CProdN (bl,f e b)
    | CLambdaN (bl,b) ->
      let (e,bl) = fold_map_local_binders g f e bl in CLambdaN (bl,f e b)
    | CLetIn (na,a,t,b) ->
      CLetIn (na,f e a,Option.map (f e) t,f (Name.fold_right g (na.CAst.v) e) b)
    | CCast (a,k,c) -> CCast (f e a, k, f e c)
    | CNotation (inscope,n,subst) ->
      (* This is an approximation because we don't know what binds what *)
      CNotation (inscope,n,
                 List.map (notation_arg_type_map (f e)
                             (fun a -> snd (fold_map_cases_pattern g f e a))
                             (fun a -> snd (fold_map_local_binders g f e a))) subst)
    | CGeneralization (b,c) -> CGeneralization (b,f e c)
    | CDelimiters (depth,s,a) -> CDelimiters (depth,s,f e a)
    | CRecord l -> CRecord (List.map (fun (id, c) -> (id, f e c)) l)
    | CCases (sty,rtnpo,a,bl) ->
      let bl = List.map (fun {CAst.v=(patl,rhs);loc} ->
          let ids = ids_of_pattern_list patl in
          CAst.make ?loc (patl,f (Id.Set.fold g ids e) rhs)) bl in
      let ids = ids_of_cases_tomatch a in
      let po = Option.map (f (Id.Set.fold g ids e)) rtnpo in
      CCases (sty, po, List.map (fun (tm,x,y) -> f e tm,x,y) a,bl)
    | CLetTuple (nal,(ona,po),b,c) ->
      let e' = List.fold_right (CAst.with_val (Name.fold_right g)) nal e in
      let e'' = Option.fold_right (CAst.with_val (Name.fold_right g)) ona e in
      CLetTuple (nal,(ona,Option.map (f e'') po),f e b,f e' c)
    | CIf (c,(ona,po),b1,b2) ->
      let e' = Option.fold_right (CAst.with_val (Name.fold_right g)) ona e in
      CIf (f e c,(ona,Option.map (f e') po),f e b1,f e b2)
    | CFix (id,dl) ->
      CFix (id,List.map (fun (id,r,n,bl,t,d) ->
          let (e',bl') = fold_map_local_binders g f e bl in
          let t' = f e' t in
          (* Note: fix names should be inserted before the arguments... *)
          let e'' = List.fold_left (fun e ({ CAst.v = id },_,_,_,_,_) -> g id e) e' dl in
          let d' = f e'' d in
          (id,r,n,bl',t',d')) dl)
    | CCoFix (id,dl) ->
      CCoFix (id,List.map (fun (id,r,bl,t,d) ->
          let (e',bl') = fold_map_local_binders g f e bl in
          let t' = f e' t in
          let e'' = List.fold_left (fun e ({ CAst.v = id },_,_,_,_) -> g id e) e' dl in
          let d' = f e'' d in
          (id,r,bl',t',d')) dl)
    | CArray (u, t, def, ty) ->
      CArray (u, Array.map (f e) t, f e def, f e ty)
    | CHole _ | CGenarg _ | CGenargGlob _ | CEvar _ | CPatVar _ | CSort _
    | CPrim _ | CRef _ as x -> x
  )

(* Used in constrintern *)
let rec replace_vars_constr_expr l r =
  match r with
  | { CAst.loc; v = CRef (qid,us) } as x when qualid_is_ident qid ->
    let id = qualid_basename qid in
    (try CAst.make ?loc @@ CRef (qualid_of_ident ?loc (Id.Map.find id l),us)
     with Not_found -> x)
  | cn -> map_constr_expr_with_binders Id.Map.remove replace_vars_constr_expr l cn

(* Returns the ranges of locs of the notation that are not occupied by args  *)
(* and which are then occupied by proper symbols of the notation (or spaces) *)

let locs_of_notation ?loc locs ntn =
  let unloc loc = Option.cata Loc.unloc (0,0) loc in
  let (bl, el) = unloc loc        in
  let locs =  List.map unloc locs in
  let rec aux pos = function
    | [] -> if Int.equal pos el then [] else [(pos,el)]
    | (ba,ea)::l -> if Int.equal pos ba then aux ea l else (pos,ba)::aux ea l
  in aux bl (List.sort (fun l1 l2 -> fst l1 - fst l2) locs)

let ntn_loc ?loc subst =
  locs_of_notation ?loc
    (List.fold_left (notation_arg_type_fold (fun acc c -> constr_loc c :: acc)
                        (fun acc x -> cases_pattern_expr_loc x :: acc)
                        (fun acc bl -> local_binders_loc bl :: acc)) [] subst)

let error_invalid_pattern_notation ?loc () =
  CErrors.user_err ?loc  (str "Invalid notation for pattern.")

(** Pseudo-constructors *)

let mkIdentC id   = CAst.make @@ CRef (qualid_of_ident id,None)
let mkRefC r      = CAst.make @@ CRef (r,None)
let mkCastC (a,k,t) = CAst.make @@ CCast (a,k,t)
let mkLambdaC (idl,bk,a,b) = CAst.make @@ CLambdaN ([CLocalAssum (idl,None,bk,a)],b)
let mkLetInC  (id,a,t,b)   = CAst.make @@ CLetIn (id,a,t,b)
let mkProdC   (idl,bk,a,b) = CAst.make @@ CProdN ([CLocalAssum (idl,None,bk,a)],b)

let mkAppC (f,l) =
  let l = List.map (fun x -> (x,None)) l in
  match CAst.(f.v) with
  | CApp (g,l') -> CAst.make @@ CApp (g, l' @ l)
  | _           -> CAst.make @@ CApp (f, l)

let mkProdCN ?loc bll c =
  if bll = [] then c else
  CAst.make ?loc @@ CProdN (bll,c)

let mkLambdaCN ?loc bll c =
  if bll = [] then c else
  CAst.make ?loc @@ CLambdaN (bll,c)

let mkCProdN ?loc bll c =
  CAst.make ?loc @@ CProdN (bll,c)

let mkCLambdaN ?loc bll c =
  CAst.make ?loc @@ CLambdaN (bll,c)

let coerce_reference_to_id qid =
  if qualid_is_ident qid then qualid_basename qid
  else
    CErrors.user_err ?loc:qid.CAst.loc
      (str "This expression should be a simple identifier.")

let coerce_to_id = function
  | { CAst.loc; v = CRef (qid,None) } when qualid_is_ident qid ->
    CAst.make ?loc @@ qualid_basename qid
  | { CAst.loc; _ } -> CErrors.user_err ?loc
                         (str "This expression should be a simple identifier.")

let coerce_to_name = function
  | { CAst.loc; v = CRef (qid,None) } when qualid_is_ident qid ->
    CAst.make ?loc @@ Name (qualid_basename qid)
  | { CAst.loc; v = CHole (None) } -> CAst.make ?loc Anonymous
  | { CAst.loc; _ } -> CErrors.user_err ?loc
                         (str "This expression should be a name.")

let mkCPatOr ?loc = function
  | [pat] -> pat
  | disjpat -> CAst.make ?loc @@ (CPatOr disjpat)

let mkAppPattern ?loc p lp =
  if List.is_empty lp then p else
  let open CAst in
  make ?loc @@ (match p.v with
  | CPatAtom (Some r) -> CPatCstr (r, None, lp)
  | CPatCstr (r, None, l2) ->
     CErrors.user_err ?loc:p.loc
                      (Pp.str "Nested applications not supported.")
  | CPatCstr (r, l1, l2) -> CPatCstr (r, l1 , l2@lp)
  | CPatNotation (inscope, n, s, l) -> CPatNotation (inscope, n , s, l@lp)
  | _ -> CErrors.user_err ?loc:p.loc (Pp.str "Such pattern cannot have arguments."))

let notation_arg_kind_map_coerce k1 k2 k3 = function
  | NtnTypeArgConstr a -> NtnTypeArgPattern (k1 a)
  | NtnTypeArgPattern (pat,kd) -> NtnTypeArgPattern (k2 pat,kd)
  | NtnTypeArgBinders binder -> NtnTypeArgBinders (k3 binder)

let rec notation_arg_type_map_coerce k1 k2 k3 = function
  | NtnTypeArg a -> NtnTypeArg (notation_arg_kind_map_coerce k1 k2 k3 a)
  | NtnTypeArgList l -> NtnTypeArgList (List.map (notation_arg_type_map_coerce k1 k2 k3) l)
  | NtnTypeArgTuple l -> NtnTypeArgTuple (List.map (notation_arg_type_map_coerce k1 k2 k3) l)

let rec coerce_to_cases_pattern_expr c = CAst.map_with_loc (fun ?loc -> function
  | CRef (r,None) ->
     CPatAtom (Some r)
  | CHole (None) ->
     CPatAtom None
  | CLetIn ({CAst.loc;v=Name id},b,None,{ CAst.v = CRef (qid,None) })
      when qualid_is_ident qid && Id.equal id (qualid_basename qid) ->
      CPatAlias (coerce_to_cases_pattern_expr b, CAst.(make ?loc @@ Name id))
  | CApp (p,args) when List.for_all (fun (_,e) -> e=None) args ->
     (mkAppPattern (coerce_to_cases_pattern_expr p) (List.map (fun (a,_) -> coerce_to_cases_pattern_expr a) args)).CAst.v
  | CAppExpl ((r,i),args) ->
     CPatCstr (r,Some (List.map coerce_to_cases_pattern_expr args),[])
  | CNotation (inscope,ntn,subst) ->
     CPatNotation (inscope,ntn,List.map (notation_arg_type_map_coerce
                                           (fun c -> (coerce_to_cases_pattern_expr c, Explicit))
                                           (fun c -> c)
                                           (fun _ -> assert false)) subst, [])
  | CPrim p ->
     CPatPrim p
  | CRecord l ->
     CPatRecord (List.map (fun (r,p) -> (r,coerce_to_cases_pattern_expr p)) l)
  | CDelimiters (depth,s,p) ->
     CPatDelimiters (depth,s,coerce_to_cases_pattern_expr p)
  | CCast (p,Some Constr.DEFAULTcast, t) ->
    CPatCast (coerce_to_cases_pattern_expr p,t)
  | CLambdaN _ | CProdN _ | CSort _ | CLetIn _ | CGeneralization _
  | CRef (_, Some _) | CCast (_, (Some (VMcast|NATIVEcast) | None), _)
  | CFix _ | CCoFix _ | CApp _ | CProj _ | CCases _ | CLetTuple _ | CIf _
  | CPatVar _ | CEvar _
  | CHole (Some _) | CGenarg _ | CGenargGlob _ ->
    CErrors.user_err ?loc
                      (str "This expression should be coercible to a pattern.")
  | CArray _ ->
    CErrors.user_err ?loc
                      (str "Arrays in patterns not supported.")) c

let isCSort a =
  match a.CAst.v with Constrexpr.CSort _ -> true | _ -> false
