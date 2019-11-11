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
open Names
open Nameops
open Libnames
open Namegen
open Glob_term
open Notation
open Constrexpr

(***********)
(* Universes *)

let sort_name_expr_eq c1 c2 = match c1, c2 with
  | CSProp, CSProp
  | CProp, CProp
  | CSet, CSet -> true
  | CType q1, CType q2 -> Libnames.qualid_eq q1 q2
  | CRawType u1, CRawType u2 -> Univ.Level.equal u1 u2
  | (CSProp|CProp|CSet|CType _|CRawType _), _ -> false

let univ_level_expr_eq u1 u2 =
  Glob_ops.glob_sort_gen_eq sort_name_expr_eq u1 u2

let sort_expr_eq u1 u2 =
  Glob_ops.glob_sort_gen_eq
    (List.equal (fun (x,m) (y,n) -> sort_name_expr_eq x y && Int.equal m n))
    u1 u2

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
  List.flatten (List.map (function CLocalAssum(l,_,_)->l|_->[]) bl)

let names_of_local_binders bl =
  List.flatten (List.map (function CLocalAssum(l,_,_)->l|CLocalDef(l,_,_)->[l]|CLocalPattern _ -> assert false) bl)

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
    cases_pattern_notation_substitution_eq s1 s2 &&
    List.equal cases_pattern_expr_eq l1 l2
  | CPatPrim i1, CPatPrim i2 ->
    prim_token_eq i1 i2
  | CPatRecord l1, CPatRecord l2 ->
    let equal (r1, e1) (r2, e2) =
      qualid_eq r1 r2 && cases_pattern_expr_eq e1 e2
    in
    List.equal equal l1 l2
  | CPatDelimiters(s1,e1), CPatDelimiters(s2,e2) ->
    String.equal s1 s2 && cases_pattern_expr_eq e1 e2
  | _ -> false

and cases_pattern_notation_substitution_eq (s1, n1) (s2, n2) =
  List.equal cases_pattern_expr_eq s1 s2 &&
  List.equal (List.equal cases_pattern_expr_eq) n1 n2

let kinded_cases_pattern_expr_eq (p1,bk1) (p2,bk2) =
  cases_pattern_expr_eq p1 p2 && Glob_ops.binding_kind_eq bk1 bk2

let eq_universes u1 u2 =
  match u1, u2 with
  | None, None -> true
  | Some l, Some l' -> l = l'
  | _, _ -> false

(* We use a functor to avoid passing the recursion all over the place *)
module EqGen (A:sig val constr_expr_eq : constr_expr -> constr_expr -> bool end) = struct

  open A
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

  let local_binder_eq l1 l2 = match l1, l2 with
    | CLocalDef (n1, e1, t1), CLocalDef (n2, e2, t2) ->
      CAst.eq Name.equal n1 n2 && constr_expr_eq e1 e2 && Option.equal constr_expr_eq t1 t2
    | CLocalAssum (n1, _, e1), CLocalAssum (n2, _, e2) ->
      (* Don't care about the [binder_kind] *)
      List.equal (CAst.eq Name.equal) n1 n2 && constr_expr_eq e1 e2
    | _ -> false

  let fix_expr_eq (id1,r1,bl1,a1,b1) (id2,r2,bl2,a2,b2) =
    (lident_eq id1 id2) &&
    Option.equal recursion_order_expr_eq r1 r2 &&
    List.equal local_binder_eq bl1 bl2 &&
    constr_expr_eq a1 a2 &&
    constr_expr_eq b1 b2

  let cofix_expr_eq (id1,bl1,a1,b1) (id2,bl2,a2,b2) =
    (lident_eq id1 id2) &&
    List.equal local_binder_eq bl1 bl2 &&
    constr_expr_eq a1 a2 &&
    constr_expr_eq b1 b2

  let constr_notation_substitution_eq (e1, el1, b1, bl1) (e2, el2, b2, bl2) =
    List.equal constr_expr_eq e1 e2 &&
    List.equal (List.equal constr_expr_eq) el1 el2 &&
    List.equal kinded_cases_pattern_expr_eq b1 b2 &&
    List.equal (List.equal local_binder_eq) bl1 bl2

  let instance_eq (x1,c1) (x2,c2) =
    Id.equal x1.CAst.v x2.CAst.v && constr_expr_eq c1 c2

  let constr_expr_eq e1 e2 =
    if CAst.(e1.v == e2.v) then true
    else match CAst.(e1.v, e2.v) with
      | CRef (r1,u1), CRef (r2,u2) -> qualid_eq r1 r2 && eq_universes u1 u2
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
        eq_universes u1 u2 &&
        List.equal constr_expr_eq al1 al2
      | CApp(e1,al1), CApp(e2,al2) ->
        constr_expr_eq e1 e2 &&
        List.equal args_eq al1 al2
      | CProj(e1,(p1,u1),al1,c1), CProj(e2,(p2,u2),al2,c2) ->
        e1 = (e2:bool) &&
        qualid_eq p1 p2 &&
        eq_universes u1 u2 &&
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
      | CPatVar i1, CPatVar i2 ->
        Id.equal i1 i2
      | CEvar (id1, c1), CEvar (id2, c2) ->
        Id.equal id1.CAst.v id2.CAst.v && List.equal instance_eq c1 c2
      | CSort s1, CSort s2 ->
        sort_expr_eq s1 s2
      | CCast(c1,k1,t1), CCast(c2,k2,t2) ->
        constr_expr_eq c1 c2 && Glob_ops.cast_kind_eq k1 k2 && constr_expr_eq t1 t2
      | CNotation(inscope1, n1, s1), CNotation(inscope2, n2, s2) ->
        Option.equal notation_with_optional_scope_eq inscope1 inscope2 &&
        notation_eq n1 n2 &&
        constr_notation_substitution_eq s1 s2
      | CPrim i1, CPrim i2 ->
        prim_token_eq i1 i2
      | CGeneralization (bk1, e1), CGeneralization (bk2, e2) ->
        Glob_ops.binding_kind_eq bk1 bk2 &&
        constr_expr_eq e1 e2
      | CDelimiters(s1,e1), CDelimiters(s2,e2) ->
        String.equal s1 s2 &&
        constr_expr_eq e1 e2
      | CArray(u1,t1,def1,ty1), CArray(u2,t2,def2,ty2) ->
        Array.equal constr_expr_eq t1 t2 &&
        constr_expr_eq def1 def2 && constr_expr_eq ty1 ty2 &&
        eq_universes u1 u2
      | (CRef _ | CFix _ | CCoFix _ | CProdN _ | CLambdaN _ | CLetIn _ | CAppExpl _
        | CApp _ | CProj _ | CRecord _ | CCases _ | CLetTuple _ | CIf _ | CHole _
        | CPatVar _ | CEvar _ | CSort _ | CCast _ | CNotation _ | CPrim _
        | CGeneralization _ | CDelimiters _ | CArray _), _ -> false

end

let constr_expr_eq_gen eq =
  let module Eq = EqGen(struct let constr_expr_eq = eq end) in
  Eq.constr_expr_eq

module Eq = EqGen(struct
    let rec constr_expr_eq c1 c2 = constr_expr_eq_gen constr_expr_eq c1 c2
  end)
include Eq

let constr_loc c = CAst.(c.loc)
let cases_pattern_expr_loc cp = CAst.(cp.loc)

let local_binder_loc = let open CAst in function
  | CLocalAssum ({ loc } ::_,_,t)
  | CLocalDef ( { loc },t,None) -> Loc.merge_opt loc (constr_loc t)
  | CLocalDef ( { loc },b,Some t) -> Loc.merge_opt loc (Loc.merge_opt (constr_loc b) (constr_loc t))
  | CLocalAssum ([],_,_) -> assert false
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

let rec cases_pattern_fold_names f h nacc pt = match CAst.(pt.v) with
  | CPatRecord l ->
    List.fold_left (fun nacc (r, cp) -> cases_pattern_fold_names f h nacc cp) nacc l
  | CPatAlias (pat,{CAst.v=na}) -> Name.fold_right (fun na (n,acc) -> (f na n,acc)) na (cases_pattern_fold_names f h nacc pat)
  | CPatOr (patl) ->
    List.fold_left (cases_pattern_fold_names f h) nacc patl
  | CPatCstr (_,patl1,patl2) ->
    List.fold_left (cases_pattern_fold_names f h)
      (Option.fold_left (List.fold_left (cases_pattern_fold_names f h)) nacc patl1) patl2
  | CPatNotation (_,_,(patl,patll),patl') ->
    List.fold_left (cases_pattern_fold_names f h)
      (List.fold_left (cases_pattern_fold_names f h) nacc (patl@List.flatten patll)) patl'
  | CPatDelimiters (_,pat) -> cases_pattern_fold_names f h nacc pat
  | CPatAtom (Some qid)
      when qualid_is_ident qid && not (is_constructor @@ qualid_basename qid) ->
      let (n, acc) = nacc in
      (f (qualid_basename qid) n, acc)
  | CPatPrim _ | CPatAtom _ -> nacc
  | CPatCast (p,t) ->
      let (n, acc) = nacc in
      cases_pattern_fold_names f h (n, h acc t) p

let ids_of_pattern_list p =
  fst (List.fold_left
    (List.fold_left (cases_pattern_fold_names Id.Set.add (fun () _ -> ())))
    (Id.Set.empty,()) p)

let ids_of_cases_tomatch tms =
  List.fold_right
    (fun (_, ona, indnal) l ->
       Option.fold_right (fun t ids -> fst (cases_pattern_fold_names Id.Set.add (fun () _ -> ()) (ids,()) t))
         indnal
         (Option.fold_right (CAst.with_val (Name.fold_right Id.Set.add)) ona l))
    tms Id.Set.empty

let rec fold_local_binders g f n acc b = let open CAst in function
  | CLocalAssum (nal,bk,t)::l ->
    let nal = List.(map (fun {v} -> v) nal) in
    let n' = List.fold_right (Name.fold_right g) nal n in
    f n (fold_local_binders g f n' acc b l) t
  | CLocalDef ( { v = na },c,t)::l ->
    Option.fold_left (f n) (f n (fold_local_binders g f (Name.fold_right g na n) acc b l) c) t
  | CLocalPattern pat :: l ->
    let n, acc = cases_pattern_fold_names g (f n) (n,acc) pat in
    fold_local_binders g f n acc b l
  | [] ->
    f n acc b

let fold_constr_expr_with_binders g f n acc = CAst.with_val (function
    | CAppExpl ((_,_),l) -> List.fold_left (f n) acc l
    | CApp (t,l) -> List.fold_left (f n) (f n acc t) (List.map fst l)
    | CProj (e,_,l,t) -> f n (List.fold_left (f n) acc (List.map fst l)) t
    | CProdN (l,b) | CLambdaN (l,b) -> fold_local_binders g f n acc b l
    | CLetIn (na,a,t,b) ->
      f (Name.fold_right g (na.CAst.v) n) (Option.fold_left (f n) (f n acc a) t) b
    | CCast (a,_,b) -> f n (f n acc a) b
    | CNotation (_,_,(l,ll,bl,bll)) ->
      (* The following is an approximation: we don't know exactly if
         an ident is binding nor to which subterms bindings apply *)
      let acc = List.fold_left (f n) acc (l@List.flatten ll) in
      List.fold_left (fun acc bl -> fold_local_binders g f n acc (CAst.make @@ CHole (None,IntroAnonymous,None)) bl) acc bll
    | CGeneralization (_,c) -> f n acc c
    | CDelimiters (_,a) -> f n acc a
    | CHole _ | CEvar _ | CPatVar _ | CSort _ | CPrim _ | CRef _ ->
      acc
    | CRecord l -> List.fold_left (fun acc (id, c) -> f n acc c) acc l
    | CCases (sty,rtnpo,al,bl) ->
      let ids = ids_of_cases_tomatch al in
      let acc = Option.fold_left (f (Id.Set.fold g ids n)) acc rtnpo in
      let acc = List.fold_left (f n) acc (List.map (fun (fst,_,_) -> fst) al) in
      List.fold_right (fun {CAst.v=(patl,rhs)} acc ->
          let ids = ids_of_pattern_list patl in
          f (Id.Set.fold g ids n) acc rhs) bl acc
    | CLetTuple (nal,(ona,po),b,c) ->
      let n' = List.fold_right (CAst.with_val (Name.fold_right g)) nal n in
      f (Option.fold_right (CAst.with_val (Name.fold_right g)) ona n') (f n acc b) c
    | CIf (c,(ona,po),b1,b2) ->
      let acc = f n (f n (f n acc b1) b2) c in
      Option.fold_left
        (f (Option.fold_right (CAst.with_val (Name.fold_right g)) ona n)) acc po
    | CFix (_,l) ->
      let n' = List.fold_right (fun ( { CAst.v = id },_,_,_,_) -> g id) l n in
      List.fold_right (fun (_,ro,lb,t,c) acc ->
          fold_local_binders g f n'
            (fold_local_binders g f n acc t lb) c lb) l acc
    | CCoFix (_,_) ->
      Feedback.msg_warning (strbrk "Capture check in multiple binders not done"); acc
    | CArray (_u,t,def,ty) -> f n (f n (Array.fold_left (f n) acc t) def) ty
  )

let free_vars_of_constr_expr c =
  let rec aux bdvars l = function
    | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
      let id = qualid_basename qid in
      if Id.List.mem id bdvars then l else Id.Set.add id l
    | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] Id.Set.empty c

let names_of_constr_expr c =
  let vars = ref Id.Set.empty in
  let rec aux () () = function
    | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
      let id = qualid_basename qid in vars := Id.Set.add id !vars
    | c -> fold_constr_expr_with_binders (fun a () -> vars := Id.Set.add a !vars) aux () () c
  in aux () () c; !vars

let occur_var_constr_expr id c = Id.Set.mem id (free_vars_of_constr_expr c)

let rec fold_map_cases_pattern f h acc (CAst.{v=pt;loc} as p) = match pt with
  | CPatRecord l ->
    let acc, l = List.fold_left_map (fun acc (r, cp) -> let acc, cp = fold_map_cases_pattern f h acc cp in acc, (r, cp)) acc l in
    acc, CAst.make ?loc (CPatRecord l)
  | CPatAlias (pat,({CAst.v=na} as lna)) ->
    let acc, p = fold_map_cases_pattern f h acc pat in
    let acc = Name.fold_right f na acc in
    acc, CAst.make ?loc (CPatAlias (pat,lna))
  | CPatOr patl ->
    let acc, patl = List.fold_left_map (fold_map_cases_pattern f h) acc patl in
    acc, CAst.make ?loc (CPatOr patl)
  | CPatCstr (c,patl1,patl2) ->
    let acc, patl1 = Option.fold_left_map (List.fold_left_map (fold_map_cases_pattern f h)) acc patl1 in
    let acc, patl2 = List.fold_left_map (fold_map_cases_pattern f h) acc patl2 in
    acc, CAst.make ?loc (CPatCstr (c,patl1,patl2))
  | CPatNotation (sc,ntn,(patl,patll),patl') ->
    let acc, patl = List.fold_left_map (fold_map_cases_pattern f h) acc patl in
    let acc, patll = List.fold_left_map (List.fold_left_map (fold_map_cases_pattern f h)) acc patll in
    let acc, patl' = List.fold_left_map (fold_map_cases_pattern f h) acc patl' in
    acc, CAst.make ?loc (CPatNotation (sc,ntn,(patl,patll),patl'))
  | CPatDelimiters (d,pat) ->
    let acc, p = fold_map_cases_pattern f h acc pat in
    acc, CAst.make ?loc (CPatDelimiters (d,pat))
  | CPatAtom (Some qid)
      when qualid_is_ident qid && not (is_constructor @@ qualid_basename qid) ->
    f (qualid_basename qid) acc, p
  | CPatPrim _ | CPatAtom _ -> (acc,p)
  | CPatCast (pat,t) ->
    let acc, pat = fold_map_cases_pattern f h acc pat in
    let t = h acc t in
    acc, CAst.make ?loc (CPatCast (pat,t))

(* Used in correctness and interface *)
let map_binder g e nal = List.fold_right (CAst.with_val (Name.fold_right g)) nal e

let fold_map_local_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let open CAst in
  let h (e,bl) = function
      CLocalAssum(nal,k,ty) ->
      (map_binder g e nal, CLocalAssum(nal,k,f e ty)::bl)
    | CLocalDef( { loc ; v = na } as cna ,c,ty) ->
      (Name.fold_right g na e, CLocalDef(cna,f e c,Option.map (f e) ty)::bl)
    | CLocalPattern pat ->
      let e, pat = fold_map_cases_pattern g f e pat in
      (e, CLocalPattern pat::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_constr_expr_with_binders g f e = CAst.map (function
    | CAppExpl (r,l) -> CAppExpl (r,List.map (f e) l)
    | CApp (a,l) ->
      CApp (f e a,List.map (fun (a,i) -> (f e a,i)) l)
    | CProj (expl,p,l,a) ->
      CProj (expl,p,List.map (fun (a,i) -> (f e a,i)) l,f e a)
    | CProdN (bl,b) ->
      let (e,bl) = fold_map_local_binders f g e bl in CProdN (bl,f e b)
    | CLambdaN (bl,b) ->
      let (e,bl) = fold_map_local_binders f g e bl in CLambdaN (bl,f e b)
    | CLetIn (na,a,t,b) ->
      CLetIn (na,f e a,Option.map (f e) t,f (Name.fold_right g (na.CAst.v) e) b)
    | CCast (a,k,c) -> CCast (f e a, k, f e c)
    | CNotation (inscope,n,(l,ll,bl,bll)) ->
      (* This is an approximation because we don't know what binds what *)
      CNotation (inscope,n,(List.map (f e) l,List.map (List.map (f e)) ll, bl,
                    List.map (fun bl -> snd (fold_map_local_binders f g e bl)) bll))
    | CGeneralization (b,c) -> CGeneralization (b,f e c)
    | CDelimiters (s,a) -> CDelimiters (s,f e a)
    | CHole _ | CEvar _ | CPatVar _ | CSort _
    | CPrim _ | CRef _ as x -> x
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
      CFix (id,List.map (fun (id,n,bl,t,d) ->
          let (e',bl') = fold_map_local_binders f g e bl in
          let t' = f e' t in
          (* Note: fix names should be inserted before the arguments... *)
          let e'' = List.fold_left (fun e ({ CAst.v = id },_,_,_,_) -> g id e) e' dl in
          let d' = f e'' d in
          (id,n,bl',t',d')) dl)
    | CCoFix (id,dl) ->
      CCoFix (id,List.map (fun (id,bl,t,d) ->
          let (e',bl') = fold_map_local_binders f g e bl in
          let t' = f e' t in
          let e'' = List.fold_left (fun e ({ CAst.v = id },_,_,_) -> g id e) e' dl in
          let d' = f e'' d in
          (id,bl',t',d')) dl)
    | CArray (u, t, def, ty) ->
      CArray (u, Array.map (f e) t, f e def, f e ty)
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

let ntn_loc ?loc (args,argslist,binders,binderslist) =
  locs_of_notation ?loc
    (List.map constr_loc (args@List.flatten argslist)@
     List.map (fun (x,_) -> cases_pattern_expr_loc x) binders@
     List.map local_binders_loc binderslist)

let patntn_loc ?loc (args,argslist) =
  locs_of_notation ?loc
    (List.map cases_pattern_expr_loc (args@List.flatten argslist))

let error_invalid_pattern_notation ?loc () =
  CErrors.user_err ?loc  (str "Invalid notation for pattern.")

(* Interpret the index of a recursion order annotation *)
let split_at_annot bl na =
  let open CAst in
  let names = List.map (fun { v } -> v) (names_of_local_assums bl) in
  match na with
  | None ->
    begin match names with
      | [] -> CErrors.user_err (Pp.str "A fixpoint needs at least one parameter.")
      | _ -> ([], bl)
    end
  | Some { loc; v = id } ->
    let rec aux acc = function
      | CLocalAssum (bls, k, t) as x :: rest ->
        let test { CAst.v = na } = match na with
          | Name id' -> Id.equal id id'
          | Anonymous -> false
        in
        let l, r = List.split_when test bls in
        begin match r with
          | [] -> aux (x :: acc) rest
          | _ ->
            let ans = match l with
              | [] -> acc
              | _ -> CLocalAssum (l, k, t) :: acc
            in
            (List.rev ans, CLocalAssum (r, k, t) :: rest)
        end
      | CLocalDef ({ CAst.v = na },_,_) as x :: rest ->
        if Name.equal (Name id) na then
          CErrors.user_err ?loc
            (Id.print id ++ str" must be a proper parameter and not a local definition.")
        else
          aux (x :: acc) rest
      | CLocalPattern _ :: rest ->
        Loc.raise ?loc (Stream.Error "pattern with quote not allowed after fix")
      | [] ->
        CErrors.user_err ?loc
          (str "No parameter named " ++ Id.print id ++ str".")
    in aux [] bl

(** Pseudo-constructors *)

let mkIdentC id   = CAst.make @@ CRef (qualid_of_ident id,None)
let mkRefC r      = CAst.make @@ CRef (r,None)
let mkCastC (a,k,t) = CAst.make @@ CCast (a,k,t)
let mkLambdaC (idl,bk,a,b) = CAst.make @@ CLambdaN ([CLocalAssum (idl,bk,a)],b)
let mkLetInC  (id,a,t,b)   = CAst.make @@ CLetIn (id,a,t,b)
let mkProdC   (idl,bk,a,b) = CAst.make @@ CProdN ([CLocalAssum (idl,bk,a)],b)

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
  | { CAst.loc; v = CHole (None,IntroAnonymous,None) } -> CAst.make ?loc Anonymous
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

let rec coerce_to_cases_pattern_expr c = CAst.map_with_loc (fun ?loc -> function
  | CRef (r,None) ->
     CPatAtom (Some r)
  | CHole (None,IntroAnonymous,None) ->
     CPatAtom None
  | CLetIn ({CAst.loc;v=Name id},b,None,{ CAst.v = CRef (qid,None) })
      when qualid_is_ident qid && Id.equal id (qualid_basename qid) ->
      CPatAlias (coerce_to_cases_pattern_expr b, CAst.(make ?loc @@ Name id))
  | CApp (p,args) when List.for_all (fun (_,e) -> e=None) args ->
     (mkAppPattern (coerce_to_cases_pattern_expr p) (List.map (fun (a,_) -> coerce_to_cases_pattern_expr a) args)).CAst.v
  | CAppExpl ((r,i),args) ->
     CPatCstr (r,Some (List.map coerce_to_cases_pattern_expr args),[])
  | CNotation (inscope,ntn,(c,cl,[],[])) ->
     CPatNotation (inscope,ntn,(List.map coerce_to_cases_pattern_expr c,
                        List.map (List.map coerce_to_cases_pattern_expr) cl),[])
  | CPrim p ->
     CPatPrim p
  | CRecord l ->
     CPatRecord (List.map (fun (r,p) -> (r,coerce_to_cases_pattern_expr p)) l)
  | CDelimiters (s,p) ->
     CPatDelimiters (s,coerce_to_cases_pattern_expr p)
  | CCast (p,Constr.DEFAULTcast, t) ->
     CPatCast (coerce_to_cases_pattern_expr p,t)
  | _ ->
     CErrors.user_err ?loc
                      (str "This expression should be coercible to a pattern.")) c
