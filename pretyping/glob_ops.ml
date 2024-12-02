(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open CAst
open Names
open Nameops
open Glob_term
open Evar_kinds

(* Untyped intermediate terms, after ASTs and before constr. *)

let cases_pattern_loc c = c.CAst.loc

let alias_of_pat pat = DAst.with_val (function
  | PatVar name -> name
  | PatCstr(_,_,name) -> name
  ) pat

let set_pat_alias id = DAst.map (function
  | PatVar Anonymous -> PatVar (Name id)
  | PatCstr (cstr,patl,Anonymous) -> PatCstr (cstr,patl,Name id)
  | pat -> assert false)

let cases_predicate_names tml =
  List.flatten (List.map (function
    | (tm,(na,None)) -> [na]
    | (tm,(na,Some {v=(_,nal)})) -> na::nal) tml)

let mkGApp ?loc p l = DAst.make ?loc @@
  match DAst.get p with
  | GApp (f,l') -> GApp (f,l'@l)
  | _          -> GApp (p,l)

let map_glob_decl_left_to_right f (na,r,k,obd,ty) =
  let comp1 = Option.map f obd in
  let comp2 = f ty in
  (na,r,k,comp1,comp2)

let glob_qvar_eq g1 g2 = match g1, g2 with
  | GLocalQVar na1, GLocalQVar na2 -> CAst.eq Name.equal na1 na2
  | GQVar q1, GQVar q2 -> Sorts.QVar.equal q1 q2
  | GRawQVar q1, GRawQVar q2 -> Sorts.QVar.equal q1 q2
  | (GLocalQVar _ | GQVar _ | GRawQVar _), _ -> false

let glob_quality_eq g1 g2 = match g1, g2 with
  | GQConstant q1, GQConstant q2 -> Sorts.Quality.Constants.equal q1 q2
  | GQualVar q1, GQualVar q2 -> glob_qvar_eq q1 q2
  | (GQConstant _ | GQualVar _), _ -> false

let glob_sort_name_eq g1 g2 = match g1, g2 with
  | GSProp, GSProp
  | GProp, GProp
  | GSet, GSet -> true
  | GUniv u1, GUniv u2 -> Univ.Level.equal u1 u2
  | GLocalUniv u1, GLocalUniv u2 -> lident_eq u1 u2
  | GRawUniv u1, GRawUniv u2 -> Univ.Level.equal u1 u2
  | (GSProp|GProp|GSet|GUniv _|GLocalUniv _|GRawUniv _), _ -> false

exception ComplexSort

let glob_Type_sort = None, UAnonymous {rigid=UnivRigid}
let glob_SProp_sort = None, UNamed [GSProp, 0]
let glob_Prop_sort = None, UNamed [GProp, 0]
let glob_Set_sort = None, UNamed [GSet, 0]

let map_glob_sort_gen f = function
  | UNamed l -> UNamed (f l)
  | UAnonymous _ as x -> x

let glob_sort_gen_eq f u1 u2 =
 match u1, u2 with
  | UAnonymous {rigid=r1}, UAnonymous {rigid=r2} -> r1 = r2
  | UNamed l1, UNamed l2 -> f l1 l2
  | (UNamed _ | UAnonymous _), _ -> false

let glob_sort_eq (q1, l1) (q2, l2) =
  Option.equal glob_qvar_eq q1 q2 &&
  glob_sort_gen_eq
    (List.equal (fun (x,m) (y,n) ->
         glob_sort_name_eq x y
         && Int.equal m n))
    l1 l2

let glob_sort_family s =
  let open Sorts in
  if glob_sort_eq s glob_Type_sort then InType
  else match s with
    | None, UNamed [s, 0] -> begin match s with
        | GSProp -> InSProp
        | GProp -> InProp
        | GSet -> InSet
        | GUniv _ | GLocalUniv _ | GRawUniv _ -> raise ComplexSort
      end
    | _ -> raise ComplexSort

let glob_univ_eq u1 u2 =
  let eq l1 l2 =
    List.equal (fun (x,m) (y,n) -> glob_sort_name_eq x y && Int.equal m n) l1 l2
  in
  glob_sort_gen_eq eq u1 u2

let instance_eq (q1,u1) (q2,u2) =
  List.equal glob_quality_eq q1 q2
  && List.equal glob_univ_eq u1 u2

let binding_kind_eq bk1 bk2 = match bk1, bk2 with
  | Explicit, Explicit -> true
  | NonMaxImplicit, NonMaxImplicit -> true
  | MaxImplicit, MaxImplicit -> true
  | (Explicit | NonMaxImplicit | MaxImplicit), _ -> false

let glob_relevance_eq a b = match a, b with
  | GRelevant, GRelevant | GIrrelevant, GIrrelevant -> true
  | GRelevanceVar q1, GRelevanceVar q2 -> glob_qvar_eq q1 q2
  | (GRelevant | GIrrelevant | GRelevanceVar _), _ -> false

let relevance_info_eq = Option.equal glob_relevance_eq

let case_style_eq s1 s2 = let open Constr in match s1, s2 with
  | LetStyle, LetStyle -> true
  | IfStyle, IfStyle -> true
  | LetPatternStyle, LetPatternStyle -> true
  | MatchStyle, MatchStyle -> true
  | RegularStyle, RegularStyle -> true
  | (LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle), _ -> false

let rec mk_cases_pattern_eq g p1 p2 = match DAst.get p1, DAst.get p2 with
  | PatVar na1, PatVar na2 -> g na1 na2
  | PatCstr (c1, pl1, na1), PatCstr (c2, pl2, na2) ->
    Construct.CanOrd.equal c1 c2 && List.equal (mk_cases_pattern_eq g) pl1 pl2 &&
      Name.equal na1 na2
  | (PatVar _ | PatCstr _), _ -> false

let cast_kind_eq t1 t2 = let open Constr in match t1, t2 with
  | DEFAULTcast, DEFAULTcast
  | VMcast, VMcast
  | NATIVEcast, NATIVEcast -> true
  | (DEFAULTcast | VMcast | NATIVEcast), _ -> false

let matching_var_kind_eq k1 k2 = match k1, k2 with
| FirstOrderPatVar ido1, FirstOrderPatVar ido2 -> Id.equal ido1 ido2
| SecondOrderPatVar id1, SecondOrderPatVar id2 -> Id.equal id1 id2
| (FirstOrderPatVar _ | SecondOrderPatVar _), _ -> false

let tomatch_tuple_eq f (c1, p1) (c2, p2) =
  let eqp {CAst.v=(i1, na1)} {CAst.v=(i2, na2)} =
    Ind.CanOrd.equal i1 i2 && List.equal Name.equal na1 na2
  in
  let eq_pred (n1, o1) (n2, o2) = Name.equal n1 n2 && Option.equal eqp o1 o2 in
  f c1 c2 && eq_pred p1 p2

and cases_clause_eq f g {CAst.v=(id1, p1, c1)} {CAst.v=(id2, p2, c2)} =
  (* In principle, id1 and id2 canonically derive from p1 and p2 *)
  List.equal (mk_cases_pattern_eq g) p1 p2 && f c1 c2

let glob_decl_eq f (na1, r1, bk1, c1, t1) (na2, r2, bk2, c2, t2) =
  Name.equal na1 na2 && relevance_info_eq r1 r2 && binding_kind_eq bk1 bk2 &&
  Option.equal f c1 c2 && f t1 t2

let fix_kind_eq k1 k2 = match k1, k2 with
  | GFix (a1, i1), GFix (a2, i2) ->
    Int.equal i1 i2 && Array.equal (Option.equal Int.equal) a1 a2
  | GCoFix i1, GCoFix i2 -> Int.equal i1 i2
  | (GFix _ | GCoFix _), _ -> false

let evar_instance_eq f (x1,c1) (x2,c2) =
  Id.equal x1.CAst.v x2.CAst.v && f c1 c2

let mk_glob_constr_eq f g c1 c2 = match DAst.get c1, DAst.get c2 with
  | GRef (gr1, u1), GRef (gr2, u2) ->
    GlobRef.CanOrd.equal gr1 gr2 &&
    Option.equal instance_eq u1 u2
  | GVar id1, GVar id2 -> Id.equal id1 id2
  | GEvar (id1, arg1), GEvar (id2, arg2) ->
    Id.equal id1.CAst.v id2.CAst.v && List.equal (evar_instance_eq f) arg1 arg2
  | GPatVar k1, GPatVar k2 -> matching_var_kind_eq k1 k2
  | GApp (f1, arg1), GApp (f2, arg2) ->
    f f1 f2 && List.equal f arg1 arg2
  | GLambda (na1, r1, bk1, t1, c1), GLambda (na2, r2, bk2, t2, c2) ->
    g na1 na2 (Some t1) (Some t2) && relevance_info_eq r1 r2
    && binding_kind_eq bk1 bk2 && f t1 t2 && f c1 c2
  | GProd (na1, r1, bk1, t1, c1), GProd (na2, r2, bk2, t2, c2) ->
    g na1 na2 (Some t1) (Some t2) && relevance_info_eq r1 r2
    && binding_kind_eq bk1 bk2 && f t1 t2 && f c1 c2
  | GLetIn (na1, r1, b1, t1, c1), GLetIn (na2, r2, b2, t2, c2) ->
    g na1 na2 t1 t2 && relevance_info_eq r1 r2
    && f b1 b2 && Option.equal f t1 t2 && f c1 c2
  | GCases (st1, c1, tp1, cl1), GCases (st2, c2, tp2, cl2) ->
    case_style_eq st1 st2 && Option.equal f c1 c2 &&
    List.equal (tomatch_tuple_eq f) tp1 tp2 &&
    List.equal (cases_clause_eq f (fun na1 na2 -> g na1 na2 None None)) cl1 cl2
  | GLetTuple (na1, (n1, p1), c1, t1), GLetTuple (na2, (n2, p2), c2, t2) ->
    List.equal (fun na1 na2 -> g na1 na2 None None) na1 na2 && g n1 n2 None None &&
    Option.equal f p1 p2 && f c1 c2 && f t1 t2
  | GIf (m1, (pat1, p1), c1, t1), GIf (m2, (pat2, p2), c2, t2) ->
    f m1 m2 && g pat1 pat2 None None &&
    Option.equal f p1 p2 && f c1 c2 && f t1 t2
  | GRec (kn1, id1, decl1, t1, c1), GRec (kn2, id2, decl2, t2, c2) ->
    fix_kind_eq kn1 kn2 && Array.equal Id.equal id1 id2 &&
    Array.equal (fun l1 l2 -> List.equal (glob_decl_eq f) l1 l2) decl1 decl2 &&
    Array.equal f c1 c2 && Array.equal f t1 t2
  | GSort s1, GSort s2 -> glob_sort_eq s1 s2
  | GHole (_kn1), GHole (_kn2) ->
    true (* this deserves a FIXME *)
  | GGenarg gn1, GGenarg gn2 ->
    gn1 == gn2 (* Only thing sensible *)
  | GCast (c1, k1, t1), GCast (c2, k2, t2) ->
    f c1 c2 && Option.equal cast_kind_eq k1 k2 && f t1 t2
  | GProj ((cst1, u1), args1, c1), GProj ((cst2, u2), args2, c2) ->
    GlobRef.(CanOrd.equal (ConstRef cst1) (ConstRef cst2)) &&
    Option.equal instance_eq u1 u2 &&
    List.equal f args1 args2 && f c1 c2
  | GInt i1, GInt i2 -> Uint63.equal i1 i2
  | GFloat f1, GFloat f2 -> Float64.equal f1 f2
  | GString s1, GString s2 -> Pstring.equal s1 s2
  | GArray (u1, t1, def1, ty1), GArray (u2, t2, def2, ty2) ->
    Array.equal f t1 t2 && f def1 def2 && f ty1 ty2 &&
    Option.equal instance_eq u1 u2
  | (GRef _ | GVar _ | GEvar _ | GPatVar _ | GApp _ | GLambda _ | GProd _ | GLetIn _ |
     GCases _ | GLetTuple _ | GIf _ | GRec _ | GSort _ | GHole _ | GGenarg _ | GCast _ | GProj _ |
     GInt _ | GFloat _ | GString _ | GArray _), _ -> false

let rec glob_constr_eq c = mk_glob_constr_eq glob_constr_eq (fun na1 na2 _ _ -> Name.equal na1 na2) c

let cases_pattern_eq c = mk_cases_pattern_eq Name.equal c

let rec map_case_pattern_binders f = DAst.map (function
  | PatVar na as x ->
      let r = f na in
      if r == na then x
      else PatVar r
  | PatCstr (c,ps,na) as x ->
      let rna = f na in
      let rps =
        CList.Smart.map (fun p -> map_case_pattern_binders f p) ps
      in
      if rna == na && rps == ps then x
      else PatCstr(c,rps,rna)
  )

let map_glob_constr_left_to_right_with_names f g = DAst.map (function
  | GApp (g,args) ->
      let comp1 = f g in
      let comp2 = Util.List.map_left f args in
      GApp (comp1,comp2)
  | GLambda (na,r,bk,ty,c) ->
      let comp1 = f ty in
      let comp2 = f c in
      GLambda (g na,r,bk,comp1,comp2)
  | GProd (na,r,bk,ty,c) ->
      let comp1 = f ty in
      let comp2 = f c in
      GProd (g na,r,bk,comp1,comp2)
  | GLetIn (na,r,b,t,c) ->
      let comp1 = f b in
      let compt = Option.map f t in
      let comp2 = f c in
      GLetIn (g na,r,comp1,compt,comp2)
  | GCases (sty,rtntypopt,tml,pl) ->
      let comp1 = Option.map f rtntypopt in
      let comp2 = Util.List.map_left (fun (tm,(x,indxl)) -> (f tm,(g x,Option.map (CAst.map (fun (ind,xl) -> (ind,List.map g xl))) indxl))) tml in
      let comp3 = Util.List.map_left (CAst.map (fun (idl,p,c) -> (List.map (fun id -> Name.get_id (g (Name id))) idl,List.map (map_case_pattern_binders g) p,f c))) pl in
      GCases (sty,comp1,comp2,comp3)
  | GLetTuple (nal,(na,po),b,c) ->
      let comp1 = Option.map f po in
      let comp2 = f b in
      let comp3 = f c in
      GLetTuple (List.map g nal,(g na,comp1),comp2,comp3)
  | GIf (c,(na,po),b1,b2) ->
      let comp1 = Option.map f po in
      let comp2 = f b1 in
      let comp3 = f b2 in
      GIf (f c,(g na,comp1),comp2,comp3)
  | GRec (fk,idl,bl,tyl,bv) ->
      let comp1 = Array.map (Util.List.map_left (map_glob_decl_left_to_right f)) bl in
      let comp2 = Array.map f tyl in
      let comp3 = Array.map f bv in
      let g id = Name.get_id (g (Name id)) in
      GRec (fk,Array.map g idl,comp1,comp2,comp3)
  | GCast (c,k,t) ->
      let c = f c in
      let t = f t in
      GCast (c,k,t)
  | GProj (p,args,c) ->
      let comp1 = Util.List.map_left f args in
      let comp2 = f c in
      GProj (p,comp1,comp2)
  | GArray (u,t,def,ty) ->
      let comp1 = Array.map_left f t in
      let comp2 = f def in
      let comp3 = f ty in
      GArray (u,comp1,comp2,comp3)
  | (GVar _ | GSort _ | GHole _ | GGenarg _ | GRef _ | GEvar _ | GPatVar _ | GInt _ | GFloat _ | GString _) as x -> x
  )

let map_glob_constr_left_to_right f = map_glob_constr_left_to_right_with_names f (fun na -> na)

let map_glob_constr = map_glob_constr_left_to_right

let fold_return_type f acc (na,tyopt) = Option.fold_left f acc tyopt

let fold_glob_constr f acc = DAst.with_val (function
  | GVar _ -> acc
  | GApp (c,args) -> List.fold_left f (f acc c) args
  | GLambda (_,_,_,b,c) | GProd (_,_,_,b,c) ->
    f (f acc b) c
  | GLetIn (_,_,b,t,c) ->
    f (Option.fold_left f (f acc b) t) c
  | GCases (_,rtntypopt,tml,pl) ->
    let fold_pattern acc {CAst.v=(idl,p,c)} = f acc c in
    List.fold_left fold_pattern
      (List.fold_left f (Option.fold_left f acc rtntypopt) (List.map fst tml))
      pl
  | GLetTuple (_,rtntyp,b,c) ->
    f (f (fold_return_type f acc rtntyp) b) c
  | GIf (c,rtntyp,b1,b2) ->
    f (f (f (fold_return_type f acc rtntyp) c) b1) b2
  | GRec (_,_,bl,tyl,bv) ->
    let acc = Array.fold_left
      (List.fold_left (fun acc (_,_,_,bbd,bty) ->
        f (Option.fold_left f acc bbd) bty)) acc bl in
    Array.fold_left f (Array.fold_left f acc tyl) bv
  | GCast (c,k,t) ->
    let acc = f acc t in
    f acc c
  | GProj (p,args,c) ->
    f (List.fold_left f acc args) c
  | GArray (_u,t,def,ty) -> f (f (Array.fold_left f acc t) def) ty
  | (GSort _ | GHole _ | GGenarg _ | GRef _ | GEvar _ | GPatVar _ | GInt _ | GFloat _ | GString _) -> acc
  )
let fold_return_type_with_binders f g v acc (na,tyopt) =
  (* eta expansion is important if g has effects, eg bound_glob_vars below, see #11959 *)
  Option.fold_left (fun acc -> f (Name.fold_right g na v) acc) acc tyopt

let fold_glob_constr_with_binders g f v acc = DAst.(with_val (function
  | GVar _ -> acc
  | GApp (c,args) -> List.fold_left (f v) (f v acc c) args
  | GLambda (na,_,_,b,c) | GProd (na,_,_,b,c) ->
    f (Name.fold_right g na v) (f v acc b) c
  | GLetIn (na,_,b,t,c) ->
    f (Name.fold_right g na v) (Option.fold_left (f v) (f v acc b) t) c
  | GCases (_,rtntypopt,tml,pl) ->
    let fold_pattern acc {v=(idl,p,c)} = f (List.fold_right g idl v) acc c in
    let fold_tomatch (v',acc) (tm,(na,onal)) =
      ((if rtntypopt = None then v' else
       Option.fold_left (fun v'' {v=(_,nal)} -> List.fold_right (Name.fold_right g) nal v'')
                        (Name.fold_right g na v') onal),
       f v acc tm) in
    let (v',acc) = List.fold_left fold_tomatch (v,acc) tml in
    let acc = Option.fold_left (f v') acc rtntypopt in
    List.fold_left fold_pattern acc pl
  | GLetTuple (nal,rtntyp,b,c) ->
    f (List.fold_right (Name.fold_right g) nal v)
      (f v (fold_return_type_with_binders f g v acc rtntyp) b) c
  | GIf (c,rtntyp,b1,b2) ->
    f v (f v (f v (fold_return_type_with_binders f g v acc rtntyp) c) b1) b2
  | GRec (_,idl,bll,tyl,bv) ->
    let v' = Array.fold_right g idl v in
    let f' i acc fid =
      let v,acc =
        List.fold_left
          (fun (v,acc) (na,_,_,bbd,bty) ->
            (Name.fold_right g na v, f v (Option.fold_left (f v) acc bbd) bty))
          (v,acc)
          bll.(i) in
      f v' (f v acc tyl.(i)) (bv.(i)) in
    Array.fold_left_i f' acc idl
  | GCast (c,k,t) ->
    let acc = f v acc t in
    f v acc c
  | GProj (p,args,c) ->
    f v (List.fold_left (f v) acc args) c
  | GArray (_u, t, def, ty) -> f v (f v (Array.fold_left (f v) acc t) def) ty
  | (GSort _ | GHole _ | GGenarg _ | GRef _ | GEvar _ | GPatVar _ | GInt _ | GFloat _ | GString _) -> acc))

let iter_glob_constr f = fold_glob_constr (fun () -> f) ()

let occur_glob_constr id =
  let rec occur barred acc c = match DAst.get c with
    | GVar id' -> Id.equal id id'
    | _ ->
       (* [g] looks if [id] appears in a binding position, in which
          case, we don't have to look in the corresponding subterm *)
       let g id' barred = barred || Id.equal id id' in
       let f barred acc c = acc || not barred && occur false acc c in
       fold_glob_constr_with_binders g f barred acc c in
  occur false false

let free_glob_vars =
  let rec vars bound vs c = match DAst.get c with
    | GVar id' -> if Id.Set.mem id' bound then vs else Id.Set.add id' vs
    | _ -> fold_glob_constr_with_binders Id.Set.add vars bound vs c in
  fun rt ->
    let vs = vars Id.Set.empty Id.Set.empty rt in
    vs

let glob_visible_short_qualid c =
  let rec aux acc c = match DAst.get c with
    | GRef (c,_) ->
        let qualid = Nametab.shortest_qualid_of_global Id.Set.empty c in
        let dir,id = Libnames.repr_qualid  qualid in
        if DirPath.is_empty dir then Id.Set.add id acc else acc
    | _ ->
        fold_glob_constr aux acc c
  in aux Id.Set.empty c

let warn_variable_collision =
  let open Pp in
  CWarnings.create ~name:"variable-collision" ~category:CWarnings.CoreCategories.ltac
         (fun name ->
          strbrk "Collision between bound variables of name " ++ Id.print name)

let add_and_check_ident id set =
  if Id.Set.mem id set then warn_variable_collision id;
  Id.Set.add id set

let bound_glob_vars =
  let rec vars bound =
    fold_glob_constr_with_binders
      (fun id () -> bound := add_and_check_ident id !bound)
      (fun () () -> vars bound)
      () ()
  in
  fun rt ->
    let bound = ref Id.Set.empty in
    vars bound rt;
    !bound

(** Mapping of names in binders *)

(* spiwack: I used a smart-style kind of mapping here, because the
   operation will be the identity almost all of the time (with any
   term outside of Ltac to begin with). But to be honest, there would
   probably be no significant penalty in doing reallocation as
   pattern-matching expressions are usually rather small. *)

let map_inpattern_binders f ({loc;v=(id,nal)} as x) =
  let r = CList.Smart.map f nal in
  if r == nal then x
  else CAst.make ?loc (id,r)

let map_tomatch_binders f ((c,(na,inp)) as x) : tomatch_tuple =
  let r = Option.Smart.map (fun p -> map_inpattern_binders f p) inp in
  if r == inp then x
  else c,(f na, r)

let map_cases_branch_binders f ({CAst.loc;v=(il,cll,rhs)} as x) : cases_clause =
  (* spiwack: not sure if I must do something with the list of idents.
     It is intended to be a superset of the free variable of the
     right-hand side, if I understand correctly. But I'm not sure when
     or how they are used. *)
  let r = List.Smart.map (fun cl -> map_case_pattern_binders f cl) cll in
  if r == cll then x
  else CAst.make ?loc (il,r,rhs)

let map_pattern_binders f tomatch branches =
  CList.Smart.map (fun tm -> map_tomatch_binders f tm) tomatch,
  CList.Smart.map (fun br -> map_cases_branch_binders f br) branches

(** /mapping of names in binders *)

let map_tomatch f (c,pp) : tomatch_tuple = f c , pp

let map_cases_branch f =
  CAst.map (fun (il,cll,rhs) -> (il , cll , f rhs))

let map_pattern f tomatch branches =
  List.map (fun tm -> map_tomatch f tm) tomatch,
  List.map (fun br -> map_cases_branch f br) branches

let loc_of_glob_constr c = c.CAst.loc

(**********************************************************************)
(* Alpha-renaming                                                     *)

exception UnsoundRenaming

let collide_id l id = List.exists (fun (id',id'') -> Id.equal id id' || Id.equal id id'') l
let test_id l id = if collide_id l id then raise UnsoundRenaming
let test_na l na = Name.iter (test_id l) na

let update_subst na l =
  let in_range id l = List.exists (fun (_,id') -> Id.equal id id') l in
  let l' = Name.fold_right Id.List.remove_assoc na l in
  Name.fold_right
    (fun id _ ->
     if in_range id l' then
       let id' = Namegen.next_ident_away_from id (fun id' -> in_range id' l') in
       Name id', (id,id')::l
     else na,l)
    na (na,l)

let rename_var l id =
  try
    let id' = Id.List.assoc id l in
    (* Check that no other earlier binding hides the one found *)
    let _,(id'',_) = List.extract_first (fun (_,id) -> Id.equal id id') l in
    if Id.equal id id'' then id' else raise UnsoundRenaming
  with Not_found ->
    if List.exists (fun (_,id') -> Id.equal id id') l then raise UnsoundRenaming
    else id

let force c = DAst.make ?loc:c.CAst.loc (DAst.get c)

let rec rename_glob_vars l c = force @@ DAst.map_with_loc (fun ?loc -> function
  | GVar id as r ->
      let id' = rename_var l id in
      if id == id' then r else GVar id'
  | GRef (GlobRef.VarRef id,_) as r ->
      if List.exists (fun (_,id') -> Id.equal id id') l then raise UnsoundRenaming
      else r
  | GProd (na,r,bk,t,c) ->
      let na',l' = update_subst na l in
      GProd (na',r,bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLambda (na,r,bk,t,c) ->
      let na',l' = update_subst na l in
      GLambda (na',r,bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLetIn (na,r,b,t,c) ->
      let na',l' = update_subst na l in
      GLetIn (na',r,rename_glob_vars l b,Option.map (rename_glob_vars l) t,rename_glob_vars l' c)
  (* Lazy strategy: we fail if a collision with renaming occurs, rather than renaming further *)
  | GCases (ci,po,tomatchl,cls) ->
      let test_pred_pat (na,ino) =
        test_na l na; Option.iter (fun {v=(_,nal)} -> List.iter (test_na l) nal) ino in
      let test_clause idl = List.iter (test_id l) idl in
      let po = Option.map (rename_glob_vars l) po in
      let tomatchl = Util.List.map_left (fun (tm,x) -> test_pred_pat x; (rename_glob_vars l tm,x)) tomatchl in
      let cls = Util.List.map_left (CAst.map (fun (idl,p,c) -> test_clause idl; (idl,p,rename_glob_vars l c))) cls in
      GCases (ci,po,tomatchl,cls)
  | GLetTuple (nal,(na,po),c,b) ->
     List.iter (test_na l) (na::nal);
     GLetTuple (nal,(na,Option.map (rename_glob_vars l) po),
                rename_glob_vars l c,rename_glob_vars l b)
  | GIf (c,(na,po),b1,b2) ->
     test_na l na;
     GIf (rename_glob_vars l c,(na,Option.map (rename_glob_vars l) po),
          rename_glob_vars l b1,rename_glob_vars l b2)
  | GRec (k,idl,decls,bs,ts) ->
     Array.iter (test_id l) idl;
     GRec (k,idl,
           Array.map (List.map (fun (na,r,k,bbd,bty) ->
               test_na l na;
               (na,r,k,Option.map (rename_glob_vars l) bbd,rename_glob_vars l bty))) decls,
           Array.map (rename_glob_vars l) bs,
           Array.map (rename_glob_vars l) ts)
  | _ -> DAst.get (map_glob_constr (rename_glob_vars l) c)
  ) c

(**********************************************************************)
(* Conversion from glob_constr to cases pattern, if possible            *)

let is_gvar id c = match DAst.get c with
| GVar id' -> Id.equal id id'
| _ -> false

let rec cases_pattern_of_glob_constr env na c =
  (* Forcing evaluation to ensure that the possible raising of
     Not_found is not delayed *)
  let c = DAst.force c in
  DAst.map (function
  | GVar id ->
    begin match na with
    | Name _ ->
      (* Unable to manage the presence of both an alias and a variable *)
      raise Not_found
    | Anonymous -> PatVar (Name id)
    end
  | GHole _ -> PatVar na
  | GGenarg _ -> PatVar na (* XXX does this really make sense? *)
  | GRef (GlobRef.VarRef id,_) -> PatVar (Name id)
  | GRef (GlobRef.ConstructRef cstr,_) -> PatCstr (cstr,[],na)
  | GApp (c, l) ->
    begin match DAst.get c with
    | GRef (GlobRef.ConstructRef cstr,_) ->
      let nparams = Inductiveops.inductive_nparams env (fst cstr) in
      let _,l = List.chop nparams l in
      PatCstr (cstr,List.map (cases_pattern_of_glob_constr env Anonymous) l,na)
    | _ -> raise Not_found
    end
  | GLetIn (Name id as na',_,b,None,e) when is_gvar id e && na = Anonymous ->
     (* A canonical encoding of aliases *)
     DAst.get (cases_pattern_of_glob_constr env na' b)
  | _ -> raise Not_found
  ) c

open Declarations
open Context

(* Keep only patterns which are not bound to a local definitions *)
let drop_local_defs params decls args =
    let decls = List.skipn (Rel.length params) (List.rev decls) in
    let rec aux decls args =
      match decls, args with
      | [], [] -> []
      | Rel.Declaration.LocalDef _ :: decls, pat :: args ->
         begin
           match DAst.get pat with
           | PatVar Anonymous -> aux decls args
           | _ -> raise Not_found (* The pattern is used, one cannot drop it *)
         end
      | Rel.Declaration.LocalAssum _ :: decls, a :: args -> a :: aux decls args
      | _ -> assert false in
    aux decls args

let add_patterns_for_params_remove_local_defs env (ind,j) l =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let nparams = mib.Declarations.mind_nparams in
  let l =
    if mip.mind_consnrealdecls.(j-1) = mip.mind_consnrealargs.(j-1) then
      (* Optimisation *) l
    else
      let (ctx, _) = mip.mind_nf_lc.(j - 1) in
      drop_local_defs mib.mind_params_ctxt ctx l in
  Util.List.addn nparams (DAst.make @@ PatVar Anonymous) l

let add_alias ?loc na c =
  match na with
  | Anonymous -> c
  | Name id -> GLetIn (na,None,DAst.make ?loc c,None,DAst.make ?loc (GVar id))

(* Turn a closed cases pattern into a glob_constr *)
let rec glob_constr_of_cases_pattern_aux env isclosed x = DAst.map_with_loc (fun ?loc -> function
  | PatCstr (cstr,[],na) -> add_alias ?loc na (GRef (GlobRef.ConstructRef cstr,None))
  | PatCstr (cstr,l,na)  ->
      let ref = DAst.make ?loc @@ GRef (GlobRef.ConstructRef cstr,None) in
      let l = add_patterns_for_params_remove_local_defs env cstr l in
      add_alias ?loc na (GApp (ref, List.map (glob_constr_of_cases_pattern_aux env isclosed) l))
  | PatVar (Name id) when not isclosed ->
      GVar id
  | PatVar Anonymous when not isclosed ->
      GHole (GQuestionMark {
        Evar_kinds.default_question_mark with Evar_kinds.qm_obligation=Define false;
      })
  | _ -> raise Not_found
  ) x

let glob_constr_of_closed_cases_pattern env p = match DAst.get p with
  | PatCstr (cstr,l,na) ->
      let loc = p.CAst.loc in
      na,glob_constr_of_cases_pattern_aux env true (DAst.make ?loc @@ PatCstr (cstr,l,Anonymous))
  | _ ->
      raise Not_found

let glob_constr_of_cases_pattern env p = glob_constr_of_cases_pattern_aux env false p

let kind_of_glob_kind = function
| GImplicitArg (gr, p, b) -> ImplicitArg (gr, p, b)
| GBinderType na -> BinderType na
| GNamedHole (fresh, id) -> NamedHole id
| GQuestionMark qm -> QuestionMark qm
| GCasesType -> CasesType false
| GInternalHole -> InternalHole
| GImpossibleCase -> ImpossibleCase

let naming_of_glob_kind = function
| GNamedHole (true, id) -> Namegen.IntroFresh id
| GNamedHole (false, id) -> Namegen.IntroIdentifier id
| _ -> Namegen.IntroAnonymous

(* This has to be in some file... *)

open Ltac_pretype

let empty_lvar : ltac_var_map = {
  ltac_constrs = Id.Map.empty;
  ltac_uconstrs = Id.Map.empty;
  ltac_idents = Id.Map.empty;
  ltac_genargs = Id.Map.empty;
}
