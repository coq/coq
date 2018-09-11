(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open CAst
open Names
open Nameops
open Globnames
open Glob_term
open Evar_kinds
open Ltac_pretype

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

let mkGApp ?loc p t = DAst.make ?loc @@
  match DAst.get p with
  | GApp (f,l) -> GApp (f,l@[t])
  | _          -> GApp (p,[t])

let map_glob_decl_left_to_right f (na,k,obd,ty) =
  let comp1 = Option.map f obd in
  let comp2 = f ty in
  (na,k,comp1,comp2)


let glob_sort_eq g1 g2 = let open Glob_term in match g1, g2 with
| GProp, GProp -> true
| GSet, GSet -> true
| GType l1, GType l2 ->
   List.equal (Option.equal (fun (x,m) (y,n) -> Libnames.qualid_eq x y && Int.equal m n)) l1 l2
| _ -> false

let binding_kind_eq bk1 bk2 = match bk1, bk2 with
  | Decl_kinds.Explicit, Decl_kinds.Explicit -> true
  | Decl_kinds.Implicit, Decl_kinds.Implicit -> true
  | (Decl_kinds.Explicit | Decl_kinds.Implicit), _ -> false

let case_style_eq s1 s2 = let open Constr in match s1, s2 with
  | LetStyle, LetStyle -> true
  | IfStyle, IfStyle -> true
  | LetPatternStyle, LetPatternStyle -> true
  | MatchStyle, MatchStyle -> true
  | RegularStyle, RegularStyle -> true
  | (LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle), _ -> false

let rec cases_pattern_eq p1 p2 = match DAst.get p1, DAst.get p2 with
  | PatVar na1, PatVar na2 -> Name.equal na1 na2
  | PatCstr (c1, pl1, na1), PatCstr (c2, pl2, na2) ->
    eq_constructor c1 c2 && List.equal cases_pattern_eq pl1 pl2 &&
      Name.equal na1 na2
  | (PatVar _ | PatCstr _), _ -> false

let cast_type_eq eq t1 t2 = match t1, t2 with
  | CastConv t1, CastConv t2 -> eq t1 t2
  | CastVM t1, CastVM t2 -> eq t1 t2
  | CastCoerce, CastCoerce -> true
  | CastNative t1, CastNative t2 -> eq t1 t2
  | (CastConv _ | CastVM _ | CastCoerce | CastNative _), _ -> false

let matching_var_kind_eq k1 k2 = match k1, k2 with
| FirstOrderPatVar ido1, FirstOrderPatVar ido2 -> Id.equal ido1 ido2
| SecondOrderPatVar id1, SecondOrderPatVar id2 -> Id.equal id1 id2
| (FirstOrderPatVar _ | SecondOrderPatVar _), _ -> false

let tomatch_tuple_eq f (c1, p1) (c2, p2) =
  let eqp {CAst.v=(i1, na1)} {CAst.v=(i2, na2)} =
    eq_ind i1 i2 && List.equal Name.equal na1 na2
  in
  let eq_pred (n1, o1) (n2, o2) = Name.equal n1 n2 && Option.equal eqp o1 o2 in
  f c1 c2 && eq_pred p1 p2

and cases_clause_eq f {CAst.v=(id1, p1, c1)} {CAst.v=(id2, p2, c2)} =
  List.equal Id.equal id1 id2 && List.equal cases_pattern_eq p1 p2 && f c1 c2

let glob_decl_eq f (na1, bk1, c1, t1) (na2, bk2, c2, t2) =
  Name.equal na1 na2 && binding_kind_eq bk1 bk2 &&
  Option.equal f c1 c2 && f t1 t2

let fix_recursion_order_eq f o1 o2 = match o1, o2 with
  | GStructRec, GStructRec -> true
  | GWfRec c1, GWfRec c2 -> f c1 c2
  | GMeasureRec (c1, o1), GMeasureRec (c2, o2) ->
    f c1 c2 && Option.equal f o1 o2
  | (GStructRec | GWfRec _ | GMeasureRec _), _ -> false

let fix_kind_eq f k1 k2 = match k1, k2 with
  | GFix (a1, i1), GFix (a2, i2) ->
    let eq (i1, o1) (i2, o2) =
      Option.equal Int.equal i1 i2 && fix_recursion_order_eq f o1 o2
    in
    Int.equal i1 i2 && Array.equal eq a1 a2
  | GCoFix i1, GCoFix i2 -> Int.equal i1 i2
  | (GFix _ | GCoFix _), _ -> false

let instance_eq f (x1,c1) (x2,c2) =
  Id.equal x1 x2 && f c1 c2

let mk_glob_constr_eq f c1 c2 = match DAst.get c1, DAst.get c2 with
  | GRef (gr1, _), GRef (gr2, _) -> GlobRef.equal gr1 gr2
  | GVar id1, GVar id2 -> Id.equal id1 id2
  | GEvar (id1, arg1), GEvar (id2, arg2) ->
    Id.equal id1 id2 && List.equal (instance_eq f) arg1 arg2
  | GPatVar k1, GPatVar k2 -> matching_var_kind_eq k1 k2
  | GApp (f1, arg1), GApp (f2, arg2) ->
    f f1 f2 && List.equal f arg1 arg2
  | GLambda (na1, bk1, t1, c1), GLambda (na2, bk2, t2, c2) ->
    Name.equal na1 na2 && binding_kind_eq bk1 bk2 && f t1 t2 && f c1 c2
  | GProd (na1, bk1, t1, c1), GProd (na2, bk2, t2, c2) ->
    Name.equal na1 na2 && binding_kind_eq bk1 bk2 && f t1 t2 && f c1 c2
  | GLetIn (na1, b1, t1, c1), GLetIn (na2, b2, t2, c2) ->
    Name.equal na1 na2 && f b1 b2 && Option.equal f t1 t2 && f c1 c2
  | GCases (st1, c1, tp1, cl1), GCases (st2, c2, tp2, cl2) ->
    case_style_eq st1 st2 && Option.equal f c1 c2 &&
    List.equal (tomatch_tuple_eq f) tp1 tp2 &&
    List.equal (cases_clause_eq f) cl1 cl2
  | GLetTuple (na1, (n1, p1), c1, t1), GLetTuple (na2, (n2, p2), c2, t2) ->
    List.equal Name.equal na1 na2 && Name.equal n1 n2 &&
    Option.equal f p1 p2 && f c1 c2 && f t1 t2
  | GIf (m1, (pat1, p1), c1, t1), GIf (m2, (pat2, p2), c2, t2) ->
    f m1 m2 && Name.equal pat1 pat2 &&
    Option.equal f p1 p2 && f c1 c2 && f t1 t2
  | GRec (kn1, id1, decl1, t1, c1), GRec (kn2, id2, decl2, t2, c2) ->
    fix_kind_eq f kn1 kn2 && Array.equal Id.equal id1 id2 &&
    Array.equal (fun l1 l2 -> List.equal (glob_decl_eq f) l1 l2) decl1 decl2 &&
    Array.equal f c1 c2 && Array.equal f t1 t2
  | GSort s1, GSort s2 -> glob_sort_eq s1 s2
  | GHole (kn1, nam1, gn1), GHole (kn2, nam2, gn2) ->
    Option.equal (==) gn1 gn2 (** Only thing sensible *) &&
    Namegen.intro_pattern_naming_eq nam1 nam2
  | GCast (c1, t1), GCast (c2, t2) ->
    f c1 c2 && cast_type_eq f t1 t2
  | (GRef _ | GVar _ | GEvar _ | GPatVar _ | GApp _ | GLambda _ | GProd _ | GLetIn _ |
     GCases _ | GLetTuple _ | GIf _ | GRec _ | GSort _ | GHole _ | GCast _ ), _ -> false

let rec glob_constr_eq c = mk_glob_constr_eq glob_constr_eq c

(** Mapping [cast_type] *)

let map_cast_type f = function
  | CastConv a -> CastConv (f a)
  | CastVM a -> CastVM (f a)
  | CastCoerce -> CastCoerce
  | CastNative a -> CastNative (f a)

let smartmap_cast_type f c =
  match c with
    | CastConv a -> let a' = f a in if a' == a then c else CastConv a'
    | CastVM a -> let a' = f a in if a' == a then c else CastVM a'
    | CastCoerce -> CastCoerce
    | CastNative a -> let a' = f a in if a' == a then c else CastNative a'

let map_glob_constr_left_to_right f = DAst.map (function
  | GApp (g,args) ->
      let comp1 = f g in
      let comp2 = Util.List.map_left f args in
      GApp (comp1,comp2)
  | GLambda (na,bk,ty,c) ->
      let comp1 = f ty in
      let comp2 = f c in
      GLambda (na,bk,comp1,comp2)
  | GProd (na,bk,ty,c) ->
      let comp1 = f ty in
      let comp2 = f c in
      GProd (na,bk,comp1,comp2)
  | GLetIn (na,b,t,c) ->
      let comp1 = f b in
      let compt = Option.map f t in
      let comp2 = f c in
      GLetIn (na,comp1,compt,comp2)
  | GCases (sty,rtntypopt,tml,pl) ->
      let comp1 = Option.map f rtntypopt in
      let comp2 = Util.List.map_left (fun (tm,x) -> (f tm,x)) tml in
      let comp3 = Util.List.map_left (CAst.map (fun (idl,p,c) -> (idl,p,f c))) pl in
      GCases (sty,comp1,comp2,comp3)
  | GLetTuple (nal,(na,po),b,c) ->
      let comp1 = Option.map f po in
      let comp2 = f b in
      let comp3 = f c in
      GLetTuple (nal,(na,comp1),comp2,comp3)
  | GIf (c,(na,po),b1,b2) ->
      let comp1 = Option.map f po in
      let comp2 = f b1 in
      let comp3 = f b2 in
      GIf (f c,(na,comp1),comp2,comp3)
  | GRec (fk,idl,bl,tyl,bv) ->
      let comp1 = Array.map (Util.List.map_left (map_glob_decl_left_to_right f)) bl in
      let comp2 = Array.map f tyl in
      let comp3 = Array.map f bv in
      GRec (fk,idl,comp1,comp2,comp3)
  | GCast (c,k) ->
      let comp1 = f c in
      let comp2 = map_cast_type f k in
      GCast (comp1,comp2)
  | (GVar _ | GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) as x -> x
  )

let map_glob_constr = map_glob_constr_left_to_right

let fold_return_type f acc (na,tyopt) = Option.fold_left f acc tyopt

let fold_glob_constr f acc = DAst.with_val (function
  | GVar _ -> acc
  | GApp (c,args) -> List.fold_left f (f acc c) args
  | GLambda (_,_,b,c) | GProd (_,_,b,c) ->
    f (f acc b) c
  | GLetIn (_,b,t,c) ->
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
      (List.fold_left (fun acc (na,k,bbd,bty) ->
	f (Option.fold_left f acc bbd) bty)) acc bl in
    Array.fold_left f (Array.fold_left f acc tyl) bv
  | GCast (c,k) ->
    let acc = match k with
      | CastConv t | CastVM t | CastNative t -> f acc t | CastCoerce -> acc in
    f acc c
  | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> acc
  )

let fold_return_type_with_binders f g v acc (na,tyopt) =
  Option.fold_left (f (Name.fold_right g na v)) acc tyopt

let fold_glob_constr_with_binders g f v acc = DAst.(with_val (function
  | GVar _ -> acc
  | GApp (c,args) -> List.fold_left (f v) (f v acc c) args
  | GLambda (na,_,b,c) | GProd (na,_,b,c) ->
    f (Name.fold_right g na v) (f v acc b) c
  | GLetIn (na,b,t,c) ->
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
	  (fun (v,acc) (na,k,bbd,bty) ->
            (Name.fold_right g na v, f v (Option.fold_left (f v) acc bbd) bty))
          (v,acc)
          bll.(i) in
      f v' (f v acc tyl.(i)) (bv.(i)) in
    Array.fold_left_i f' acc idl
  | GCast (c,k) ->
    let acc = match k with
      | CastConv t | CastVM t | CastNative t -> f v acc t | CastCoerce -> acc in
    f v acc c
  | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> acc))

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
  CWarnings.create ~name:"variable-collision" ~category:"ltac"
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
    (* Check that no other earlier binding hide the one found *)
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
  | GRef (VarRef id,_) as r ->
      if List.exists (fun (_,id') -> Id.equal id id') l then raise UnsoundRenaming
      else r
  | GProd (na,bk,t,c) ->
      let na',l' = update_subst na l in
      GProd (na',bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLambda (na,bk,t,c) ->
      let na',l' = update_subst na l in
      GLambda (na',bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLetIn (na,b,t,c) ->
      let na',l' = update_subst na l in
      GLetIn (na',rename_glob_vars l b,Option.map (rename_glob_vars l) t,rename_glob_vars l' c)
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
           Array.map (List.map (fun (na,k,bbd,bty) ->
             test_na l na; (na,k,Option.map (rename_glob_vars l) bbd,rename_glob_vars l bty))) decls,
           Array.map (rename_glob_vars l) bs,
           Array.map (rename_glob_vars l) ts)
  | _ -> DAst.get (map_glob_constr (rename_glob_vars l) c)
  ) c

(**********************************************************************)
(* Conversion from glob_constr to cases pattern, if possible            *)

let is_gvar id c = match DAst.get c with
| GVar id' -> Id.equal id id'
| _ -> false

let rec cases_pattern_of_glob_constr na = DAst.map (function
  | GVar id ->
    begin match na with
    | Name _ ->
      (* Unable to manage the presence of both an alias and a variable *)
      raise Not_found
    | Anonymous -> PatVar (Name id)
    end
  | GHole (_,_,_) -> PatVar na
  | GRef (ConstructRef cstr,_) -> PatCstr (cstr,[],na)
  | GApp (c, l) ->
    begin match DAst.get c with
    | GRef (ConstructRef cstr,_) ->
      PatCstr (cstr,List.map (cases_pattern_of_glob_constr Anonymous) l,na)
    | _ -> raise Not_found
    end
  | GLetIn (Name id as na',b,None,e) when is_gvar id e && na = Anonymous ->
     (* A canonical encoding of aliases *)
     DAst.get (cases_pattern_of_glob_constr na' b)
  | _ -> raise Not_found
  )

open Declarations
open Term
open Context

(* Keep only patterns which are not bound to a local definitions *)
let drop_local_defs typi args =
    let (decls,_) = decompose_prod_assum typi in
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
    aux (List.rev decls) args

let add_patterns_for_params_remove_local_defs (ind,j) l =
  let (mib,mip) = Global.lookup_inductive ind in
  let nparams = mib.Declarations.mind_nparams in
  let l =
    if mip.mind_consnrealdecls.(j-1) = mip.mind_consnrealargs.(j-1) then
      (* Optimisation *) l
    else
      let typi = mip.mind_nf_lc.(j-1) in
      let (_,typi) = decompose_prod_n_assum (Rel.length mib.mind_params_ctxt) typi in
      drop_local_defs typi l in
  Util.List.addn nparams (DAst.make @@ PatVar Anonymous) l

let add_alias ?loc na c =
  match na with
  | Anonymous -> c
  | Name id -> GLetIn (na,DAst.make ?loc c,None,DAst.make ?loc (GVar id))

(* Turn a closed cases pattern into a glob_constr *)
let rec glob_constr_of_cases_pattern_aux isclosed x = DAst.map_with_loc (fun ?loc -> function
  | PatCstr (cstr,[],na) -> add_alias ?loc na (GRef (ConstructRef cstr,None))
  | PatCstr (cstr,l,na)  ->
      let ref = DAst.make ?loc @@ GRef (ConstructRef cstr,None) in
      let l = add_patterns_for_params_remove_local_defs cstr l in
      add_alias ?loc na (GApp (ref, List.map (glob_constr_of_cases_pattern_aux isclosed) l))
  | PatVar (Name id) when not isclosed ->
      GVar id
  | PatVar Anonymous when not isclosed ->
      GHole (Evar_kinds.QuestionMark {
        Evar_kinds.default_question_mark with Evar_kinds.qm_obligation=Define false;
      },Namegen.IntroAnonymous,None)
  | _ -> raise Not_found
  ) x

let glob_constr_of_closed_cases_pattern p = match DAst.get p with
  | PatCstr (cstr,l,na) ->
      let loc = p.CAst.loc in
      na,glob_constr_of_cases_pattern_aux true (DAst.make ?loc @@ PatCstr (cstr,l,Anonymous))
  | _ ->
      raise Not_found

let glob_constr_of_cases_pattern p = glob_constr_of_cases_pattern_aux false p

(**********************************************************************)
(* Interpreting ltac variables *)

open Pp
open CErrors

let ltac_interp_name { ltac_idents ; ltac_genargs } = function
  | Anonymous -> Anonymous
  | Name id as n ->
      try Name (Id.Map.find id ltac_idents)
      with Not_found ->
        if Id.Map.mem id ltac_genargs then
          user_err (str"Ltac variable"++spc()++ Id.print id ++
                           spc()++str"is not bound to an identifier."++spc()++
                           str"It cannot be used in a binder.")
        else n

let empty_lvar : ltac_var_map = {
  ltac_constrs = Id.Map.empty;
  ltac_uconstrs = Id.Map.empty;
  ltac_idents = Id.Map.empty;
  ltac_genargs = Id.Map.empty;
}
