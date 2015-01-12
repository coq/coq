(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Globnames
open Misctypes
open Glob_term

(* Untyped intermediate terms, after ASTs and before constr. *)

let cases_pattern_loc = function
    PatVar(loc,_) -> loc
  | PatCstr(loc,_,_,_) -> loc

let cases_predicate_names tml =
  List.flatten (List.map (function
    | (tm,(na,None)) -> [na]
    | (tm,(na,Some (_,_,nal))) -> na::nal) tml)

let mkGApp loc p t =
  match p with
  | GApp (loc,f,l) -> GApp (loc,f,l@[t])
  | _ -> GApp (loc,p,[t])

let map_glob_decl_left_to_right f (na,k,obd,ty) =
  let comp1 = Option.map f obd in
  let comp2 = f ty in
  (na,k,comp1,comp2)

let binding_kind_eq bk1 bk2 = match bk1, bk2 with
| Decl_kinds.Explicit, Decl_kinds.Explicit -> true
| Decl_kinds.Implicit, Decl_kinds.Implicit -> true
| _ -> false

let case_style_eq s1 s2 = match s1, s2 with
| LetStyle, LetStyle -> true
| IfStyle, IfStyle -> true
| LetPatternStyle, LetPatternStyle -> true
| MatchStyle, MatchStyle -> true
| RegularStyle, RegularStyle -> true
| _ -> false

let rec cases_pattern_eq p1 p2 = match p1, p2 with
| PatVar (_, na1), PatVar (_, na2) -> Name.equal na1 na2
| PatCstr (_, c1, pl1, na1), PatCstr (_, c2, pl2, na2) ->
  eq_constructor c1 c2 && List.equal cases_pattern_eq pl1 pl2 &&
  Name.equal na1 na2
| _ -> false

let cast_type_eq eq t1 t2 = match t1, t2 with
| CastConv t1, CastConv t2 -> eq t1 t2
| CastVM t1, CastVM t2 -> eq t1 t2
| CastCoerce, CastCoerce -> true
| CastNative t1, CastNative t2 -> eq t1 t2
| _ -> false

let rec glob_constr_eq c1 c2 = match c1, c2 with
| GRef (_, gr1, _), GRef (_, gr2, _) -> eq_gr gr1 gr2
| GVar (_, id1), GVar (_, id2) -> Id.equal id1 id2
| GEvar (_, id1, arg1), GEvar (_, id2, arg2) ->
  Id.equal id1 id2 &&
  List.equal instance_eq arg1 arg2
| GPatVar (_, (b1, pat1)), GPatVar (_, (b2, pat2)) ->
  (b1 : bool) == b2 && Id.equal pat1 pat2
| GApp (_, f1, arg1), GApp (_, f2, arg2) ->
  glob_constr_eq f1 f2 && List.equal glob_constr_eq arg1 arg2
| GLambda (_, na1, bk1, t1, c1), GLambda (_, na2, bk2, t2, c2) ->
  Name.equal na1 na2 && binding_kind_eq bk1 bk2 &&
  glob_constr_eq t1 t2 && glob_constr_eq c1 c2
| GProd (_, na1, bk1, t1, c1), GProd (_, na2, bk2, t2, c2) ->
  Name.equal na1 na2 && binding_kind_eq bk1 bk2 &&
  glob_constr_eq t1 t2 && glob_constr_eq c1 c2
| GLetIn (_, na1, t1, c1), GLetIn (_, na2, t2, c2) ->
  Name.equal na1 na2 && glob_constr_eq t1 t2 && glob_constr_eq c1 c2
| GCases (_, st1, c1, tp1, cl1), GCases (_, st2, c2, tp2, cl2) ->
  case_style_eq st1 st2 && Option.equal glob_constr_eq c1 c2 &&
  List.equal tomatch_tuple_eq tp1 tp2 &&
  List.equal cases_clause_eq cl1 cl2
| GLetTuple (_, na1, (n1, p1), c1, t1), GLetTuple (_, na2, (n2, p2), c2, t2) ->
  List.equal Name.equal na1 na2 && Name.equal n1 n2 &&
  Option.equal glob_constr_eq p1 p2 && glob_constr_eq c1 c2 &&
  glob_constr_eq t1 t2
| GIf (_, m1, (pat1, p1), c1, t1), GIf (_, m2, (pat2, p2), c2, t2) ->
  glob_constr_eq m1 m2 && Name.equal pat1 pat2 &&
  Option.equal glob_constr_eq p1 p2 && glob_constr_eq c1 c2 &&
  glob_constr_eq t1 t2
| GRec (_, kn1, id1, decl1, c1, t1), GRec (_, kn2, id2, decl2, c2, t2) ->
  fix_kind_eq kn1 kn2 && Array.equal Id.equal id1 id2 &&
  Array.equal (fun l1 l2 -> List.equal glob_decl_eq l1 l2) decl1 decl2 &&
  Array.equal glob_constr_eq c1 c2 &&
  Array.equal glob_constr_eq t1 t2
| GSort (_, s1), GSort (_, s2) -> Miscops.glob_sort_eq s1 s2
| GHole (_, kn1, nam1, gn1), GHole (_, kn2, nam2, gn2) ->
  Option.equal (==) gn1 gn2 (** Only thing sensible *) &&
  Miscops.intro_pattern_naming_eq nam1 nam2
| GCast (_, c1, t1), GCast (_, c2, t2) ->
  glob_constr_eq c1 c2 && cast_type_eq glob_constr_eq t1 t2
| _ -> false

and tomatch_tuple_eq (c1, p1) (c2, p2) =
  let eqp (_, i1, na1) (_, i2, na2) =
    eq_ind i1 i2 && List.equal Name.equal na1 na2
  in
  let eq_pred (n1, o1) (n2, o2) = Name.equal n1 n2 && Option.equal eqp o1 o2 in
  glob_constr_eq c1 c2 && eq_pred p1 p2

and cases_clause_eq (_, id1, p1, c1) (_, id2, p2, c2) =
  List.equal Id.equal id1 id2 && List.equal cases_pattern_eq p1 p2 &&
  glob_constr_eq c1 c2

and glob_decl_eq (na1, bk1, c1, t1) (na2, bk2, c2, t2) =
  Name.equal na1 na2 && binding_kind_eq bk1 bk2 &&
  Option.equal glob_constr_eq c1 c2 &&
  glob_constr_eq t1 t2

and fix_kind_eq k1 k2 = match k1, k2 with
| GFix (a1, i1), GFix (a2, i2) ->
  let eq (i1, o1) (i2, o2) =
    Option.equal Int.equal i1 i2 && fix_recursion_order_eq o1 o2
  in
  Int.equal i1 i2 && Array.equal eq a1 a1
| GCoFix i1, GCoFix i2 -> Int.equal i1 i2
| _ -> false

and fix_recursion_order_eq o1 o2 = match o1, o2 with
| GStructRec, GStructRec -> true
| GWfRec c1, GWfRec c2 -> glob_constr_eq c1 c2
| GMeasureRec (c1, o1), GMeasureRec (c2, o2) ->
  glob_constr_eq c1 c2 && Option.equal glob_constr_eq o1 o2
| _ -> false

and instance_eq (x1,c1) (x2,c2) =
  Id.equal x1 x2 && glob_constr_eq c1 c2

let map_glob_constr_left_to_right f = function
  | GApp (loc,g,args) ->
      let comp1 = f g in
      let comp2 = Util.List.map_left f args in
      GApp (loc,comp1,comp2)
  | GLambda (loc,na,bk,ty,c) ->
      let comp1 = f ty in
      let comp2 = f c in
      GLambda (loc,na,bk,comp1,comp2)
  | GProd (loc,na,bk,ty,c) ->
      let comp1 = f ty in
      let comp2 = f c in
      GProd (loc,na,bk,comp1,comp2)
  | GLetIn (loc,na,b,c) ->
      let comp1 = f b in
      let comp2 = f c in
      GLetIn (loc,na,comp1,comp2)
  | GCases (loc,sty,rtntypopt,tml,pl) ->
      let comp1 = Option.map f rtntypopt in
      let comp2 = Util.List.map_left (fun (tm,x) -> (f tm,x)) tml in
      let comp3 = Util.List.map_left (fun (loc,idl,p,c) -> (loc,idl,p,f c)) pl in
      GCases (loc,sty,comp1,comp2,comp3)
  | GLetTuple (loc,nal,(na,po),b,c) ->
      let comp1 = Option.map f po in
      let comp2 = f b in
      let comp3 = f c in
      GLetTuple (loc,nal,(na,comp1),comp2,comp3)
  | GIf (loc,c,(na,po),b1,b2) ->
      let comp1 = Option.map f po in
      let comp2 = f b1 in
      let comp3 = f b2 in
      GIf (loc,f c,(na,comp1),comp2,comp3)
  | GRec (loc,fk,idl,bl,tyl,bv) ->
      let comp1 = Array.map (Util.List.map_left (map_glob_decl_left_to_right f)) bl in
      let comp2 = Array.map f tyl in
      let comp3 = Array.map f bv in
      GRec (loc,fk,idl,comp1,comp2,comp3)
  | GCast (loc,c,k) ->
      let comp1 = f c in
      let comp2 = Miscops.map_cast_type f k in
      GCast (loc,comp1,comp2)
  | (GVar _ | GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) as x -> x

let map_glob_constr = map_glob_constr_left_to_right

let fold_glob_constr f acc =
  let rec fold acc = function
  | GVar _ -> acc
  | GApp (_,c,args) -> List.fold_left fold (fold acc c) args
  | GLambda (_,_,_,b,c) | GProd (_,_,_,b,c) | GLetIn (_,_,b,c) ->
      fold (fold acc b) c
  | GCases (_,_,rtntypopt,tml,pl) ->
      List.fold_left fold_pattern
	(List.fold_left fold (Option.fold_left fold acc rtntypopt) (List.map fst tml))
	pl
    | GLetTuple (_,_,rtntyp,b,c) ->
	fold (fold (fold_return_type acc rtntyp) b) c
    | GIf (_,c,rtntyp,b1,b2) ->
	fold (fold (fold (fold_return_type acc rtntyp) c) b1) b2
    | GRec (_,_,_,bl,tyl,bv) ->
	let acc = Array.fold_left
	  (List.fold_left (fun acc (na,k,bbd,bty) ->
	    fold (Option.fold_left fold acc bbd) bty)) acc bl in
	Array.fold_left fold (Array.fold_left fold acc tyl) bv
    | GCast (_,c,k) ->
        let r = match k with
        | CastConv t | CastVM t | CastNative t -> fold acc t | CastCoerce -> acc
        in
        fold r c
    | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> acc

  and fold_pattern acc (_,idl,p,c) = fold acc c

  and fold_return_type acc (na,tyopt) = Option.fold_left fold acc tyopt

  in fold acc

let iter_glob_constr f = fold_glob_constr (fun () -> f) ()

let same_id na id = match na with
| Anonymous -> false
| Name id' -> Id.equal id id'

let occur_glob_constr id =
  let rec occur = function
    | GVar (loc,id') -> Id.equal id id'
    | GApp (loc,f,args) -> (occur f) || (List.exists occur args)
    | GLambda (loc,na,bk,ty,c) ->
      (occur ty) || (not (same_id na id) && (occur c))
    | GProd (loc,na,bk,ty,c) ->
      (occur ty) || (not (same_id na id) && (occur c))
    | GLetIn (loc,na,b,c) ->
      (occur b) || (not (same_id na id) && (occur c))
    | GCases (loc,sty,rtntypopt,tml,pl) ->
	(occur_option rtntypopt)
        || (List.exists (fun (tm,_) -> occur tm) tml)
	|| (List.exists occur_pattern pl)
    | GLetTuple (loc,nal,rtntyp,b,c) ->
	occur_return_type rtntyp id
        || (occur b) || (not (List.mem_f Name.equal (Name id) nal) && (occur c))
    | GIf (loc,c,rtntyp,b1,b2) ->
	occur_return_type rtntyp id || (occur c) || (occur b1) || (occur b2)
    | GRec (loc,fk,idl,bl,tyl,bv) ->
        not (Array.for_all4 (fun fid bl ty bd ->
          let rec occur_fix = function
              [] -> not (occur ty) && (Id.equal fid id || not(occur bd))
            | (na,k,bbd,bty)::bl ->
                not (occur bty) &&
                (match bbd with
                    Some bd -> not (occur bd)
                  | _ -> true) &&
                (match na with Name id' -> Id.equal id id' | _ -> not (occur_fix bl)) in
          occur_fix bl)
          idl bl tyl bv)
    | GCast (loc,c,k) -> (occur c) || (match k with CastConv t
      | CastVM t | CastNative t -> occur t | CastCoerce -> false)
    | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> false

  and occur_pattern (loc,idl,p,c) = not (Id.List.mem id idl) && (occur c)

  and occur_option = function None -> false | Some p -> occur p

  and occur_return_type (na,tyopt) id = not (same_id na id) && occur_option tyopt

  in occur


let add_name_to_ids set na =
  match na with
    | Anonymous -> set
    | Name id -> Id.Set.add id set

let free_glob_vars  =
  let rec vars bounded vs = function
    | GVar (loc,id') -> if Id.Set.mem id' bounded then vs else Id.Set.add id' vs
    | GApp (loc,f,args) -> List.fold_left (vars bounded) vs (f::args)
    | GLambda (loc,na,_,ty,c) | GProd (loc,na,_,ty,c) | GLetIn (loc,na,ty,c) ->
	let vs' = vars bounded vs ty in
	let bounded' = add_name_to_ids bounded na in
       vars bounded' vs' c
    | GCases (loc,sty,rtntypopt,tml,pl) ->
	let vs1 = vars_option bounded vs rtntypopt in
	let vs2 = List.fold_left (fun vs (tm,_) -> vars bounded vs tm) vs1 tml in
	List.fold_left (vars_pattern bounded) vs2 pl
    | GLetTuple (loc,nal,rtntyp,b,c) ->
	let vs1 = vars_return_type bounded vs rtntyp in
	let vs2 = vars bounded vs1 b in
	let bounded' = List.fold_left add_name_to_ids bounded nal in
	vars bounded' vs2 c
    | GIf (loc,c,rtntyp,b1,b2) ->
	let vs1 = vars_return_type bounded vs rtntyp in
	let vs2 = vars bounded vs1 c in
	let vs3 = vars bounded vs2 b1 in
	vars bounded vs3 b2
    | GRec (loc,fk,idl,bl,tyl,bv) ->
	let bounded' = Array.fold_right Id.Set.add idl bounded in
	let vars_fix i vs fid =
	  let vs1,bounded1 =
	    List.fold_left
	      (fun (vs,bounded) (na,k,bbd,bty) ->
		 let vs' = vars_option bounded vs bbd in
		 let vs'' = vars bounded vs' bty in
		 let bounded' = add_name_to_ids bounded na in
		 (vs'',bounded')
	      )
	      (vs,bounded')
	      bl.(i)
	  in
	  let vs2 = vars bounded1 vs1 tyl.(i) in
	  vars bounded1 vs2 bv.(i)
	in
	Array.fold_left_i vars_fix vs idl
    | GCast (loc,c,k) -> let v = vars bounded vs c in
	(match k with CastConv t | CastVM t | CastNative t -> vars bounded v t | _ -> v)
    | (GSort _ | GHole _ | GRef _ | GEvar _ | GPatVar _) -> vs

  and vars_pattern bounded vs (loc,idl,p,c) =
    let bounded' = List.fold_right Id.Set.add idl bounded  in
    vars bounded' vs c

  and vars_option bounded vs = function None -> vs | Some p -> vars bounded vs p

  and vars_return_type bounded vs (na,tyopt) =
    let bounded' = add_name_to_ids bounded na in
    vars_option bounded' vs tyopt
  in
  fun rt ->
    let vs = vars Id.Set.empty Id.Set.empty rt in
    Id.Set.elements vs

(** Mapping of names in binders *)

(* spiwack: I used a smartmap-style kind of mapping here, because the
   operation will be the identity almost all of the time (with any
   term outside of Ltac to begin with). But to be honest, there would
   probably be no significant penalty in doing reallocation as
   pattern-matching expressions are usually rather small. *)

let map_inpattern_binders f ((loc,id,nal) as x) =
  let r = CList.smartmap f nal in
  if r == nal then x
  else loc,id,r

let map_tomatch_binders f ((c,(na,inp)) as x) : tomatch_tuple =
  let r = Option.smartmap (fun p -> map_inpattern_binders f p) inp in
  if r == inp then x
  else c,(f na, r)

let rec map_case_pattern_binders f = function
  | PatVar (loc,na) as x ->
      let r = f na in
      if r == na then x
      else PatVar (loc,r)
  | PatCstr (loc,c,ps,na) as x ->
      let rna = f na in
      let rps =
        CList.smartmap (fun p -> map_case_pattern_binders f p) ps
      in
      if rna == na && rps == ps then x
      else PatCstr(loc,c,rps,rna)

let map_cases_branch_binders f ((loc,il,cll,rhs) as x) : cases_clause =
  (* spiwack: not sure if I must do something with the list of idents.
     It is intended to be a superset of the free variable of the
     right-hand side, if I understand correctly. But I'm not sure when
     or how they are used. *)
  let r = List.smartmap (fun cl -> map_case_pattern_binders f cl) cll in
  if r == cll then x
  else loc,il,r,rhs

let map_pattern_binders f tomatch branches =
  CList.smartmap (fun tm -> map_tomatch_binders f tm) tomatch,
  CList.smartmap (fun br -> map_cases_branch_binders f br) branches

(** /mapping of names in binders *)

let map_tomatch f (c,pp) : tomatch_tuple = f c , pp

let map_cases_branch f (loc,il,cll,rhs) : cases_clause =
  loc , il , cll , f rhs

let map_pattern f tomatch branches =
  List.map (fun tm -> map_tomatch f tm) tomatch,
  List.map (fun br -> map_cases_branch f br) branches

let loc_of_glob_constr = function
  | GRef (loc,_,_) -> loc
  | GVar (loc,_) -> loc
  | GEvar (loc,_,_) -> loc
  | GPatVar (loc,_) -> loc
  | GApp (loc,_,_) -> loc
  | GLambda (loc,_,_,_,_) -> loc
  | GProd (loc,_,_,_,_) -> loc
  | GLetIn (loc,_,_,_) -> loc
  | GCases (loc,_,_,_,_) -> loc
  | GLetTuple (loc,_,_,_,_) -> loc
  | GIf (loc,_,_,_,_) -> loc
  | GRec (loc,_,_,_,_,_) -> loc
  | GSort (loc,_) -> loc
  | GHole (loc,_,_,_) -> loc
  | GCast (loc,_,_) -> loc

(**********************************************************************)
(* Conversion from glob_constr to cases pattern, if possible            *)

let rec cases_pattern_of_glob_constr na = function
  | GVar (loc,id) ->
    begin match na with
    | Name _ ->
      (* Unable to manage the presence of both an alias and a variable *)
      raise Not_found
    | Anonymous -> PatVar (loc,Name id)
    end
  | GHole (loc,_,_,_) -> PatVar (loc,na)
  | GRef (loc,ConstructRef cstr,_) ->
      PatCstr (loc,cstr,[],na)
  | GApp (loc,GRef (_,ConstructRef cstr,_),l) ->
      PatCstr (loc,cstr,List.map (cases_pattern_of_glob_constr Anonymous) l,na)
  | _ -> raise Not_found

(* Turn a closed cases pattern into a glob_constr *)
let rec glob_constr_of_closed_cases_pattern_aux = function
  | PatCstr (loc,cstr,[],Anonymous) ->
      GRef (loc,ConstructRef cstr,None)
  | PatCstr (loc,cstr,l,Anonymous) ->
      let ref = GRef (loc,ConstructRef cstr,None) in
      GApp (loc,ref, List.map glob_constr_of_closed_cases_pattern_aux l)
  | _ -> raise Not_found

let glob_constr_of_closed_cases_pattern = function
  | PatCstr (loc,cstr,l,na) ->
      na,glob_constr_of_closed_cases_pattern_aux (PatCstr (loc,cstr,l,Anonymous))
  | _ ->
      raise Not_found
