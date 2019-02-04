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
open CErrors
open Util
open Names
open Nameops
open Constr
open Globnames
open Decl_kinds
open Namegen
open Glob_term
open Glob_ops
open Mod_subst
open Notation_term

(**********************************************************************)
(* Utilities                                                          *)

(* helper for NVar, NVar case in eq_notation_constr *)
let get_var_ndx id vs = try Some (List.index Id.equal id vs) with Not_found -> None

let rec eq_notation_constr (vars1,vars2 as vars) t1 t2 = match t1, t2 with
| NRef gr1, NRef gr2 -> GlobRef.equal gr1 gr2
| NVar id1, NVar id2 -> (
   match (get_var_ndx id1 vars1,get_var_ndx id2 vars2) with
   | Some n,Some m -> Int.equal n m
   | None  ,None   -> Id.equal id1 id2
   | _             -> false)
| NApp (t1, a1), NApp (t2, a2) ->
  (eq_notation_constr vars) t1 t2 && List.equal (eq_notation_constr vars) a1 a2
| NHole (_, _, _), NHole (_, _, _) -> true (* FIXME? *)
| NList (i1, j1, t1, u1, b1), NList (i2, j2, t2, u2, b2) ->
  Id.equal i1 i2 && Id.equal j1 j2 && (eq_notation_constr vars) t1 t2 &&
  (eq_notation_constr vars) u1 u2 && b1 == b2
| NLambda (na1, t1, u1), NLambda (na2, t2, u2) ->
  Name.equal na1 na2 && (eq_notation_constr vars) t1 t2 && (eq_notation_constr vars) u1 u2
| NProd (na1, t1, u1), NProd (na2, t2, u2) ->
  Name.equal na1 na2 && (eq_notation_constr vars) t1 t2 && (eq_notation_constr vars) u1 u2
| NBinderList (i1, j1, t1, u1, b1), NBinderList (i2, j2, t2, u2, b2) ->
  Id.equal i1 i2 && Id.equal j1 j2 && (eq_notation_constr vars) t1 t2 &&
  (eq_notation_constr vars) u1 u2 && b1 == b2
| NLetIn (na1, b1, t1, u1), NLetIn (na2, b2, t2, u2) ->
  Name.equal na1 na2 && eq_notation_constr vars b1 b2 &&
  Option.equal (eq_notation_constr vars) t1 t2 && (eq_notation_constr vars) u1 u2
| NCases (_, o1, r1, p1), NCases (_, o2, r2, p2) -> (* FIXME? *)
  let eqpat (p1, t1) (p2, t2) =
    List.equal cases_pattern_eq p1 p2 &&
    (eq_notation_constr vars) t1 t2
  in
  let eqf (t1, (na1, o1)) (t2, (na2, o2)) =
    let eq (i1, n1) (i2, n2) = eq_ind i1 i2 && List.equal Name.equal n1 n2 in
    (eq_notation_constr vars) t1 t2 && Name.equal na1 na2 && Option.equal eq o1 o2
  in
  Option.equal (eq_notation_constr vars) o1 o2 &&
  List.equal eqf r1 r2 &&
  List.equal eqpat p1 p2
| NLetTuple (nas1, (na1, o1), t1, u1), NLetTuple (nas2, (na2, o2), t2, u2) ->
  List.equal Name.equal nas1 nas2 &&
  Name.equal na1 na2 &&
  Option.equal (eq_notation_constr vars) o1 o2 &&
  (eq_notation_constr vars) t1 t2 &&
  (eq_notation_constr vars) u1 u2
| NIf (t1, (na1, o1), u1, r1), NIf (t2, (na2, o2), u2, r2) ->
  (eq_notation_constr vars) t1 t2 &&
  Name.equal na1 na2 &&
  Option.equal (eq_notation_constr vars) o1 o2 &&
  (eq_notation_constr vars) u1 u2 &&
  (eq_notation_constr vars) r1 r2
| NRec (_, ids1, ts1, us1, rs1), NRec (_, ids2, ts2, us2, rs2) -> (* FIXME? *)
  let eq (na1, o1, t1) (na2, o2, t2) =
    Name.equal na1 na2 &&
    Option.equal (eq_notation_constr vars) o1 o2 &&
    (eq_notation_constr vars) t1 t2
  in
  Array.equal Id.equal ids1 ids2 &&
  Array.equal (List.equal eq) ts1 ts2 &&
  Array.equal (eq_notation_constr vars) us1 us2 &&
  Array.equal (eq_notation_constr vars) rs1 rs2
| NSort s1, NSort s2 ->
  glob_sort_eq s1 s2
| NCast (t1, c1), NCast (t2, c2) ->
  (eq_notation_constr vars) t1 t2 && cast_type_eq (eq_notation_constr vars) c1 c2
| NInt i1, NInt i2 ->
   Uint63.equal i1 i2
| (NRef _ | NVar _ | NApp _ | NHole _ | NList _ | NLambda _ | NProd _
  | NBinderList _ | NLetIn _ | NCases _ | NLetTuple _ | NIf _
  | NRec _ | NSort _ | NCast _ | NInt _), _ -> false

(**********************************************************************)
(* Re-interpret a notation as a glob_constr, taking care of binders   *)

let name_to_ident = function
  | Anonymous -> CErrors.user_err Pp.(str "This expression should be a simple identifier.")
  | Name id -> id

let to_id g e id = let e,na = g e (Name id) in e,name_to_ident na

let product_of_cases_patterns patl =
  List.fold_right (fun patl restl ->
     List.flatten (List.map (fun p -> List.map (fun rest -> p::rest) restl) patl))
    patl [[]]

let rec cases_pattern_fold_map ?loc g e = DAst.with_val (function
  | PatVar na ->
      let e',disjpat,na' = g e na in
      e', (match disjpat with
      | None -> [DAst.make ?loc @@ PatVar na']
      | Some ((_,disjpat),_) -> disjpat)
  | PatCstr (cstr,patl,na) ->
      let e',disjpat,na' = g e na in
      if disjpat <> None then user_err (Pp.str "Unable to instantiate an \"as\" clause with a pattern.");
      let e',patl' = List.fold_left_map (cases_pattern_fold_map ?loc g) e patl in
      (* Distribute outwards the inner disjunctive patterns *)
      let disjpatl' = product_of_cases_patterns patl' in
      e', List.map (fun patl' -> DAst.make ?loc @@ PatCstr (cstr,patl',na')) disjpatl'
  )

let subst_binder_type_vars l = function
  | Evar_kinds.BinderType (Name id) ->
     let id =
       try match DAst.get (Id.List.assoc id l) with GVar id' -> id' | _ -> id
       with Not_found -> id in
     Evar_kinds.BinderType (Name id)
  | e -> e

let rec subst_glob_vars l gc = DAst.map (function
  | GVar id as r -> (try DAst.get (Id.List.assoc id l) with Not_found -> r)
  | GProd (Name id,bk,t,c) ->
      let id =
	try match DAst.get (Id.List.assoc id l) with GVar id' -> id' | _ -> id
	with Not_found -> id in
      GProd (Name id,bk,subst_glob_vars l t,subst_glob_vars l c)
  | GLambda (Name id,bk,t,c) ->
      let id =
	try match DAst.get (Id.List.assoc id l) with GVar id' -> id' | _ -> id
	with Not_found -> id in
      GLambda (Name id,bk,subst_glob_vars l t,subst_glob_vars l c)
  | GHole (x,naming,arg) -> GHole (subst_binder_type_vars l x,naming,arg)
  | _ -> DAst.get (map_glob_constr (subst_glob_vars l) gc) (* assume: id is not binding *)
  ) gc

let ldots_var = Id.of_string ".."

let protect g e na =
  let e',disjpat,na = g e na in
  if disjpat <> None then user_err (Pp.str "Unsupported substitution of an arbitrary pattern.");
  e',na

let apply_cases_pattern_term ?loc (ids,disjpat) tm c =
  let eqns = List.map (fun pat -> (CAst.make ?loc (ids,[pat],c))) disjpat in
  DAst.make ?loc @@ GCases (Constr.LetPatternStyle, None, [tm,(Anonymous,None)], eqns)

let apply_cases_pattern ?loc (ids_disjpat,id) c =
  apply_cases_pattern_term ?loc ids_disjpat (DAst.make ?loc (GVar id)) c

let glob_constr_of_notation_constr_with_binders ?loc g f e nc =
  let lt x = DAst.make ?loc x in lt @@ match nc with
  | NVar id -> GVar id
  | NApp (a,args) -> GApp (f e a, List.map (f e) args)
  | NList (x,y,iter,tail,swap) ->
      let t = f e tail in let it = f e iter in
      let innerl = (ldots_var,t)::(if swap then [y, lt @@ GVar x] else []) in
      let inner  = lt @@ GApp (lt @@ GVar (ldots_var),[subst_glob_vars innerl it]) in
      let outerl = (ldots_var,inner)::(if swap then [] else [y, lt @@ GVar x]) in
      DAst.get (subst_glob_vars outerl it)
  | NBinderList (x,y,iter,tail,swap) ->
      let t = f e tail in let it = f e iter in
      let innerl = (ldots_var,t)::(if swap then [y, lt @@ GVar x] else []) in
      let inner  = lt @@ GApp (lt @@ GVar ldots_var,[subst_glob_vars innerl it]) in
      let outerl = (ldots_var,inner)::(if swap then [] else [y, lt @@ GVar x]) in
      DAst.get (subst_glob_vars outerl it)
  | NLambda (na,ty,c) ->
      let e',disjpat,na = g e na in GLambda (na,Explicit,f e ty,Option.fold_right (apply_cases_pattern ?loc) disjpat (f e' c))
  | NProd (na,ty,c) ->
      let e',disjpat,na = g e na in GProd (na,Explicit,f e ty,Option.fold_right (apply_cases_pattern ?loc) disjpat (f e' c))
  | NLetIn (na,b,t,c) ->
      let e',disjpat,na = g e na in
      (match disjpat with
       | None -> GLetIn (na,f e b,Option.map (f e) t,f e' c)
       | Some (disjpat,_id) -> DAst.get (apply_cases_pattern_term ?loc disjpat (f e b) (f e' c)))
  | NCases (sty,rtntypopt,tml,eqnl) ->
      let e',tml' = List.fold_right (fun (tm,(na,t)) (e',tml') ->
	let e',t' = match t with
	| None -> e',None
	| Some (ind,nal) ->
	  let e',nal' = List.fold_right (fun na (e',nal) ->
              let e',na' = protect g e' na in
              e',na'::nal) nal (e',[]) in
          e',Some (CAst.make ?loc (ind,nal')) in
        let e',na' = protect g e' na in
        (e',(f e tm,(na',t'))::tml')) tml (e,[]) in
      let fold (idl,e) na = let (e,disjpat,na) = g e na in ((Name.cons na idl,e),disjpat,na) in
      let eqnl' = List.map (fun (patl,rhs) ->
        let ((idl,e),patl) =
          List.fold_left_map (cases_pattern_fold_map ?loc fold) ([],e) patl in
        let disjpatl = product_of_cases_patterns patl in
        List.map (fun patl -> CAst.make (idl,patl,f e rhs)) disjpatl) eqnl in
      GCases (sty,Option.map (f e') rtntypopt,tml',List.flatten eqnl')
  | NLetTuple (nal,(na,po),b,c) ->
      let e',nal = List.fold_left_map (protect g) e nal in
      let e'',na = protect g e na in
      GLetTuple (nal,(na,Option.map (f e'') po),f e b,f e' c)
  | NIf (c,(na,po),b1,b2) ->
      let e',na = protect g e na in
      GIf (f e c,(na,Option.map (f e') po),f e b1,f e b2)
  | NRec (fk,idl,dll,tl,bl) ->
      let e,dll = Array.fold_left_map (List.fold_left_map (fun e (na,oc,b) ->
          let e,na = protect g e na in
	  (e,(na,Explicit,Option.map (f e) oc,f e b)))) e dll in
      let e',idl = Array.fold_left_map (to_id (protect g)) e idl in
      GRec (fk,idl,dll,Array.map (f e) tl,Array.map (f e') bl)
  | NCast (c,k) -> GCast (f e c,map_cast_type (f e) k)
  | NSort x -> GSort x
  | NHole (x, naming, arg)  -> GHole (x, naming, arg)
  | NRef x -> GRef (x,None)
  | NInt i -> GInt i

let glob_constr_of_notation_constr ?loc x =
  let rec aux () x =
    glob_constr_of_notation_constr_with_binders ?loc (fun () id -> ((),None,id)) aux () x
  in aux () x

(******************************************************************************)
(* Translating a glob_constr into a notation, interpreting recursive patterns *)

type found_variables = {
    vars : Id.t list;
    recursive_term_vars : (Id.t * Id.t) list;
    recursive_binders_vars : (Id.t * Id.t) list;
  }

let add_id r id = r := { !r with vars = id :: (!r).vars }
let add_name r = function Anonymous -> () | Name id -> add_id r id

let is_gvar id c = match DAst.get c with
| GVar id' -> Id.equal id id'
| _ -> false

let split_at_recursive_part c =
  let sub = ref None in
  let rec aux c =
    let loc0 = c.CAst.loc in
    match DAst.get c with
    | GApp (f, c::l) when is_gvar ldots_var f -> (*  *)
      let loc = f.CAst.loc in
      begin match !sub with
      | None ->
        let () = sub := Some c in
        begin match l with
        | []     -> DAst.make ?loc @@ GVar ldots_var
        | _ :: _ -> DAst.make ?loc:loc0 @@ GApp (DAst.make ?loc @@ GVar ldots_var, l)
        end
      | Some _ ->
        (* Not narrowed enough to find only one recursive part *)
        raise Not_found
      end
    | _ -> map_glob_constr aux c in
  let outer_iterator = aux c in
  match !sub with
  | None -> (* No recursive pattern found *) raise Not_found
  | Some c ->
  match DAst.get outer_iterator with
  | GVar v when Id.equal v ldots_var -> (* Not enough context *) raise Not_found
  | _ -> outer_iterator, c

let subtract_loc loc1 loc2 =
  let l1 = fst (Option.cata Loc.unloc (0,0) loc1) in
  let l2 = fst (Option.cata Loc.unloc (0,0) loc2) in
  Some (Loc.make_loc (l1,l2-1))

let check_is_hole id t = match DAst.get t with GHole _ -> () | _ ->
  user_err ?loc:(loc_of_glob_constr t)
   (strbrk "In recursive notation with binders, " ++ Id.print id ++
    strbrk " is expected to come without type.")

let check_pair_matching ?loc x y x' y' revert revert' =
  if not (Id.equal x x' && Id.equal y y' && revert = revert') then
    let x,y = if revert then y,x else x,y in
    let x',y' = if revert' then y',x' else x',y' in
    (* This is a case where one would like to highlight two locations! *)
    user_err ?loc
      (strbrk "Found " ++ Id.print x ++ strbrk " matching " ++ Id.print y ++
       strbrk " while " ++ Id.print x' ++ strbrk " matching " ++ Id.print y' ++
       strbrk " was first found.")

let pair_equal eq1 eq2 (a,b) (a',b') = eq1 a a' && eq2 b b'

let mem_recursive_pair (x,y) l = List.mem_f (pair_equal Id.equal Id.equal) (x,y) l

type recursive_pattern_kind =
| RecursiveTerms of bool (* in reverse order *)
| RecursiveBinders of bool (* in reverse order *)

let compare_recursive_parts recvars found f f' (iterator,subc) =
  let diff = ref None in
  let terminator = ref None in
  let rec aux c1 c2 = match DAst.get c1, DAst.get c2 with
  | GVar v, term when Id.equal v ldots_var ->
      (* We found the pattern *)
      assert (match !terminator with None -> true | Some _ -> false);
      terminator := Some c2;
      true
  | GApp (f,l1), GApp (term, l2) ->
    begin match DAst.get f with
    | GVar v when Id.equal v ldots_var ->
      (* We found the pattern, but there are extra arguments *)
      (* (this allows e.g. alternative (recursive) notation of application) *)
      assert (match !terminator with None -> true | Some _ -> false);
      terminator := Some term;
      List.for_all2eq aux l1 l2
    | _ -> mk_glob_constr_eq aux c1 c2
    end
  | GVar x, GVar y
        when mem_recursive_pair (x,y) recvars || mem_recursive_pair (y,x) recvars ->
      (* We found the position where it differs *)
      let revert = mem_recursive_pair (y,x) recvars in
      let x,y = if revert then y,x else x,y in
      begin match !diff with
      | None ->
        let () = diff := Some (x, y, RecursiveTerms revert) in
        true
      | Some (x', y', RecursiveTerms revert')
      | Some (x', y', RecursiveBinders revert') ->
        check_pair_matching ?loc:c1.CAst.loc x y x' y' revert revert';
        true
      end
  | GLambda (Name x,_,t_x,c), GLambda (Name y,_,t_y,term)
  | GProd (Name x,_,t_x,c), GProd (Name y,_,t_y,term)
        when mem_recursive_pair (x,y) recvars || mem_recursive_pair (y,x) recvars ->
      (* We found a binding position where it differs *)
      check_is_hole x t_x;
      check_is_hole y t_y;
      let revert = mem_recursive_pair (y,x) recvars in
      let x,y = if revert then y,x else x,y in
      begin match !diff with
      | None ->
        let () = diff := Some (x, y, RecursiveBinders revert) in
        aux c term
      | Some (x', y', RecursiveBinders revert') ->
        check_pair_matching ?loc:c1.CAst.loc x y x' y' revert revert';
        true
      | Some (x', y', RecursiveTerms revert') ->
        (* Recursive binders have precedence: they can be coerced to
           terms but not reciprocally *)
        check_pair_matching ?loc:c1.CAst.loc x y x' y' revert revert';
        let () = diff := Some (x, y, RecursiveBinders revert) in
        true
      end
  | _ ->
      mk_glob_constr_eq aux c1 c2 in
  if aux iterator subc then
    match !diff with
    | None ->
	let loc1 = loc_of_glob_constr iterator in
	let loc2 = loc_of_glob_constr (Option.get !terminator) in
        (* Here, we would need a loc made of several parts ... *)
        user_err ?loc:(subtract_loc loc1 loc2)
          (str "Both ends of the recursive pattern are the same.")
    | Some (x,y,RecursiveTerms revert) ->
        (* By arbitrary convention, we use the second variable of the pair
           as the place-holder for the iterator *)
        let iterator =
          f' (if revert then iterator else subst_glob_vars [x, DAst.make @@ GVar y] iterator) in
        (* found variables have been collected by compare_constr *)
        found := { !found with vars = List.remove Id.equal y (!found).vars;
                               recursive_term_vars = List.add_set (pair_equal Id.equal Id.equal) (x,y) (!found).recursive_term_vars };
        NList (x,y,iterator,f (Option.get !terminator),revert)
    | Some (x,y,RecursiveBinders revert) ->
        let iterator =
          f' (if revert then iterator else subst_glob_vars [x, DAst.make @@ GVar y] iterator) in
        (* found have been collected by compare_constr *)
        found := { !found with vars = List.remove Id.equal y (!found).vars;
                               recursive_binders_vars = List.add_set (pair_equal Id.equal Id.equal) (x,y) (!found).recursive_binders_vars };
        NBinderList (x,y,iterator,f (Option.get !terminator),revert)
  else
    raise Not_found

let notation_constr_and_vars_of_glob_constr recvars a =
  let found = ref { vars = []; recursive_term_vars = []; recursive_binders_vars = [] } in
  let has_ltac = ref false in
  (* Turn a glob_constr into a notation_constr by first trying to find a recursive pattern *)
  let rec aux c =
    let keepfound = !found in
    (* n^2 complexity but small and done only once per notation *)
    try compare_recursive_parts recvars found aux aux' (split_at_recursive_part c)
    with Not_found ->
    found := keepfound;
    match DAst.get c with
    | GApp (t, [_]) ->
      begin match DAst.get t with
      | GVar f when Id.equal f ldots_var ->
	(* Fall on the second part of the recursive pattern w/o having
	   found the first part *)
        let loc = t.CAst.loc in
	user_err ?loc 
	(str "Cannot find where the recursive pattern starts.")
      | _ -> aux' c
      end
    | _c ->
	aux' c
  and aux' x = DAst.with_val (function
  | GVar id -> if not (Id.equal id ldots_var) then add_id found id; NVar id
  | GApp (g,args) -> NApp (aux g, List.map aux args)
  | GLambda (na,bk,ty,c) -> add_name found na; NLambda (na,aux ty,aux c)
  | GProd (na,bk,ty,c) -> add_name found na; NProd (na,aux ty,aux c)
  | GLetIn (na,b,t,c) -> add_name found na; NLetIn (na,aux b,Option.map aux t, aux c)
  | GCases (sty,rtntypopt,tml,eqnl) ->
      let f {CAst.v=(idl,pat,rhs)} = List.iter (add_id found) idl; (pat,aux rhs) in
      NCases (sty,Option.map aux rtntypopt,
        List.map (fun (tm,(na,x)) ->
	  add_name found na;
	  Option.iter
            (fun {CAst.v=(_,nl)} -> List.iter (add_name found) nl) x;
          (aux tm,(na,Option.map (fun {CAst.v=(ind,nal)} -> (ind,nal)) x))) tml,
        List.map f eqnl)
  | GLetTuple (nal,(na,po),b,c) ->
      add_name found na;
      List.iter (add_name found) nal;
      NLetTuple (nal,(na,Option.map aux po),aux b,aux c)
  | GIf (c,(na,po),b1,b2) ->
      add_name found na;
      NIf (aux c,(na,Option.map aux po),aux b1,aux b2)
  | GRec (fk,idl,dll,tl,bl) ->
      Array.iter (add_id found) idl;
      let dll = Array.map (List.map (fun (na,bk,oc,b) ->
	 if bk != Explicit then
	   user_err Pp.(str "Binders marked as implicit not allowed in notations.");
	 add_name found na; (na,Option.map aux oc,aux b))) dll in
      NRec (fk,idl,dll,Array.map aux tl,Array.map aux bl)
  | GCast (c,k) -> NCast (aux c,map_cast_type aux k)
  | GSort s -> NSort s
  | GInt i -> NInt i
  | GHole (w,naming,arg) ->
     if arg != None then has_ltac := true;
     NHole (w, naming, arg)
  | GRef (r,_) -> NRef r
  | GEvar _ | GPatVar _ ->
      user_err Pp.(str "Existential variables not allowed in notations.")
  ) x
  in
  let t = aux a in
  (* Side effect *)
  t, !found, !has_ltac

let check_variables_and_reversibility nenv
  { vars = found; recursive_term_vars = foundrec; recursive_binders_vars = foundrecbinding } =
  let injective = ref [] in
  let recvars = nenv.ninterp_rec_vars in
  let fold _ y accu = Id.Set.add y accu in
  let useless_vars = Id.Map.fold fold recvars Id.Set.empty in
  let filter y _ = not (Id.Set.mem y useless_vars) in
  let vars = Id.Map.filter filter nenv.ninterp_var_type in
  let check_recvar x =
    if Id.List.mem x found then
      user_err  (Id.print x ++
	strbrk " should only be used in the recursive part of a pattern.") in
  let check (x, y) = check_recvar x; check_recvar y in
  let () = List.iter check foundrec in
  let () = List.iter check foundrecbinding in
  let check_bound x =
    if not (Id.List.mem x found) then
      if Id.List.mem_assoc x foundrec ||
         Id.List.mem_assoc x foundrecbinding ||
         Id.List.mem_assoc_sym x foundrec ||
         Id.List.mem_assoc_sym x foundrecbinding
      then
	user_err Pp.(str
          (Id.to_string x ^
          " should not be bound in a recursive pattern of the right-hand side."))
      else injective := x :: !injective
  in
  let check_pair s x y where =
    if not (mem_recursive_pair (x,y) where) then
      user_err  (strbrk "in the right-hand side, " ++ Id.print x ++
	str " and " ++ Id.print y ++ strbrk " should appear in " ++ str s ++
	str " position as part of a recursive pattern.") in
  let check_type x typ =
    match typ with
    | NtnInternTypeAny ->
	begin
	  try check_pair "term" x (Id.Map.find x recvars) foundrec
	  with Not_found -> check_bound x
	end
    | NtnInternTypeOnlyBinder ->
	begin
	  try check_pair "binding" x (Id.Map.find x recvars) foundrecbinding
	  with Not_found -> check_bound x
        end in
  Id.Map.iter check_type vars;
  List.rev !injective

let notation_constr_of_glob_constr nenv a =
  let recvars = Id.Map.bindings nenv.ninterp_rec_vars in
  let a, found, has_ltac = notation_constr_and_vars_of_glob_constr recvars a in
  let injective = check_variables_and_reversibility nenv found in
  let status = if has_ltac then HasLtac else match injective with
  | [] -> APrioriReversible
  | l -> NonInjective l in
  a, status

(**********************************************************************)
(* Substitution of kernel names, avoiding a list of bound identifiers *)

let notation_constr_of_constr avoiding t =
  let t = EConstr.of_constr t in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let t = Detyping.detype Detyping.Now false avoiding env evd t in
  let nenv = {
    ninterp_var_type = Id.Map.empty;
    ninterp_rec_vars = Id.Map.empty;
  } in
  notation_constr_of_glob_constr nenv t

let rec subst_pat subst pat =
  match DAst.get pat with
  | PatVar _ -> pat
  | PatCstr (((kn,i),j),cpl,n) ->
      let kn' = subst_mind subst kn
      and cpl' = List.Smart.map (subst_pat subst) cpl in
      if kn' == kn && cpl' == cpl then pat else
        DAst.make ?loc:pat.CAst.loc @@ PatCstr (((kn',i),j),cpl',n)

let rec subst_notation_constr subst bound raw =
  match raw with
  | NRef ref ->
      let ref',t = subst_global subst ref in
      if ref' == ref then raw else (match t with
          | None -> NRef ref'
          | Some t ->
            fst (notation_constr_of_constr bound t.Univ.univ_abstracted_value))

  | NVar _ -> raw

  | NApp (r,rl) ->
      let r' = subst_notation_constr subst bound r
      and rl' = List.Smart.map (subst_notation_constr subst bound) rl in
	if r' == r && rl' == rl then raw else
	  NApp(r',rl')

  | NList (id1,id2,r1,r2,b) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NList (id1,id2,r1',r2',b)

  | NLambda (n,r1,r2) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NLambda (n,r1',r2')

  | NProd (n,r1,r2) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
	  NProd (n,r1',r2')

  | NBinderList (id1,id2,r1,r2,b) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && r2' == r2 then raw else
          NBinderList (id1,id2,r1',r2',b)

  | NLetIn (n,r1,t,r2) ->
      let r1' = subst_notation_constr subst bound r1 in
      let t' = Option.Smart.map (subst_notation_constr subst bound) t in
      let r2' = subst_notation_constr subst bound r2 in
	if r1' == r1 && t == t' && r2' == r2 then raw else
	  NLetIn (n,r1',t',r2')

  | NCases (sty,rtntypopt,rl,branches) ->
      let rtntypopt' = Option.Smart.map (subst_notation_constr subst bound) rtntypopt
      and rl' = List.Smart.map
        (fun (a,(n,signopt) as x) ->
	  let a' = subst_notation_constr subst bound a in
	  let signopt' = Option.map (fun ((indkn,i),nal as z) ->
	    let indkn' = subst_mind subst indkn in
	    if indkn == indkn' then z else ((indkn',i),nal)) signopt in
	  if a' == a && signopt' == signopt then x else (a',(n,signopt')))
        rl
      and branches' = List.Smart.map
                        (fun (cpl,r as branch) ->
                           let cpl' = List.Smart.map (subst_pat subst) cpl
                           and r' = subst_notation_constr subst bound r in
                             if cpl' == cpl && r' == r then branch else
                               (cpl',r'))
                        branches
      in
        if rtntypopt' == rtntypopt && rtntypopt == rtntypopt' &&
          rl' == rl && branches' == branches then raw else
          NCases (sty,rtntypopt',rl',branches')

  | NLetTuple (nal,(na,po),b,c) ->
      let po' = Option.Smart.map (subst_notation_constr subst bound) po
      and b' = subst_notation_constr subst bound b
      and c' = subst_notation_constr subst bound c in
	if po' == po && b' == b && c' == c then raw else
	  NLetTuple (nal,(na,po'),b',c')

  | NIf (c,(na,po),b1,b2) ->
      let po' = Option.Smart.map (subst_notation_constr subst bound) po
      and b1' = subst_notation_constr subst bound b1
      and b2' = subst_notation_constr subst bound b2
      and c' = subst_notation_constr subst bound c in
	if po' == po && b1' == b1 && b2' == b2 && c' == c then raw else
	  NIf (c',(na,po'),b1',b2')

  | NRec (fk,idl,dll,tl,bl) ->
      let dll' =
        Array.Smart.map (List.Smart.map (fun (na,oc,b as x) ->
          let oc' =  Option.Smart.map (subst_notation_constr subst bound) oc in
	  let b' =  subst_notation_constr subst bound b in
	  if oc' == oc && b' == b then x else (na,oc',b'))) dll in
      let tl' = Array.Smart.map (subst_notation_constr subst bound) tl in
      let bl' = Array.Smart.map (subst_notation_constr subst bound) bl in
      if dll' == dll && tl' == tl && bl' == bl then raw else
	  NRec (fk,idl,dll',tl',bl')

  | NSort _ -> raw
  | NInt _ -> raw

  | NHole (knd, naming, solve) ->
    let nknd = match knd with
    | Evar_kinds.ImplicitArg (ref, i, b) ->
      let nref, _ = subst_global subst ref in
      if nref == ref then knd else Evar_kinds.ImplicitArg (nref, i, b)
    | _ -> knd
    in
    let nsolve = Option.Smart.map (Genintern.generic_substitute subst) solve in
    if nsolve == solve && nknd == knd then raw
    else NHole (nknd, naming, nsolve)

  | NCast (r1,k) ->
      let r1' = subst_notation_constr subst bound r1 in
      let k' = smartmap_cast_type (subst_notation_constr subst bound) k in
      if r1' == r1 && k' == k then raw else NCast(r1',k')

let subst_interpretation subst (metas,pat) =
  let bound = List.fold_left (fun accu (id, _) -> Id.Set.add id accu) Id.Set.empty metas in
  (metas,subst_notation_constr subst bound pat)

(**********************************************************************)
(* Pattern-matching a [glob_constr] against a [notation_constr]       *)

let abstract_return_type_context pi mklam tml rtno =
  Option.map (fun rtn ->
    let nal =
      List.flatten (List.map (fun (_,(na,t)) ->
	match t with Some x -> (pi x)@[na] | None -> [na]) tml) in
    List.fold_right mklam nal rtn)
    rtno

let abstract_return_type_context_glob_constr tml rtn =
  abstract_return_type_context (fun {CAst.v=(_,nal)} -> nal)
    (fun na c -> DAst.make @@
      GLambda(na,Explicit,DAst.make @@ GHole(Evar_kinds.InternalHole,IntroAnonymous,None),c)) tml rtn

let abstract_return_type_context_notation_constr tml rtn =
  abstract_return_type_context snd
    (fun na c -> NLambda(na,NHole (Evar_kinds.InternalHole, IntroAnonymous, None),c)) tml rtn

let is_term_meta id metas =
  try match Id.List.assoc id metas with _,(NtnTypeConstr | NtnTypeConstrList) -> true | _ -> false
  with Not_found -> false

let is_onlybinding_strict_meta id metas =
  try match Id.List.assoc id metas with _,NtnTypeBinder (NtnParsedAsPattern true) -> true | _ -> false
  with Not_found -> false

let is_onlybinding_meta id metas =
  try match Id.List.assoc id metas with _,NtnTypeBinder _ -> true | _ -> false
  with Not_found -> false

let is_onlybinding_pattern_like_meta isvar id metas =
  try match Id.List.assoc id metas with
      | _,NtnTypeBinder (NtnBinderParsedAsConstr
                           (AsIdentOrPattern | AsStrictPattern)) -> true
      | _,NtnTypeBinder (NtnParsedAsPattern strict) -> not (strict && isvar)
      | _ -> false
  with Not_found -> false

let is_bindinglist_meta id metas =
  try match Id.List.assoc id metas with _,NtnTypeBinderList -> true | _ -> false
  with Not_found -> false

exception No_match

let rec alpha_var id1 id2 = function
  | (i1,i2)::_ when Id.equal i1 id1 -> Id.equal i2 id2
  | (i1,i2)::_ when Id.equal i2 id2 -> Id.equal i1 id1
  | _::idl -> alpha_var id1 id2 idl
  | [] -> Id.equal id1 id2

let alpha_rename alpmetas v =
  if alpmetas == [] then v
  else try rename_glob_vars alpmetas v with UnsoundRenaming -> raise No_match

let add_env (alp,alpmetas) (terms,termlists,binders,binderlists) var v =
  (* Check that no capture of binding variables occur *)
  (* [alp] is used when matching a pattern "fun x => ... x ... ?var ... x ..."
     with an actual term "fun z => ... z ..." when "x" is not bound in the
     notation, as in "Notation "'twice_upto' y" := (fun x => x + x + y)". Then
     we keep (z,x) in alp, and we have to check that what the [v] which is bound
     to [var] does not contain z *)
  if not (Id.equal ldots_var var) &&
     List.exists (fun (id,_) -> occur_glob_constr id v) alp then raise No_match;
  (* [alpmetas] is used when matching a pattern "fun x => ... x ... ?var ... x ..."
     with an actual term "fun z => ... z ..." when "x" is bound in the
     notation and the name "x" cannot be changed to "z", e.g. because
     used at another occurrence, as in "Notation "'lam' y , P & Q" :=
     ((fun y => P),(fun y => Q))". Then, we keep (z,y) in alpmetas, and we
     have to check that "fun z => ... z ..." denotes the same term as
     "fun x => ... x ... ?var ... x" up to alpha-conversion when [var]
     is instantiated by [v];
     Currently, we fail, but, eventually, [x] in [v] could be replaced by [x],
     and, in match_, when finding "x" in subterm, failing because of a capture,
     and, in match_, when finding "z" in subterm, replacing it with "x",
     and, in an even further step, being even more robust, independent of the order, so
     that e.g. the notation for ex2 works on "x y |- ex2 (fun x => y=x) (fun y => x=y)"
     by giving, say, "exists2 x0, y=x0 & x=x0", but this would typically require the
     glob_constr_eq in bind_term_env to be postponed in match_notation_constr, and the
     choice of exact variable be done there; but again, this would be a non-trivial
     refinement *)
  let v = alpha_rename alpmetas v in
  (* TODO: handle the case of multiple occs in different scopes *)
  ((var,v)::terms,termlists,binders,binderlists)

let add_termlist_env (alp,alpmetas) (terms,termlists,binders,binderlists) var vl =
  if List.exists (fun (id,_) -> List.exists (occur_glob_constr id) vl) alp then raise No_match;
  let vl = List.map (alpha_rename alpmetas) vl in
  (terms,(var,vl)::termlists,binders,binderlists)

let add_binding_env alp (terms,termlists,binders,binderlists) var v =
  (* TODO: handle the case of multiple occs in different scopes *)
  (terms,termlists,(var,v)::binders,binderlists)

let add_bindinglist_env (terms,termlists,binders,binderlists) x bl =
  (terms,termlists,binders,(x,bl)::binderlists)

let rec map_cases_pattern_name_left f = DAst.map (function
  | PatVar na -> PatVar (f na)
  | PatCstr (c,l,na) -> PatCstr (c,List.map_left (map_cases_pattern_name_left f) l,f na)
  )

let rec fold_cases_pattern_eq f x p p' =
  let loc = p.CAst.loc in
  match DAst.get p, DAst.get p' with
  | PatVar na, PatVar na' -> let x,na = f x na na' in x, DAst.make ?loc @@ PatVar na
  | PatCstr (c,l,na), PatCstr (c',l',na') when eq_constructor c c' ->
     let x,l = fold_cases_pattern_list_eq f x l l' in
     let x,na = f x na na' in
     x, DAst.make ?loc @@ PatCstr (c,l,na)
  | _ -> failwith "Not equal"

and fold_cases_pattern_list_eq f x pl pl' = match pl, pl' with
  | [], [] -> x, []
  | p::pl, p'::pl' ->
     let x, p = fold_cases_pattern_eq f x p p' in
     let x, pl = fold_cases_pattern_list_eq f x pl pl' in
     x, p :: pl
  | _ -> assert false

let rec cases_pattern_eq p1 p2 = match DAst.get p1, DAst.get p2 with
| PatVar na1, PatVar na2 -> Name.equal na1 na2
| PatCstr (c1, pl1, na1), PatCstr (c2, pl2, na2) ->
  eq_constructor c1 c2 && List.equal cases_pattern_eq pl1 pl2 &&
  Name.equal na1 na2
| _ -> false

let rec pat_binder_of_term t = DAst.map (function
  | GVar id -> PatVar (Name id)
  | GApp (t, l) ->
    begin match DAst.get t with
    | GRef (ConstructRef cstr,_) ->
     let nparams = Inductiveops.inductive_nparams (fst cstr) in
     let _,l = List.chop nparams l in
     PatCstr (cstr, List.map pat_binder_of_term l, Anonymous)
    | _ -> raise No_match
    end
  | _ -> raise No_match
  ) t

let unify_name_upto alp na na' =
  match na, na' with
  | Anonymous, na' -> alp, na'
  | na, Anonymous -> alp, na
  | Name id, Name id' ->
     if Id.equal id id' then alp, na'
     else (fst alp,(id,id')::snd alp), na'

let unify_pat_upto alp p p' =
  try fold_cases_pattern_eq unify_name_upto alp p p' with Failure _ -> raise No_match

let unify_term alp v v' =
  match DAst.get v, DAst.get v' with
  | GHole _, _ -> v'
  | _, GHole _ -> v
  | _, _ -> if glob_constr_eq (alpha_rename (snd alp) v) v' then v else raise No_match

let unify_opt_term alp v v' =
  match v, v' with
  | Some t, Some t' -> Some (unify_term alp t t')
  | (Some _ as x), None | None, (Some _ as x) -> x
  | None, None -> None

let unify_binding_kind bk bk' = if bk == bk' then bk' else raise No_match

let unify_binder_upto alp b b' =
  let loc, loc' = CAst.(b.loc, b'.loc) in
  match DAst.get b, DAst.get b' with
  | GLocalAssum (na,bk,t), GLocalAssum (na',bk',t') ->
     let alp, na = unify_name_upto alp na na' in
     alp, DAst.make ?loc @@ GLocalAssum (na, unify_binding_kind bk bk', unify_term alp t t')
  | GLocalDef (na,bk,c,t), GLocalDef (na',bk',c',t') ->
     let alp, na = unify_name_upto alp na na' in
     alp, DAst.make ?loc @@ GLocalDef (na, unify_binding_kind bk bk', unify_term alp c c', unify_opt_term alp t t')
  | GLocalPattern ((disjpat,ids),id,bk,t), GLocalPattern ((disjpat',_),_,bk',t') when List.length disjpat = List.length disjpat' ->
     let alp, p = List.fold_left2_map unify_pat_upto alp disjpat disjpat' in
     alp, DAst.make ?loc @@ GLocalPattern ((p,ids), id, unify_binding_kind bk bk', unify_term alp t t')
  | _ -> raise No_match

let rec unify_terms alp vl vl' =
  match vl, vl' with
  | [], [] -> []
  | v :: vl, v' :: vl' -> unify_term alp v v' :: unify_terms alp vl vl'
  | _ -> raise No_match

let rec unify_binders_upto alp bl bl' =
  match bl, bl' with
  | [], [] -> alp, []
  | b :: bl, b' :: bl' ->
     let alp,b = unify_binder_upto alp b b' in
     let alp,bl = unify_binders_upto alp bl bl' in
     alp, b :: bl
  | _ -> raise No_match

let unify_id alp id na' =
  match na' with
  | Anonymous -> Name (rename_var (snd alp) id)
  | Name id' ->
     if Id.equal (rename_var (snd alp) id) id' then na' else raise No_match

let unify_pat alp p p' =
  if cases_pattern_eq (map_cases_pattern_name_left (Name.map (rename_var (snd alp))) p) p' then p'
  else raise No_match

let unify_term_binder alp c = DAst.(map (fun b' ->
  match DAst.get c, b' with
  | GVar id, GLocalAssum (na', bk', t') ->
     GLocalAssum (unify_id alp id na', bk', t')
  | _, GLocalPattern (([p'],ids), id, bk', t') ->
     let p = pat_binder_of_term c in
     GLocalPattern (([unify_pat alp p p'],ids), id, bk', t')
  | _ -> raise No_match))

let rec unify_terms_binders alp cl bl' =
  match cl, bl' with
  | [], [] -> []
  | c :: cl, b' :: bl' ->
     begin match DAst.get b' with
     | GLocalDef ( _, _, _, t) -> unify_terms_binders alp cl bl'
     | _ -> unify_term_binder alp c b' :: unify_terms_binders alp cl bl'
     end
  | _ -> raise No_match

let bind_term_env alp (terms,termlists,binders,binderlists as sigma) var v =
  try
    (* If already bound to a term, unify with the new term *)
    let v' = Id.List.assoc var terms in
    let v'' = unify_term alp v v' in
    if v'' == v' then sigma else
      let sigma = (Id.List.remove_assoc var terms,termlists,binders,binderlists) in
      add_env alp sigma var v
  with Not_found -> add_env alp sigma var v

let bind_termlist_env alp (terms,termlists,binders,binderlists as sigma) var vl =
  try
    (* If already bound to a list of term, unify with the new terms *)
    let vl' = Id.List.assoc var termlists in
    let vl = unify_terms alp vl vl' in
    let sigma = (terms,Id.List.remove_assoc var termlists,binders,binderlists) in
    add_termlist_env alp sigma var vl
  with Not_found -> add_termlist_env alp sigma var vl

let bind_term_as_binding_env alp (terms,termlists,binders,binderlists as sigma) var id =
  try
    (* If already bound to a term, unify the binder and the term *)
    match DAst.get (Id.List.assoc var terms) with
    | GVar id' ->
       (if not (Id.equal id id') then (fst alp,(id,id')::snd alp) else alp),
       sigma
    | t ->
       (* The term is a non-variable pattern *)
       raise No_match
  with Not_found ->
    (* The matching against a term allowing to find the instance has not been found yet *)
    (* If it will be a different name, we shall unfortunately fail *)
    (* TODO: look at the consequences for alp *)
    alp, add_env alp sigma var (DAst.make @@ GVar id)

let force_cases_pattern c =
  DAst.make ?loc:c.CAst.loc (DAst.get c)

let bind_binding_as_term_env alp (terms,termlists,binders,binderlists as sigma) var c =
  let pat = try force_cases_pattern (cases_pattern_of_glob_constr Anonymous c) with Not_found -> raise No_match in
  try
    (* If already bound to a binder, unify the term and the binder *)
    let patl' = Id.List.assoc var binders in
    let patl'' = List.map2 (unify_pat alp) [pat] patl' in
    if patl' == patl'' then sigma
    else
      let sigma = (terms,termlists,Id.List.remove_assoc var binders,binderlists) in
      add_binding_env alp sigma var patl''
  with Not_found -> add_binding_env alp sigma var [pat]

let bind_binding_env alp (terms,termlists,binders,binderlists as sigma) var disjpat =
  try
    (* If already bound to a binder possibly *)
    (* generating an alpha-renaming from unifying the new binder *)
    let disjpat' = Id.List.assoc var binders in
    let alp, disjpat = List.fold_left2_map unify_pat_upto alp disjpat disjpat' in
    let sigma = (terms,termlists,Id.List.remove_assoc var binders,binderlists) in
    alp, add_binding_env alp sigma var disjpat
  with Not_found -> alp, add_binding_env alp sigma var disjpat

let bind_bindinglist_env alp (terms,termlists,binders,binderlists as sigma) var bl =
  let bl = List.rev bl in
  try
    (* If already bound to a list of binders possibly *)
    (* generating an alpha-renaming from unifying the new binders *)
    let bl' = Id.List.assoc var binderlists in
    let alp, bl = unify_binders_upto alp bl bl' in
    let sigma = (terms,termlists,binders,Id.List.remove_assoc var binderlists) in
    alp, add_bindinglist_env sigma var bl
  with Not_found ->
    alp, add_bindinglist_env sigma var bl

let bind_bindinglist_as_termlist_env alp (terms,termlists,binders,binderlists) var cl =
  try
    (* If already bound to a list of binders, unify the terms and binders *)
    let bl' = Id.List.assoc var binderlists in
    let bl = unify_terms_binders alp cl bl' in
    let sigma = (terms,termlists,binders,Id.List.remove_assoc var binderlists) in
    add_bindinglist_env sigma var bl
  with Not_found ->
    anomaly (str "There should be a binder list bindings this list of terms.")

let match_fix_kind fk1 fk2 =
  match (fk1,fk2) with
  | GCoFix n1, GCoFix n2 -> Int.equal n1 n2
  | GFix (nl1,n1), GFix (nl2,n2) ->
      let test (n1, _) (n2, _) = match n1, n2 with
      | _, None -> true
      | Some id1, Some id2 -> Int.equal id1 id2
      | _ -> false
      in
      Int.equal n1 n2 &&
      Array.for_all2 test nl1 nl2
  | _ -> false

let match_opt f sigma t1 t2 = match (t1,t2) with
  | None, None -> sigma
  | Some t1, Some t2 -> f sigma t1 t2
  | _ -> raise No_match

let match_names metas (alp,sigma) na1 na2 = match (na1,na2) with
  | (na1,Name id2) when is_onlybinding_strict_meta id2 metas ->
      raise No_match
  | (na1,Name id2) when is_onlybinding_meta id2 metas ->
      bind_binding_env alp sigma id2 [DAst.make (PatVar na1)]
  | (Name id1,Name id2) when is_term_meta id2 metas ->
      (* We let the non-binding occurrence define the rhs and hence reason up to *)
      (* alpha-conversion for the given occurrence of the name (see #4592)) *)
      bind_term_as_binding_env alp sigma id2 id1
  | (Anonymous,Name id2) when is_term_meta id2 metas ->
      (* We let the non-binding occurrence define the rhs *)
      alp, sigma
  | (Name id1,Name id2) -> ((id1,id2)::fst alp, snd alp),sigma
  | (Anonymous,Anonymous) -> alp,sigma
  | _ -> raise No_match

let rec match_cases_pattern_binders allow_catchall metas (alp,sigma as acc) pat1 pat2 =
  match DAst.get pat1, DAst.get pat2 with
  | PatVar _, PatVar (Name id2) when is_onlybinding_pattern_like_meta true id2 metas ->
      bind_binding_env alp sigma id2 [pat1]
  | _, PatVar (Name id2) when is_onlybinding_pattern_like_meta false id2 metas ->
      bind_binding_env alp sigma id2 [pat1]
  | PatVar na1, PatVar na2 -> match_names metas acc na1 na2
  | _, PatVar Anonymous when allow_catchall -> acc
  | PatCstr (c1,patl1,na1), PatCstr (c2,patl2,na2)
      when eq_constructor c1 c2 && Int.equal (List.length patl1) (List.length patl2) ->
      List.fold_left2 (match_cases_pattern_binders false metas)
        (match_names metas acc na1 na2) patl1 patl2
  | _ -> raise No_match

let remove_sigma x (terms,termlists,binders,binderlists) =
  (Id.List.remove_assoc x terms,termlists,binders,binderlists)

let remove_bindinglist_sigma x (terms,termlists,binders,binderlists) =
  (terms,termlists,binders,Id.List.remove_assoc x binderlists)

let add_ldots_var metas = (ldots_var,((Constrexpr.InConstrEntrySomeLevel,(None,[])),NtnTypeConstr))::metas

let add_meta_bindinglist x metas = (x,((Constrexpr.InConstrEntrySomeLevel,(None,[])),NtnTypeBinderList))::metas

(* This tells if letins in the middle of binders should be included in
   the sequence of binders *)
let glue_inner_letin_with_decls = true

(* This tells if trailing letins (with no further proper binders)
   should be included in sequence of binders *)
let glue_trailing_letin_with_decls = false

exception OnlyTrailingLetIns

let match_binderlist match_fun alp metas sigma rest x y iter termin revert =
  let rec aux trailing_letins sigma bl rest =
    try
      let metas = add_ldots_var (add_meta_bindinglist y metas) in
      let (terms,_,_,binderlists as sigma) = match_fun alp metas sigma rest iter in
      let rest = Id.List.assoc ldots_var terms in
      let b =
        match Id.List.assoc y binderlists with [b] -> b | _ ->assert false
      in
      let sigma = remove_bindinglist_sigma y (remove_sigma ldots_var sigma) in
      (* In case y is bound not only to a binder but also to a term *)
      let sigma = remove_sigma y sigma in
      aux false sigma (b::bl) rest
    with No_match ->
    match DAst.get rest with
    | GLetIn (na,c,t,rest') when glue_inner_letin_with_decls ->
       let b = DAst.make ?loc:rest.CAst.loc @@ GLocalDef (na,Explicit (*?*), c,t) in
       (* collect let-in *)
       (try aux true sigma (b::bl) rest'
        with OnlyTrailingLetIns
             when not (trailing_letins && not glue_trailing_letin_with_decls) ->
         (* renounce to take into account trailing let-ins *)
         if not (List.is_empty bl) then bl, rest, sigma else raise No_match)
    | _ ->
       if trailing_letins && not glue_trailing_letin_with_decls then
         (* Backtrack to when we tried to glue letins *)
         raise OnlyTrailingLetIns;
       if not (List.is_empty bl) then bl, rest, sigma else raise No_match in
  let bl,rest,sigma = aux false sigma [] rest in
  let bl = if revert then List.rev bl else bl in
  let alp,sigma = bind_bindinglist_env alp sigma x bl in
  match_fun alp metas sigma rest termin

let add_meta_term x metas = (x,((Constrexpr.InConstrEntrySomeLevel,(None,[])),NtnTypeConstr))::metas (* Should reuse the scope of the partner of x! *)

let match_termlist match_fun alp metas sigma rest x y iter termin revert =
  let rec aux sigma acc rest =
    try
      let metas = add_ldots_var (add_meta_term y metas) in
      let (terms,_,_,_ as sigma) = match_fun metas sigma rest iter in
      let rest = Id.List.assoc ldots_var terms in
      let t = Id.List.assoc y terms in
      let sigma = remove_sigma y (remove_sigma ldots_var sigma) in
      aux sigma (t::acc) rest
    with No_match when not (List.is_empty acc) ->
      acc, match_fun metas sigma rest termin in
  let l,(terms,termlists,binders,binderlists as sigma) = aux sigma [] rest in
  let l = if revert then l else List.rev l in
  if is_bindinglist_meta x metas then
    (* This is a recursive pattern for both bindings and terms; it is *)
    (* registered for binders *)
    bind_bindinglist_as_termlist_env alp sigma x l
  else
    bind_termlist_env alp sigma x l

let match_cast match_fun sigma c1 c2 =
  match c1, c2 with
  | CastConv t1, CastConv t2
  | CastVM t1, CastVM t2
  | CastNative t1, CastNative t2 ->
    match_fun sigma t1 t2
  | CastCoerce, CastCoerce ->
    sigma
  | CastConv _, _
  | CastVM _, _
  | CastNative _, _
  | CastCoerce, _ -> raise No_match

let does_not_come_from_already_eta_expanded_var glob =
  (* This is hack to avoid looping on a rule with rhs of the form *)
  (* "?f (fun ?x => ?g)" since otherwise, matching "F H" expands in *)
  (* "F (fun x => H x)" and "H x" is recursively matched against the same *)
  (* rule, giving "H (fun x' => x x')" and so on. *)
  (* Ideally, we would need the type of the expression to know which of *)
  (* the arguments applied to it can be eta-expanded without looping. *)
  (* The following test is then an approximation of what can be done *)
  (* optimally (whether other looping situations can occur remains to be *)
  (* checked). *)
  match DAst.get glob with GVar _ -> false | _ -> true

let rec match_ inner u alp metas sigma a1 a2 =
  let open CAst in
  let loc = a1.loc in
  match DAst.get a1, a2 with
  (* Matching notation variable *)
  | r1, NVar id2 when is_term_meta id2 metas -> bind_term_env alp sigma id2 a1
  | GVar _, NVar id2 when is_onlybinding_pattern_like_meta true id2 metas -> bind_binding_as_term_env alp sigma id2 a1
  | r1, NVar id2 when is_onlybinding_pattern_like_meta false id2 metas -> bind_binding_as_term_env alp sigma id2 a1
  | GVar _, NVar id2 when is_onlybinding_strict_meta id2 metas -> raise No_match
  | GVar _, NVar id2 when is_onlybinding_meta id2 metas -> bind_binding_as_term_env alp sigma id2 a1
  | r1, NVar id2 when is_bindinglist_meta id2 metas -> bind_term_env alp sigma id2 a1

  (* Matching recursive notations for terms *)
  | r1, NList (x,y,iter,termin,revert) ->
      match_termlist (match_hd u alp) alp metas sigma a1 x y iter termin revert

  (* Matching recursive notations for binders: general case *)
  | _r, NBinderList (x,y,iter,termin,revert) ->
      match_binderlist (match_hd u) alp metas sigma a1 x y iter termin revert

  (* Matching compositionally *)
  | GVar id1, NVar id2 when alpha_var id1 id2 (fst alp) -> sigma
  | GRef (r1,_), NRef r2 when (GlobRef.equal r1 r2) -> sigma
  | GApp (f1,l1), NApp (f2,l2) ->
      let n1 = List.length l1 and n2 = List.length l2 in
      let f1,l1,f2,l2 =
	if n1 < n2 then
	  let l21,l22 = List.chop (n2-n1) l2 in f1,l1, NApp (f2,l21), l22
	else if n1 > n2 then
	  let l11,l12 = List.chop (n1-n2) l1 in DAst.make ?loc @@ GApp (f1,l11),l12, f2,l2
	else f1,l1, f2, l2 in
      let may_use_eta = does_not_come_from_already_eta_expanded_var f1 in
      List.fold_left2 (match_ may_use_eta u alp metas)
        (match_hd u alp metas sigma f1 f2) l1 l2
  | GLambda (na1,bk1,t1,b1), NLambda (na2,t2,b2) ->
     match_extended_binders false u alp metas na1 na2 bk1 t1 (match_in u alp metas sigma t1 t2) b1 b2
  | GProd (na1,bk1,t1,b1), NProd (na2,t2,b2) ->
     match_extended_binders true u alp metas na1 na2 bk1 t1 (match_in u alp metas sigma t1 t2) b1 b2
  | GLetIn (na1,b1,_,c1), NLetIn (na2,b2,None,c2)
  | GLetIn (na1,b1,None,c1), NLetIn (na2,b2,_,c2) ->
     match_binders u alp metas na1 na2 (match_in u alp metas sigma b1 b2) c1 c2
  | GLetIn (na1,b1,Some t1,c1), NLetIn (na2,b2,Some t2,c2) ->
     match_binders u alp metas na1 na2
       (match_in u alp metas (match_in u alp metas sigma b1 b2) t1 t2) c1 c2
  | GCases (sty1,rtno1,tml1,eqnl1), NCases (sty2,rtno2,tml2,eqnl2)
      when sty1 == sty2 && Int.equal (List.length tml1) (List.length tml2) ->
      let rtno1' = abstract_return_type_context_glob_constr tml1 rtno1 in
      let rtno2' = abstract_return_type_context_notation_constr tml2 rtno2 in
      let sigma =
	try Option.fold_left2 (match_in u alp metas) sigma rtno1' rtno2'
	with Option.Heterogeneous -> raise No_match
      in
      let sigma = List.fold_left2
      (fun s (tm1,_) (tm2,_) ->
        match_in u alp metas s tm1 tm2) sigma tml1 tml2 in
      (* Try two different strategies for matching clauses *)
      (try
        List.fold_left2_set No_match (match_equations u alp metas) sigma eqnl1 eqnl2
      with
        No_match ->
        List.fold_left2_set No_match (match_disjunctive_equations u alp metas) sigma
           (Detyping.factorize_eqns eqnl1)
           (List.map (fun (patl,rhs) -> ([patl],rhs)) eqnl2))
  | GLetTuple (nal1,(na1,to1),b1,c1), NLetTuple (nal2,(na2,to2),b2,c2)
      when Int.equal (List.length nal1) (List.length nal2) ->
      let sigma = match_opt (match_binders u alp metas na1 na2) sigma to1 to2 in
      let sigma = match_in u alp metas sigma b1 b2 in
      let (alp,sigma) =
	List.fold_left2 (match_names metas) (alp,sigma) nal1 nal2 in
      match_in u alp metas sigma c1 c2
  | GIf (a1,(na1,to1),b1,c1), NIf (a2,(na2,to2),b2,c2) ->
      let sigma = match_opt (match_binders u alp metas na1 na2) sigma to1 to2 in
      List.fold_left2 (match_in u alp metas) sigma [a1;b1;c1] [a2;b2;c2]
  | GRec (fk1,idl1,dll1,tl1,bl1), NRec (fk2,idl2,dll2,tl2,bl2)
      when match_fix_kind fk1 fk2 && Int.equal (Array.length idl1) (Array.length idl2) &&
	Array.for_all2 (fun l1 l2 -> Int.equal (List.length l1) (List.length l2)) dll1 dll2
	->
      let alp,sigma = Array.fold_left2
	(List.fold_left2 (fun (alp,sigma) (na1,_,oc1,b1) (na2,oc2,b2) ->
	  let sigma =
	    match_in u alp metas
              (match_opt (match_in u alp metas) sigma oc1 oc2) b1 b2
	  in match_names metas (alp,sigma) na1 na2)) (alp,sigma) dll1 dll2 in
      let sigma = Array.fold_left2 (match_in u alp metas) sigma tl1 tl2 in
      let alp,sigma = Array.fold_right2 (fun id1 id2 alsig ->
	match_names metas alsig (Name id1) (Name id2)) idl1 idl2 (alp,sigma) in
      Array.fold_left2 (match_in u alp metas) sigma bl1 bl2
  | GCast(t1, c1), NCast(t2, c2) ->
    match_cast (match_in u alp metas) (match_in u alp metas sigma t1 t2) c1 c2
  | GSort (GType _), NSort (GType _) when not u -> sigma
  | GSort s1, NSort s2 when glob_sort_eq s1 s2 -> sigma
  | GInt i1, NInt i2 when Uint63.equal i1 i2 -> sigma
  | GPatVar _, NHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, NHole _ -> sigma

  (* On the fly eta-expansion so as to use notations of the form
     "exists x, P x" for "ex P"; ensure at least one constructor is
     consumed to avoid looping; expects type not given because don't know
     otherwise how to ensure it corresponds to a well-typed eta-expansion;
     we make an exception for types which are metavariables: this is useful e.g.
     to print "{x:_ & P x}" knowing that notation "{x & P x}" is not defined. *)
  | _b1, NLambda (Name id as na,(NHole _ | NVar _ as t2),b2) when inner ->
      let avoid =
        Id.Set.union (free_glob_vars a1) (* as in Namegen: *) (glob_visible_short_qualid a1) in
      let id' = Namegen.next_ident_away id avoid in
      let t1 = DAst.make @@ GHole(Evar_kinds.BinderType (Name id'),IntroAnonymous,None) in
      let sigma = match t2 with
      | NHole _ -> sigma
      | NVar id2 -> bind_term_env alp sigma id2 t1
      | _ -> assert false in
      let (alp,sigma) =
        if is_bindinglist_meta id metas then
          bind_bindinglist_env alp sigma id [DAst.make @@ GLocalAssum (Name id',Explicit,t1)]
        else
          match_names metas (alp,sigma) (Name id') na in
      match_in u alp metas sigma (mkGApp a1 (DAst.make @@ GVar id')) b2

  | (GRef _ | GVar _ | GEvar _ | GPatVar _ | GApp _ | GLambda _ | GProd _
     | GLetIn _ | GCases _ | GLetTuple _ | GIf _ | GRec _ | GSort _ | GHole _
     | GCast _ | GInt _ ), _ -> raise No_match

and match_in u = match_ true u

and match_hd u = match_ false u

and match_binders u alp metas na1 na2 sigma b1 b2 =
  (* Match binders which cannot be substituted by a pattern *)
  let (alp,sigma) = match_names metas (alp,sigma) na1 na2 in
  match_in u alp metas sigma b1 b2

and match_extended_binders ?loc isprod u alp metas na1 na2 bk t sigma b1 b2 =
  (* Match binders which can be substituted by a pattern *)
  let store, get = set_temporary_memory () in
  match na1, DAst.get b1, na2 with
  (* Matching individual binders as part of a recursive pattern *)
  | Name p, GCases (Constr.LetPatternStyle,None,[(e,_)],(_::_ as eqns)), Name id
       when is_gvar p e && is_bindinglist_meta id metas && List.length (store (Detyping.factorize_eqns eqns)) = 1 ->
    (match get () with
     | [{CAst.v=(ids,disj_of_patl,b1)}] ->
     let disjpat = List.map (function [pat] -> pat | _ -> assert false) disj_of_patl in
     let disjpat = if occur_glob_constr p b1 then List.map (set_pat_alias p) disjpat else disjpat in
     let alp,sigma = bind_bindinglist_env alp sigma id [DAst.make ?loc @@ GLocalPattern ((disjpat,ids),p,bk,t)] in
     match_in u alp metas sigma b1 b2
     | _ -> assert false)
  | Name p, GCases (LetPatternStyle,None,[(e,_)],(_::_ as eqns)), Name id
       when is_gvar p e && is_onlybinding_pattern_like_meta false id metas && List.length (store (Detyping.factorize_eqns eqns)) = 1 ->
    (match get () with
     | [{CAst.v=(ids,disj_of_patl,b1)}] ->
     let disjpat = List.map (function [pat] -> pat | _ -> assert false) disj_of_patl in
     let disjpat = if occur_glob_constr p b1 then List.map (set_pat_alias p) disjpat else disjpat in
     let alp,sigma = bind_binding_env alp sigma id disjpat in
     match_in u alp metas sigma b1 b2
     | _ -> assert false)
  | _, _, Name id when is_bindinglist_meta id metas && (not isprod || na1 != Anonymous)->
      let alp,sigma = bind_bindinglist_env alp sigma id [DAst.make ?loc @@ GLocalAssum (na1,bk,t)] in
      match_in u alp metas sigma b1 b2
  | _, _, _ ->
     let (alp,sigma) = match_names metas (alp,sigma) na1 na2 in
     match_in u alp metas sigma b1 b2

and match_equations u alp metas sigma {CAst.v=(ids,patl1,rhs1)} (patl2,rhs2) rest1 rest2 =
  (* patl1 and patl2 have the same length because they respectively
     correspond to some tml1 and tml2 that have the same length *)
  let allow_catchall = (rest2 = [] && ids = []) in
  let (alp,sigma) =
    List.fold_left2 (match_cases_pattern_binders allow_catchall metas)
      (alp,sigma) patl1 patl2 in
  match_in u alp metas sigma rhs1 rhs2

and match_disjunctive_equations u alp metas sigma {CAst.v=(ids,disjpatl1,rhs1)} (disjpatl2,rhs2) _ _ =
  (* patl1 and patl2 have the same length because they respectively
     correspond to some tml1 and tml2 that have the same length *)
  let (alp,sigma) =
    List.fold_left2_set No_match
      (fun alp_sigma patl1 patl2 _ _ ->
        List.fold_left2 (match_cases_pattern_binders false metas) alp_sigma patl1 patl2)
      (alp,sigma) disjpatl1 disjpatl2 in
  match_in u alp metas sigma rhs1 rhs2

let match_notation_constr u c (metas,pat) =
  let terms,termlists,binders,binderlists =
    match_ false u ([],[]) metas ([],[],[],[]) c pat in
  (* Turning substitution based on binding/constr distinction into a
     substitution based on entry productions *)
  List.fold_right (fun (x,(scl,typ)) (terms',termlists',binders',binderlists') ->
    match typ with
    | NtnTypeConstr ->
      let term = try Id.List.assoc x terms with Not_found -> raise No_match in
       ((term, scl)::terms',termlists',binders',binderlists')
    | NtnTypeBinder (NtnBinderParsedAsConstr _) ->
       (match Id.List.assoc x binders with
        | [pat] ->
          let v = glob_constr_of_cases_pattern pat in
          ((v,scl)::terms',termlists',binders',binderlists')
        | _ -> raise No_match)
    | NtnTypeBinder (NtnParsedAsIdent | NtnParsedAsPattern _) ->
       (terms',termlists',(Id.List.assoc x binders,scl)::binders',binderlists')
    | NtnTypeConstrList ->
       (terms',(Id.List.assoc x termlists,scl)::termlists',binders',binderlists')
    | NtnTypeBinderList ->
      let bl = try Id.List.assoc x binderlists with Not_found -> raise No_match in
       (terms',termlists',binders',(bl, scl)::binderlists'))
    metas ([],[],[],[])

(* Matching cases pattern *)

let bind_env_cases_pattern (terms,x,termlists,y as sigma) var v =
  try
    let vvar = Id.List.assoc var terms in
    if cases_pattern_eq v vvar then sigma else raise No_match
  with Not_found ->
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::terms,x,termlists,y

let match_cases_pattern_list match_fun metas sigma rest x y iter termin revert =
  let rec aux sigma acc rest =
    try
      let metas = add_ldots_var (add_meta_term y metas) in
      let (terms,_,_,_ as sigma) = match_fun metas sigma rest iter in
      let rest = Id.List.assoc ldots_var terms in
      let t = Id.List.assoc y terms in
      let sigma = remove_sigma y (remove_sigma ldots_var sigma) in
      aux sigma (t::acc) rest
    with No_match when not (List.is_empty acc) ->
      acc, match_fun metas sigma rest termin in
  let l,(terms,termlists,binders,binderlists as sigma) = aux sigma [] rest in
  (terms,(x,if revert then l else List.rev l)::termlists,binders,binderlists)

let rec match_cases_pattern metas (terms,termlists,(),() as sigma) a1 a2 =
 match DAst.get a1, a2 with
  | r1, NVar id2 when Id.List.mem_assoc id2 metas -> (bind_env_cases_pattern sigma id2 a1),(0,[])
  | PatVar Anonymous, NHole _ -> sigma,(0,[])
  | PatCstr ((ind,_ as r1),largs,Anonymous), NRef (ConstructRef r2) when eq_constructor r1 r2 ->
      let l = try add_patterns_for_params_remove_local_defs r1 largs with Not_found -> raise No_match in
      sigma,(0,l)
  | PatCstr ((ind,_ as r1),args1,Anonymous), NApp (NRef (ConstructRef r2),l2)
      when eq_constructor r1 r2 ->
      let l1 = try add_patterns_for_params_remove_local_defs r1 args1 with Not_found -> raise No_match in
      let le2 = List.length l2 in
      if Int.equal le2 0 (* Special case of a notation for a @Cstr *) || le2 > List.length l1
      then
	raise No_match
      else
	let l1',more_args = Util.List.chop le2 l1 in
        (List.fold_left2 (match_cases_pattern_no_more_args metas) sigma l1' l2),(le2,more_args)
  | r1, NList (x,y,iter,termin,revert) ->
      (match_cases_pattern_list (match_cases_pattern_no_more_args)
        metas (terms,termlists,(),()) a1 x y iter termin revert),(0,[])
  | _ -> raise No_match

and match_cases_pattern_no_more_args metas sigma a1 a2 =
    match match_cases_pattern metas sigma a1 a2 with
      | out,(_,[]) -> out
      | _ -> raise No_match

let match_ind_pattern metas sigma ind pats a2 =
  match a2 with
  | NRef (IndRef r2) when eq_ind ind r2 ->
      sigma,(0,pats)
  | NApp (NRef (IndRef r2),l2)
      when eq_ind ind r2 ->
      let le2 = List.length l2 in
      if Int.equal le2 0 (* Special case of a notation for a @Cstr *) || le2 > List.length pats
      then
	raise No_match
      else
	let l1',more_args = Util.List.chop le2 pats in
	(List.fold_left2 (match_cases_pattern_no_more_args metas) sigma l1' l2),(le2,more_args)
  |_ -> raise No_match

let reorder_canonically_substitution terms termlists metas =
  List.fold_right (fun (x,(scl,typ)) (terms',termlists') ->
    match typ with
      | NtnTypeConstr -> ((Id.List.assoc x terms, scl)::terms',termlists')
      | NtnTypeBinder _ -> assert false
      | NtnTypeConstrList -> (terms',(Id.List.assoc x termlists,scl)::termlists')
      | NtnTypeBinderList -> assert false)
    metas ([],[])

let match_notation_constr_cases_pattern c (metas,pat) =
  let (terms,termlists,(),()),more_args = match_cases_pattern metas ([],[],(),()) c pat in
  reorder_canonically_substitution terms termlists metas, more_args

let match_notation_constr_ind_pattern ind args (metas,pat) =
  let (terms,termlists,(),()),more_args = match_ind_pattern metas ([],[],(),()) ind args pat in
  reorder_canonically_substitution terms termlists metas, more_args
