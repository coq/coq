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
open CErrors
open Util
open Names
open Nameops
open Constr
open Globnames
open Glob_term
open Glob_ops
open Mod_subst
open Notation_term

(** Constr default entry *)

let constr_lowest_level =
  Constrexpr.{notation_entry = InConstrEntry; notation_level = 0}

let constr_some_level =
  Constrexpr.{notation_subentry = InConstrEntry; notation_relative_level = LevelSome; notation_position = None}

(**********************************************************************)
(* Utilities                                                          *)

let ldots_var = Id.of_string ".."

type alpha_conversion_map = {
  (* the actual binding variables accumulated; e.g. when matching "fun x => t"
     with "fun '(y,z) => t'", we accumulate y and z; used for avoiding collisions
     with global names *)
  actualvars : Id.Set.t;
  (* the matching between binders of the pattern unbound in the
     notation and actual binders of the term to match; e.g. when
     matching term "fun y => t" against pattern "fun x => u" where "x"
     is not a notation variable, we bind "y" to "x" and compare t and
     u up to this renaming (note that in this case, "x" is not bound
     to a notation variable and thus will not occur in any instance of
     a notation variable in "t"). *)
  staticbinders : (Name.t * Id.t) list;
  (* the renaming to do between binder variables bound several times; e.g. if
     "fun x => t" has to match pattern "fun y => u" and, either "fun z => v"
     is already known to match pattern "fun y => w" (for the same
     binder variable "y"), or "y" already occurs also as a term bound,
     say, to the variable "z", then, when matching "fun x => t"
     against "fun y => u", "t" is matched against "u" with the
     constraint that any "x" in "t" has to be renamed into "z" (and in
     particular any subterm bound by the notation and mentioning "x"
     must be renamed so as to use "z" instead). *)
  renaming : (Id.t * Id.t) list;
}

(* Check if [id1], in the actual term, matches [id2], in the pattern,
   up to the static alpha-renaming obtained by matching the context of
   the pattern with the actual names of the term *)
let rec alpha_var id1 id2 = function
  | (Name i1,i2)::_ when Id.equal i1 id1 -> Id.equal i2 id2
  | (i1,i2)::_ when Id.equal i2 id2 -> Name.equal i1 (Name id1)
  | _::idl -> alpha_var id1 id2 idl
  | [] -> Id.equal id1 id2

(* used to update the notation variable with the local variables used
   in NList and NBinderList, since the iterator has its own variable *)
let replace_var i j var = j :: List.remove Id.equal i var

let eq_rigid a b =
  let open UState in
  match a, b with
  | UnivRigid, UnivRigid -> true
  | UnivFlexible a, UnivFlexible b -> (a:bool) = b
  | (UnivRigid | UnivFlexible _), _ -> false

(* compare_glob_universe_instances true strictly_lt us1 us2 computes us1 <= us2,
   compare_glob_universe_instances false strictly_lt us1 us2 computes us1 = us2.
   strictly_lt will be set to true if any part is strictly less. *)
let compare_glob_universe_instances lt strictly_lt us1 us2 =
  match us1, us2 with
  | None, None -> true
  | Some _, None -> strictly_lt := true; lt
  | None, Some _ -> false
  | Some (ql1,ul1), Some (ql2,ul2) ->
    let is_anon = function
      | GQualVar (GLocalQVar {v=Anonymous}) -> true
      | _ -> false
    in
    CList.for_all2eq (fun q1 q2 ->
        match is_anon q1, is_anon q2 with
        | true, true -> true
        | false, true -> strictly_lt := true; lt
        | true, false -> false
        | false, false -> glob_quality_eq q1 q2)
      ql1 ql2
    && CList.for_all2eq (fun u1 u2 ->
         match u1, u2 with
         | UAnonymous {rigid}, UAnonymous {rigid=rigid'} -> eq_rigid rigid rigid'
         | UNamed _, UAnonymous _ -> strictly_lt := true; lt
         | UAnonymous _, UNamed _ -> false
         | UNamed _, UNamed _ -> glob_level_eq u1 u2) ul1 ul2

(* Compute us1 <= us2, as a boolean *)
let compare_glob_universe_instances_le us1 us2 =
  compare_glob_universe_instances true (ref false) us1 us2

(* When [lt] is [true], tell if [t1] is a strict refinement of [t2]
   (this is a partial order, so returning [false] does not mean that
   [t2] is finer than [t1]); when [lt] is false, tell if [t1] is the
   same pattern as [t2] *)

let compare_notation_constr lt var_eq_hole (vars1,vars2) t1 t2 =
  (* this is used to reason up to order of notation variables *)
  let alphameta = ref [] in
  (* this becomes true when at least one subterm is detected as strictly smaller *)
  let strictly_lt = ref false in
  (* this is the stack of inner of iter patterns for comparison with a
     new iteration or the tail of a recursive pattern *)
  let tail = ref [] in
  let check_alphameta id1 id2 =
    try if not (Id.equal (List.assoc id1 !alphameta) id2) then raise_notrace Exit
    with Not_found ->
      if (List.mem_assoc id1 !alphameta) then raise_notrace Exit;
      alphameta := (id1,id2) :: !alphameta in
  let check_eq_id (vars1,vars2) renaming id1 id2 =
    let ismeta1 = List.mem_f Id.equal id1 vars1 in
    let ismeta2 = List.mem_f Id.equal id2 vars2 in
    match ismeta1, ismeta2 with
    | true, true -> check_alphameta id1 id2
    | false, false -> if not (alpha_var id1 id2 renaming) then raise_notrace Exit
    | false, true ->
      if not lt then raise_notrace Exit
      else
        (* a binder which is not bound in the notation can be
           considered as strictly more precise since it prevents the
           notation variables in its scope to be bound by this binder;
           i.e. it is strictly more precise in the sense that it
           covers strictly less patterns than a notation where the
           same binder is bound in the notation; this is hawever
           disputable *)
        strictly_lt := true
    | true, false -> if not lt then raise_notrace Exit in
  let check_eq_name vars renaming na1 na2 =
    match na1, na2 with
    | Name id1, Name id2 -> check_eq_id vars renaming id1 id2; (Name id1,id2)::renaming
    | Anonymous, Anonymous -> renaming
    | Anonymous, Name _ when lt -> renaming
    | _ -> raise_notrace Exit in
  let rec aux (vars1,vars2 as vars) renaming t1 t2 = match t1, t2 with
  | NVar id1, NVar id2 when id1 = ldots_var && id2 = ldots_var -> ()
  | _, NVar id2 when lt && id2 = ldots_var -> tail := t1 :: !tail
  | NVar id1, _ when lt && id1 = ldots_var -> tail := t2 :: !tail
  | NVar id1, NVar id2 -> check_eq_id vars renaming id1 id2
  | NHole _, NVar id2 when lt && List.mem_f Id.equal id2 vars2 -> ()
  | NVar id1, NHole _ when lt && List.mem_f Id.equal id1 vars1 -> ()
  | _, NVar id2 when lt && List.mem_f Id.equal id2 vars2 -> strictly_lt := true
  | NRef (gr1,u1), NRef (gr2,u2) when GlobRef.CanOrd.equal gr1 gr2 && compare_glob_universe_instances lt strictly_lt u1 u2 -> ()
  | NHole _, NHole _ -> () (* FIXME? *)
  | _, NHole _ when lt -> strictly_lt := true
  | NGenarg _, NGenarg _ -> () (* FIXME? *)
  | NList (i1, j1, iter1, tail1, b1), NList (i2, j2, iter2, tail2, b2)
  | NBinderList (i1, j1, iter1, tail1, b1), NBinderList (i2, j2, iter2, tail2, b2) ->
    if b1 <> b2 then raise_notrace Exit;
    let vars1 = replace_var i1 j1 vars1 in
    let vars2 = replace_var i2 j2 vars2 in
    check_alphameta i1 i2; aux (vars1,vars2) renaming iter1 iter2; aux vars renaming tail1 tail2;
  | NBinderList (i1, j1, iter1, tail1, b1), NList (i2, j2, iter2, tail2, b2)
  | NList (i1, j1, iter1, tail1, b1), NBinderList (i2, j2, iter2, tail2, b2) ->
    (* They may overlap on a unique iteration of them *)
    let vars1 = replace_var i1 j1 vars1 in
    let vars2 = replace_var i2 j2 vars2 in
    aux (vars1,vars2) renaming iter1 iter2;
    aux vars renaming tail1 tail2
  | t1, NList (i2, j2, iter2, tail2, b2)
  | t1, NBinderList (i2, j2, iter2, tail2, b2) when lt ->
    (* checking if t1 is a finite iteration of the pattern *)
    let vars2 = replace_var i2 j2 vars2 in
    aux (vars1,vars2) renaming t1 iter2;
    let t1 = List.hd !tail in
    tail := List.tl !tail;
    (* either matching a new iteration, or matching the tail *)
    (try aux vars renaming t1 tail2 with Exit -> aux vars renaming t1 t2)
  | NList (i1, j1, iter1, tail1, b1), t2
  | NBinderList (i1, j1, iter1, tail1, b1), t2 when lt ->
    (* we see the NList as a single iteration *)
    let vars1 = replace_var i1 j1 vars1 in
    aux (vars1,vars2) renaming iter1 t2;
    let t2 = match !tail with
      | t::rest -> tail := rest; t
      | _ -> (* ".." is in a discarded fine-grained position *) raise_notrace Exit in
    (* it had to be a single iteration of iter1 *)
    aux vars renaming tail1 t2
  | NApp (t1, a1), NApp (t2, a2) -> aux vars renaming t1 t2; List.iter2 (aux vars renaming) a1 a2
  | NProj ((cst1,u1), l1, a1), NProj ((cst2,u2), l2, a2)
    when GlobRef.CanOrd.equal (GlobRef.ConstRef cst1) (GlobRef.ConstRef cst2) && compare_glob_universe_instances lt strictly_lt u1 u2 ->
    List.iter2 (aux vars renaming) l1 l2; aux vars renaming a1 a2
  | NLambda (na1, t1, u1), NLambda (na2, t2, u2)
  | NProd (na1, t1, u1), NProd (na2, t2, u2) ->
    (match t1, t2 with
     | None, None -> ()
     | Some _, None -> if lt then strictly_lt := true
     | Some t1, Some t2 -> aux vars renaming t1 t2
     | None, Some _ -> raise_notrace Exit);
    let renaming = check_eq_name vars renaming na1 na2 in
    aux vars renaming u1 u2
  | NLetIn (na1, b1, t1, u1), NLetIn (na2, b2, t2, u2) ->
    aux vars renaming b1 b2;
    Option.iter2 (aux vars renaming) t1 t2;(* TODO : subtyping? *)
    let renaming = check_eq_name vars renaming na1 na2 in
    aux vars renaming u1 u2
  | NCases (_, o1, r1, p1), NCases (_, o2, r2, p2) -> (* FIXME? *)
    let check_pat (p1, t1) (p2, t2) =
      if not (List.equal cases_pattern_eq p1 p2) then raise_notrace Exit; (* TODO: subtyping and renaming *)
      aux vars renaming t1 t2
    in
    let eqf renaming (t1, (na1, o1)) (t2, (na2, o2)) =
      aux vars renaming t1 t2;
      let renaming = check_eq_name vars renaming na1 na2 in
      let eq renaming (i1, n1) (i2, n2) =
        if not (Ind.CanOrd.equal i1 i2) then raise_notrace Exit;
        List.fold_left2 (check_eq_name vars) renaming n1 n2 in
        Option.fold_left2 eq renaming o1 o2 in
    let renaming = List.fold_left2 eqf renaming r1 r2 in
    Option.iter2 (aux vars renaming) o1 o2;
    List.iter2 check_pat p1 p2
  | NLetTuple (nas1, (na1, o1), t1, u1), NLetTuple (nas2, (na2, o2), t2, u2) ->
    aux vars renaming t1 t2;
    let renaming = check_eq_name vars renaming na1 na2 in
    Option.iter2 (aux vars renaming) o1 o2;
    let renaming' = List.fold_left2 (check_eq_name vars) renaming nas1 nas2 in
    aux vars renaming' u1 u2
  | NIf (t1, (na1, o1), u1, r1), NIf (t2, (na2, o2), u2, r2) ->
    aux vars renaming t1 t2;
    aux vars renaming u1 u2;
    aux vars renaming r1 r2;
    let renaming = check_eq_name vars renaming na1 na2 in
    Option.iter2 (aux vars renaming) o1 o2
  | NRec (_, ids1, ts1, us1, rs1), NRec (_, ids2, ts2, us2, rs2) -> (* FIXME? *)
    let eq renaming (na1, o1, t1) (na2, o2, t2) =
      Option.iter2 (aux vars renaming) o1 o2;
      aux vars renaming t1 t2;
      check_eq_name vars renaming na1 na2
    in
    let renaming = Array.fold_left2 (fun r id1 id2 -> check_eq_id vars r id1 id2; (Name id1,id2)::r) renaming ids1 ids2 in
    let renamings = Array.map2 (List.fold_left2 eq renaming) ts1 ts2 in
    Array.iter3 (aux vars) renamings us1 us2;
    Array.iter3 (aux vars) (Array.map ((@) renaming) renamings) rs1 rs2
  | NSort s1, NSort s2 when glob_sort_eq s1 s2 -> ()
  | NCast (c1, k1, t1), NCast (c2, k2, t2) ->
    aux vars renaming c1 c2;
    if not (Option.equal cast_kind_eq k1 k2) then raise_notrace Exit;
    aux vars renaming t1 t2
  | NInt i1, NInt i2 when Uint63.equal i1 i2 -> ()
  | NFloat f1, NFloat f2 when Float64.equal f1 f2 -> ()
  | NArray(t1,def1,ty1), NArray(t2,def2,ty2) ->
    Array.iter2 (aux vars renaming) t1 t2;
    aux vars renaming def1 def2;
    aux vars renaming ty1 ty2
  | (NRef _ | NVar _ | NApp _ | NProj _ | NHole _ | NGenarg _ | NList _ | NLambda _ | NProd _
    | NBinderList _ | NLetIn _ | NCases _ | NLetTuple _ | NIf _
    | NRec _ | NSort _ | NCast _ | NInt _ | NFloat _ | NString _ | NArray _), _ -> raise_notrace Exit in
  try
    let _ = aux (vars1,vars2) [] t1 t2 in
    if not lt then
      (* Check that order of notation metavariables does not matter *)
      List.iter2 check_alphameta vars1 vars2;
    not lt || var_eq_hole || !strictly_lt
  with Exit | (* Option.iter2: *) Option.Heterogeneous | Invalid_argument _ -> false

let eq_notation_constr vars t1 t2 = t1 == t2 || compare_notation_constr false false vars t1 t2

(* "strictly finer" is the order generated by constructed-node <= var/hole *)
let strictly_finer_notation_constr vars t1 t2 = compare_notation_constr true false vars t1 t2

(* "finer" is the order also including var = hole and hole = var *)
let finer_notation_constr vars t1 t2 = compare_notation_constr true true vars t1 t2

let adjust_application c1 c2 =
  match c1, c2 with
  | NApp (t1, a1), (NList (_,_,NApp (_, a2),_,_) | NBinderList (_,_,NApp (_, a2),_,_) | NApp (_, a2)) when List.length a1 >= List.length a2 ->
      NApp (t1, List.firstn (List.length a2) a1)
  | NApp (t1, a1), _ ->
      t1
  | _ -> c1

let strictly_finer_interpretation_than (vars1,c1) (vars2,c2) =
  let c1 = adjust_application c1 c2 in
  strictly_finer_notation_constr (List.map fst vars1, List.map fst vars2) c1 c2

let finer_interpretation_than (vars1,c1) (vars2,c2) =
  let c1 = adjust_application c1 c2 in
  finer_notation_constr (List.map fst vars1, List.map fst vars2) c1 c2

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
  | GBinderType (Name id) ->
     let id =
       try match DAst.get (Id.List.assoc id l) with GVar id' -> id' | _ -> id
       with Not_found -> id in
     GBinderType (Name id)
  | e -> e

let rec subst_glob_vars l gc = DAst.map (function
  | GVar id as r -> (try DAst.get (Id.List.assoc id l) with Not_found -> r)
  | GHole x -> GHole (subst_binder_type_vars l x)
  | _ ->
    let g =
      Name.map (fun id ->
          try match DAst.get (Id.List.assoc id l) with GVar id' -> id' | _ -> id
          with Not_found -> id) in
    DAst.get (map_glob_constr_left_to_right_with_names (subst_glob_vars l) g gc) (* assume: id is not binding *)
  ) gc

type 'a binder_status_fun = {
  no : 'a -> 'a;
  restart_prod : 'a -> 'a;
  restart_lambda : 'a -> 'a;
  switch_prod : 'a -> 'a;
  switch_lambda : 'a -> 'a;
  slide : 'a -> 'a;
}

let default_binder_status_fun = {
  no = (fun x -> x);
  restart_prod = (fun x -> x);
  restart_lambda = (fun x -> x);
  switch_prod = (fun x -> x);
  switch_lambda = (fun x -> x);
  slide = (fun x -> x);
}

let test_implicit_argument_mark bk =
  if not (Glob_ops.binding_kind_eq bk Explicit) then
    user_err (Pp.str "Unexpected implicit argument mark.")

let test_pattern_cast = function
  | None -> ()
  | Some t -> user_err ?loc:t.CAst.loc (Pp.str "Unsupported pattern cast.")

let protect g e na =
  let e',disjpat,na,bk,t = g e na None in
  if disjpat <> None then user_err (Pp.str "Unsupported substitution of an arbitrary pattern.");
  test_implicit_argument_mark bk;
  test_pattern_cast t;
  e',na

let set_anonymous_type na = function
  | None -> DAst.make @@ GHole (GBinderType na)
  | Some t -> t

let apply_cases_pattern_term ?loc (ids,disjpat) tm c =
  let eqns = List.map (fun pat -> (CAst.make ?loc (ids,[pat],c))) disjpat in
  DAst.make ?loc @@ GCases (Constr.LetPatternStyle, None, [tm,(Anonymous,None)], eqns)

let apply_cases_pattern ?loc (ids_disjpat,id) c =
  apply_cases_pattern_term ?loc ids_disjpat (DAst.make ?loc (GVar id)) c

let glob_constr_of_notation_constr_with_binders ?loc g f ?(h=default_binder_status_fun) e nc =
  let lt x = DAst.make ?loc x in lt @@ match nc with
  | NVar id -> GVar id
  | NApp (a,args) -> let e = h.no e in DAst.get (mkGApp (f e a) (List.map (f e) args))
  | NProj (p,args,c) -> let e = h.no e in GProj (p, List.map (f e) args, f e c)
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
      let e = h.switch_lambda e in
      let ty = Option.map (f (h.restart_prod e)) ty in
      let e',disjpat,na',bk,ty = g e na ty in
      GLambda (na',None,bk,set_anonymous_type na ty,Option.fold_right (apply_cases_pattern ?loc) disjpat (f e' c))
  | NProd (na,ty,c) ->
      let e = h.switch_prod e in
      let ty = Option.map (f (h.restart_prod e)) ty in
      let e',disjpat,na',bk,ty = g e na ty in
      GProd (na',None,bk,set_anonymous_type na ty,Option.fold_right (apply_cases_pattern ?loc) disjpat (f e' c))
  | NLetIn (na,b,t,c) ->
      let t = Option.map (f (h.restart_prod e)) t in
      let e',disjpat,na,bk,t = g e na t in
      test_implicit_argument_mark bk;
      (match disjpat with
       | None -> GLetIn (na,None, f (h.restart_lambda e) b,t,f e' c)
       | Some (disjpat,_id) -> test_pattern_cast t; DAst.get (apply_cases_pattern_term ?loc disjpat (f e b) (f e' c)))
  | NCases (sty,rtntypopt,tml,eqnl) ->
      let e = h.no e in
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
      let fold (idl,e) na =
        let (e,disjpat,na,bk,t) = g e na None in
        test_implicit_argument_mark bk;
        test_pattern_cast t;
        ((Name.cons na idl,e),disjpat,na) in
      let eqnl' = List.map (fun (patl,rhs) ->
        let ((idl,e),patl) =
          List.fold_left_map (cases_pattern_fold_map ?loc fold) ([],e) patl in
        let disjpatl = product_of_cases_patterns patl in
        List.map (fun patl -> CAst.make (idl,patl,f e rhs)) disjpatl) eqnl in
      GCases (sty,Option.map (f e') rtntypopt,tml',List.flatten eqnl')
  | NLetTuple (nal,(na,po),b,c) ->
      let e = h.no e in
      let e',nal = List.fold_left_map (protect g) e nal in
      let e'',na = protect g e na in
      GLetTuple (nal,(na,Option.map (f e'') po),f e b,f e' c)
  | NIf (c,(na,po),b1,b2) ->
      let e = h.no e in
      let e',na = protect g e na in
      GIf (f e c,(na,Option.map (f e') po),f e b1,f e b2)
  | NRec (fk,idl,dll,tl,bl) ->
      let e = h.no e in
      let e,dll = Array.fold_left_map (List.fold_left_map (fun e (na,oc,b) ->
          let e,na = protect g e na in
          (e,(na,None,Explicit,Option.map (f e) oc,f e b)))) e dll in
      let e',idl = Array.fold_left_map (to_id (protect g)) e idl in
      GRec (fk,idl,dll,Array.map (f e) tl,Array.map (f e') bl)
  | NCast (c,k,t) -> GCast (f e c, k, f (h.slide e) t)
  | NSort x -> GSort x
  | NHole x  -> GHole x
  | NGenarg arg -> GGenarg arg
  | NRef (x,u) -> GRef (x,u)
  | NInt i -> GInt i
  | NFloat f -> GFloat f
  | NString s -> GString s
  | NArray (t,def,ty) -> GArray(None, Array.map (f e) t, f e def, f e ty)

let glob_constr_of_notation_constr ?loc x =
  let rec aux () x =
    glob_constr_of_notation_constr_with_binders ?loc (fun () id t -> ((),None,id,Explicit,t)) aux () x
  in aux () x

let pr_notation_info prglob ntn c =
  str (String.quote_coq_string ntn) ++ str " :=" ++ brk (1,2) ++
  prglob (glob_constr_of_notation_constr c)

(******************************************************************************)
(* Translating a glob_constr into a notation, interpreting recursive patterns *)

let print_parentheses = ref false

type found_variables = {
    vars : Id.t list;
    recursive_term_vars : (Id.t * Id.t) list;
    recursive_binders_vars : (Id.t * Id.t) list;
  }

let add_id r id = r := { !r with vars = id :: (!r).vars }
let add_name r = function Anonymous -> () | Name id -> add_id r id

let mkNApp1 (g,a) =
  match g with
  (* Ensure flattening of nested applicative nodes *)
  | NApp (g,args') -> NApp (g,args'@[a])
  | _ -> NApp (g,[a])

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

let check_is_hole id = function
  | None -> ()
  | Some t -> match DAst.get t with GHole _ -> () | _ ->
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

let mem_recursive_pair (x,y) l = List.mem_f (eq_pair Id.equal Id.equal) (x,y) l

type recursive_pattern_kind =
| RecursiveTerms of bool (* in reverse order *)
| RecursiveBinders of bool (* in reverse order *)

let compare_recursive_parts recvars found f f' (iterator,subc) =
  let diff = ref None in
  let terminator = ref None in
  let treat_binder ?loc x y t_x t_y =
    match x, y with
    | Name x, Name y when mem_recursive_pair (x,y) recvars || mem_recursive_pair (y,x) recvars ->
      (* We found a binding position where it differs *)
      check_is_hole x t_x;
      check_is_hole y t_y;
      let revert = mem_recursive_pair (y,x) recvars in
      let x,y = if revert then y,x else x,y in
      begin match !diff with
      | None -> diff := Some (x, y, RecursiveBinders revert)
      | Some (x', y', RecursiveBinders revert') ->
        check_pair_matching ?loc x y x' y' revert revert'
      | Some (x', y', RecursiveTerms revert') ->
        (* Recursive binders have precedence: they can be coerced to
           terms but not reciprocally *)
        check_pair_matching ?loc x y x' y' revert revert';
        diff := Some (x, y, RecursiveBinders revert)
      end;
      true
    | _ -> Name.equal x y
  in
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
    | _ -> mk_glob_constr_eq aux (treat_binder ?loc:c1.CAst.loc) c1 c2
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
  | _ ->
      mk_glob_constr_eq aux (treat_binder ?loc:c1.CAst.loc) c1 c2 in
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
                               recursive_term_vars = List.add_set (eq_pair Id.equal Id.equal) (x,y) (!found).recursive_term_vars };
        NList (x,y,iterator,f (Option.get !terminator),revert)
    | Some (x,y,RecursiveBinders revert) ->
        let iterator =
          f' (if revert then iterator else subst_glob_vars [x, DAst.make @@ GVar y] iterator) in
        (* found have been collected by compare_constr *)
        found := { !found with vars = List.remove Id.equal y (!found).vars;
                               recursive_binders_vars = List.add_set (eq_pair Id.equal Id.equal) (x,y) (!found).recursive_binders_vars };
        NBinderList (x,y,iterator,f (Option.get !terminator),revert)
  else
    raise Not_found

let notation_constr_and_vars_of_glob_constr recvars a =
  let found = ref { vars = []; recursive_term_vars = []; recursive_binders_vars = [] } in
  let forgetful = ref { forget_ltac = false; forget_volatile_cast = false } in
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
  | GApp (g,[]) -> NApp (aux g,[]) (* Encoding @foo *)
  | GApp (g,args) ->
     (* Treat applicative notes as binary nodes *)
     let a,args = List.sep_last args in mkNApp1 (aux (DAst.make (GApp (g, args))), aux a)
  | GProj (p,args,c) -> NProj (p, List.map aux args, aux c)
  | GLambda (na,_,bk,ty,c) -> add_name found na; NLambda (na,aux_type ty,aux c)
  | GProd (na,_,bk,ty,c) -> add_name found na; NProd (na,aux_type ty,aux c)
  | GLetIn (na,_,b,t,c) -> add_name found na; NLetIn (na,aux b,Option.map aux t, aux c)
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
      let dll = Array.map (List.map (fun (na,_,bk,oc,b) ->
         if bk != Explicit then
           user_err Pp.(str "Binders marked as implicit not allowed in notations.");
         add_name found na; (na,Option.map aux oc,aux b))) dll in
      NRec (fk,idl,dll,Array.map aux tl,Array.map aux bl)
  | GCast (c,k,t) ->
    if Option.is_empty k then forgetful := { !forgetful with forget_volatile_cast = true };
    NCast (aux c, k, aux t)
  | GSort s -> NSort s
  | GInt i -> NInt i
  | GFloat f -> NFloat f
  | GString s -> NString s
  | GHole w -> NHole w
  | GGenarg arg -> forgetful := { !forgetful with forget_ltac = true }; NGenarg arg
  | GRef (r,u) -> NRef (r,u)
  | GArray (_u,t,def,ty) -> NArray (Array.map aux t, aux def, aux ty)
  | GEvar _ | GPatVar _ ->
      user_err Pp.(str "Existential variables not allowed in notations.")
  ) x
  and aux_type t = DAst.with_val (function
  | GHole (GBinderType _) -> None
  | _ -> Some (aux t)) t
  in
  let t = aux a in
  (* Side effect *)
  t, !found, !forgetful

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
    | NtnInternTypeAny _ ->
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

let[@warning "+9"] is_forgetful { forget_ltac; forget_volatile_cast } =
  forget_ltac || forget_volatile_cast

let notation_constr_of_glob_constr nenv a =
  let recvars = Id.Map.bindings nenv.ninterp_rec_vars in
  let a, found, forgetful = notation_constr_and_vars_of_glob_constr recvars a in
  let injective = check_variables_and_reversibility nenv found in
  let status = if is_forgetful forgetful then Forgetful forgetful
    else match injective with
  | [] -> APrioriReversible
  | l -> NonInjective l in
  a, status

(**********************************************************************)
(* Substitution of kernel names, avoiding a list of bound identifiers *)

let notation_constr_of_constr avoid t =
  let t = EConstr.of_constr t in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let t = Detyping.detype Detyping.Now ~avoid env evd t in
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
  | NRef (ref,u) ->
      let ref',t = subst_global subst ref in
      if ref' == ref then raw else (match t with
          | None -> NRef (ref',u)
          | Some t ->
            fst (notation_constr_of_constr bound t.UVars.univ_abstracted_value))

  | NVar _ -> raw

  | NApp (r,rl) ->
      let r' = subst_notation_constr subst bound r
      and rl' = List.Smart.map (subst_notation_constr subst bound) rl in
        if r' == r && rl' == rl then raw else
          NApp(r',rl')

  | NProj ((cst,u),rl,r) ->
      let ref = GlobRef.ConstRef cst in
      let ref',t = subst_global subst ref in
      assert (t = None);
      let rl' = List.Smart.map (subst_notation_constr subst bound) rl
      and r' = subst_notation_constr subst bound r in
        if ref' == ref && rl' == rl && r' == r then raw else
          NProj ((destConstRef ref',u),rl',r')

  | NList (id1,id2,r1,r2,b) ->
      let r1' = subst_notation_constr subst bound r1
      and r2' = subst_notation_constr subst bound r2 in
        if r1' == r1 && r2' == r2 then raw else
          NList (id1,id2,r1',r2',b)

  | NLambda (n,r1,r2) ->
      let r1' = Option.Smart.map (subst_notation_constr subst bound) r1
      and r2' = subst_notation_constr subst bound r2 in
        if r1' == r1 && r2' == r2 then raw else
          NLambda (n,r1',r2')

  | NProd (n,r1,r2) ->
      let r1' = Option.Smart.map (subst_notation_constr subst bound) r1
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
  | NFloat _ -> raw
  | NString _ -> raw

  | NHole knd ->
    let nknd = match knd with
    | GImplicitArg (ref, i, b) ->
      let nref, _ = subst_global subst ref in
      if nref == ref then knd else GImplicitArg (nref, i, b)
    | _ -> knd
    in
    if nknd == knd then raw
    else NHole nknd

  | NGenarg arg ->
    let arg' = Gensubst.generic_substitute subst arg in
    if arg' == arg then raw
    else NGenarg arg'

  | NCast (r1,k,t) ->
      let r1' = subst_notation_constr subst bound r1 in
      let t' = subst_notation_constr subst bound t in
      if r1' == r1 && t' == t then raw else NCast(r1',k,t')

  | NArray (t,def,ty) ->
      let def' = subst_notation_constr subst bound def
      and t' = Array.Smart.map (subst_notation_constr subst bound) t
      and ty' = subst_notation_constr subst bound ty
      in
        if def' == def && t' == t && ty' == ty then raw else
          NArray(t',def',ty')

let subst_interpretation subst (metas,pat) =
  let bound = List.fold_left (fun accu (id, _) -> Fresh.add id accu) Fresh.empty metas in
  (metas,subst_notation_constr subst (Namegen.Generator.fresh, bound) pat)

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
      GLambda(na,None,Explicit,DAst.make @@ GHole (GInternalHole), c)) tml rtn

let abstract_return_type_context_notation_constr tml rtn =
  abstract_return_type_context snd
    (fun na c -> NLambda(na,None,c)) tml rtn

let rec push_pattern_binders vars pat =
  match DAst.get pat with
  | PatVar na -> Termops.add_vname vars na
  | PatCstr (c, pl, na) -> List.fold_left push_pattern_binders (Termops.add_vname vars na) pl

let rec push_context_binders vars = function
  | [] -> vars
  | b :: bl ->
    let vars = match DAst.get b with
    | GLocalAssum (na,_,_,_) -> Termops.add_vname vars na
    | GLocalPattern ((disjpat,ids),p,bk,t) -> List.fold_right Id.Set.add ids vars
    | GLocalDef (na,_,_,_) -> Termops.add_vname vars na in
    push_context_binders vars bl

let is_term_meta id metas =
  try match Id.List.assoc id metas with NtnTypeConstr | NtnTypeConstrList -> true | _ -> false
  with Not_found -> false

let is_onlybinding_strict_meta id metas =
  try match Id.List.assoc id metas with NtnTypeBinder (NtnBinderParsedAsSomeBinderKind AsStrictPattern) -> true | _ -> false
  with Not_found -> false

let is_onlybinding_meta id metas =
  try match Id.List.assoc id metas with NtnTypeBinder _ -> true | _ -> false
  with Not_found -> false

let is_onlybindinglist_meta id metas =
  try match Id.List.assoc id metas with NtnTypeBinderList _ -> true | _ -> false
  with Not_found -> false

let is_onlybinding_pattern_like_meta isvar id metas =
  try match Id.List.assoc id metas with
    | NtnTypeBinder (NtnBinderParsedAsConstr (AsAnyPattern | AsStrictPattern)) -> true
    | NtnTypeBinder (NtnBinderParsedAsSomeBinderKind AsStrictPattern | NtnBinderParsedAsBinder) -> not isvar
    | NtnTypeBinder (NtnBinderParsedAsSomeBinderKind AsAnyPattern) -> true
    | NtnTypeBinder (NtnBinderParsedAsSomeBinderKind (AsIdent | AsName)) -> false
    | NtnTypeBinder (NtnBinderParsedAsConstr (AsIdent | AsName)) -> false
    | NtnTypeBinderList _ | NtnTypeConstr | NtnTypeConstrList -> false
  with Not_found -> false

let is_bindinglist_meta id metas =
  try match Id.List.assoc id metas with NtnTypeBinderList _ -> true | _ -> false
  with Not_found -> false

exception No_match

let alpha_rename renaming v =
  if renaming == [] then (* shortcut: *) v
  else try rename_glob_vars renaming v with UnsoundRenaming -> raise No_match

let static_binder_escape staticbinders v =
  List.exists (function (Name id,_) -> occur_glob_constr id v | (Anonymous,_) -> false) staticbinders

let add_env {actualvars;staticbinders;renaming} (terms,termlists,binders,binderlists) var v =
  (* Check that no capture of binding variables occur *)
  (* [staticbinders] is used when matching a pattern "fun x => ... x ... ?var ... x ..."
     with an actual term "fun z => ... z ..." when "x" is not bound in the
     notation, as in "Notation "'twice_upto' y" := (fun x => x + x + y)". Then
     we keep (z,x) in staticbinders, and we have to check that what the [v] which is bound
     to [var] does not contain z *)
  if not (Id.equal ldots_var var) && static_binder_escape staticbinders v then raise No_match;
  (* [renaming] is used when matching a pattern "fun x => ... x ... ?var ... x ..."
     with an actual term "fun z => ... z ..." when "x" is bound in the
     notation and the name "x" cannot be changed to "z", e.g. because
     used at another occurrence, as in "Notation "'lam' y , P & Q" :=
     ((fun y => P),(fun y => Q))". Then, we keep (z,y) in renaming, and we
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
  let v = alpha_rename renaming v in
  (* TODO: handle the case of multiple occs in different scopes *)
  ((var,(actualvars,staticbinders,v))::terms,termlists,binders,binderlists)

let add_termlist_env {actualvars;staticbinders;renaming} (terms,termlists,binders,binderlists) var vl =
  if List.exists (static_binder_escape staticbinders) vl then raise No_match;
  let vl = List.map (alpha_rename renaming) vl in
  (terms,(var,(actualvars,vl))::termlists,binders,binderlists)

let add_binding_env {actualvars} (terms,termlists,binders,binderlists) var v =
  (* TODO: handle the case of multiple occs in different scopes *)
  (terms,termlists,(var,(actualvars,v))::binders,binderlists)

let add_bindinglist_env {actualvars} (terms,termlists,binders,binderlists) var bl =
  (terms,termlists,binders,(var,(actualvars,bl))::binderlists)

let rec map_cases_pattern_name_left f = DAst.map (function
  | PatVar na -> PatVar (f na)
  | PatCstr (c,l,na) -> PatCstr (c,List.map_left (map_cases_pattern_name_left f) l,f na)
  )

let rec fold_cases_pattern_eq f x p p' =
  let loc = p.CAst.loc in
  match DAst.get p, DAst.get p' with
  | PatVar na, PatVar na' -> let x,na = f x na na' in x, DAst.make ?loc @@ PatVar na
  | PatCstr (c,l,na), PatCstr (c',l',na') when Construct.CanOrd.equal c c' ->
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
  Construct.CanOrd.equal c1 c2 && List.equal cases_pattern_eq pl1 pl2 &&
  Name.equal na1 na2
| _ -> false

let rec pat_binder_of_term t = DAst.map (function
  | GVar id -> PatVar (Name id)
  | GApp (t, l) ->
    begin match DAst.get t with
    | GRef (GlobRef.ConstructRef cstr,_) ->
     let nparams = Inductiveops.inductive_nparams (Global.env()) (fst cstr) in
     let _,l = List.chop nparams l in
     PatCstr (cstr, List.map pat_binder_of_term l, Anonymous)
    | _ -> raise No_match
    end
  | _ -> raise No_match
  ) t

let unify_name_upto ({actualvars;staticbinders;renaming} as alp) na na' =
  match na, na' with
  | Anonymous, na' -> {alp with actualvars = Termops.add_vname actualvars na'}, na'
  | na, Anonymous -> {alp with actualvars = Termops.add_vname actualvars na}, na
  | Name id, Name id' ->
     let vars = Termops.add_vname actualvars na' in
     if Id.equal id id' then {alp with actualvars = vars}, na'
     else {actualvars = vars; staticbinders; renaming = (id,id')::renaming}, na'

let unify_pat_upto alp p p' =
  try fold_cases_pattern_eq unify_name_upto alp p p' with Failure _ -> raise No_match

let unify_term renaming v v' =
  match DAst.get v, DAst.get v' with
  | GHole _, _ -> v'
  | _, GHole _ -> v
  | _, _ -> let v = alpha_rename renaming v in if glob_constr_eq v v' then v else raise No_match

let unify_opt_term alp v v' =
  match v, v' with
  | Some t, Some t' -> Some (unify_term alp t t')
  | (Some _ as x), None | None, (Some _ as x) -> x
  | None, None -> None

let unify_binding_kind bk bk' = if bk == bk' then bk' else raise No_match

let unify_relevance_info r r' = if relevance_info_eq r r' then r else raise No_match

let unify_binder_upto alp b b' =
  let loc, loc' = CAst.(b.loc, b'.loc) in
  match DAst.get b, DAst.get b' with
  | GLocalAssum (na,r,bk,t), GLocalAssum (na',r',bk',t') ->
     let alp', na = unify_name_upto alp na na' in
     alp', DAst.make ?loc @@
     GLocalAssum
       (na,
        unify_relevance_info r r',
        unify_binding_kind bk bk',
        unify_term alp.renaming t t')
  | GLocalDef (na,r,c,t), GLocalDef (na',r',c',t') ->
     let alp', na = unify_name_upto alp na na' in
     alp', DAst.make ?loc @@
     GLocalDef
       (na,
        unify_relevance_info r r',
        unify_term alp.renaming c c',
        unify_opt_term alp.renaming t t')
  | GLocalPattern ((disjpat,ids),id,bk,t), GLocalPattern ((disjpat',_),_,bk',t') when List.length disjpat = List.length disjpat' ->
     let alp', p = List.fold_left2_map unify_pat_upto alp disjpat disjpat' in
     alp', DAst.make ?loc @@ GLocalPattern ((p,ids), id, unify_binding_kind bk bk', unify_term alp.renaming t t')
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

let unify_id renaming id na' =
  let id = rename_var renaming id in
  match na' with
  | Anonymous -> Name id
  | Name id' -> if Id.equal id id' then na' else raise No_match

let unify_pat renaming p p' =
  if cases_pattern_eq (map_cases_pattern_name_left (Name.map (rename_var renaming)) p) p' then p'
  else raise No_match

let unify_term_binder renaming c = DAst.(map (fun b' ->
  match DAst.get c, b' with
  | GVar id, GLocalAssum (na', r', bk', t') ->
     GLocalAssum (unify_id renaming id na', r', bk', t')
  | _, GLocalPattern (([p'],ids), id, bk', t') ->
     let p = pat_binder_of_term c in
     GLocalPattern (([unify_pat renaming p p'],ids), id, bk', t')
  | _ -> raise No_match))

let rec unify_terms_binders renaming cl bl' =
  match cl, bl' with
  | [], [] -> []
  | c :: cl', b' :: bl' ->
     begin match DAst.get b' with
     | GLocalDef (_, _, _, t) -> b' :: unify_terms_binders renaming cl bl'
     | _ -> unify_term_binder renaming c b' :: unify_terms_binders renaming cl' bl'
     end
  | _ -> raise No_match

let bind_term_env alp (terms,termlists,binders,binderlists as sigma) var v =
  try
    (* If already bound to a term, unify with the new term *)
    let vars,_alp',v' = Id.List.assoc var terms in
    (* Note: at Notation definition time, it should have been checked that v and v' are
       in the same static context, i.e. alp.staticbinders = _alp'.staticbinders *)
    let v'' = unify_term alp.renaming v v' in
    if v'' == v' then sigma else
      let sigma = (Id.List.remove_assoc var terms,termlists,binders,binderlists) in
      let alp' = {alp with actualvars = Id.Set.union vars alp.actualvars} in
      add_env alp' sigma var v
  with Not_found -> add_env alp sigma var v

let bind_termlist_env alp (terms,termlists,binders,binderlists as sigma) var vl =
  try
    (* If already bound to a list of term, unify with the new terms *)
    let vars,vl' = Id.List.assoc var termlists in
    let vl = unify_terms alp.renaming vl vl' in
    let sigma = (terms,Id.List.remove_assoc var termlists,binders,binderlists) in
    let alp' = {alp with actualvars = Id.Set.union vars alp.actualvars} in
    add_termlist_env alp' sigma var vl
  with Not_found -> add_termlist_env alp sigma var vl

let bind_term_as_binding_env alp (terms,termlists,binders,binderlists as sigma) var id =
  try
    (* If already bound to a term, unify the binder and the term *)
    let vars',_alp',v' = Id.List.assoc var terms in
    match DAst.get v' with
    | GVar id' | GRef (GlobRef.VarRef id',None) ->
       let {actualvars;staticbinders;renaming} = alp in
       let vars = Id.Set.add id' actualvars in
       let renaming = if not (Id.equal id id') then (id,id')::renaming else renaming in
       {actualvars = Id.Set.union vars' vars; staticbinders; renaming}, sigma
    | t ->
       (* The term is a non-variable pattern *)
       raise No_match
  with Not_found ->
    let alp = {alp with actualvars = Id.Set.add id alp.actualvars} in
    (* The matching against a term allowing to find the instance has not been found yet *)
    (* If it will be a different name, we shall unfortunately fail *)
    (* TODO: look at the consequences for alp *)
    alp, add_env alp sigma var (DAst.make @@ GVar id)

let bind_singleton_bindinglist_as_term_env alp (terms,termlists,binders,binderlists as sigma) var c =
  try
    (* If already bound to a binder, unify the term and the binder *)
    let vars,patl' = Id.List.assoc var binderlists in
    let patl'' = unify_terms_binders alp.renaming [c] patl' in
    if patl' == patl'' then sigma
    else
      let sigma = (terms,termlists,binders,Id.List.remove_assoc var binderlists) in
      let alp' = {alp with actualvars = Id.Set.union vars alp.actualvars} in
      add_bindinglist_env alp' sigma var patl''
  with Not_found ->
    (* A term-as-binder occurs in the scope of a binder which is already bound *)
    anomaly (Pp.str "Unbound term as binder.")

let bind_binding_as_term_env alp (terms,termlists,binders,binderlists as sigma) var c =
  let env = Global.env () in
  let pat = try cases_pattern_of_glob_constr env Anonymous c with Not_found -> raise No_match in
  try
    (* If already bound to a binder, unify the term and the binder *)
    let vars,patl' = Id.List.assoc var binders in
    let patl'' = List.map2 (unify_pat alp.renaming) [pat] patl' in
    if patl' == patl'' then sigma
    else
      let sigma = (terms,termlists,Id.List.remove_assoc var binders,binderlists) in
      let alp' = {alp with actualvars = Id.Set.union vars alp.actualvars} in
      add_binding_env alp' sigma var patl''
  with Not_found -> add_binding_env alp sigma var [pat]

let bind_binding_env alp (terms,termlists,binders,binderlists as sigma) var disjpat =
  try
    (* If already bound to a binder possibly *)
    (* generating an alpha-renaming from unifying the new binder *)
    let vars,disjpat' = Id.List.assoc var binders in
    (* if, maybe, there is eventually casts in patterns, the common types have *)
    (* to exclude the spine of variable from the two locations they occur *)
    let alp' = {alp with actualvars = Id.Set.union vars alp.actualvars} in
    let alp, disjpat = List.fold_left2_map unify_pat_upto alp disjpat disjpat' in
    let sigma = (terms,termlists,Id.List.remove_assoc var binders,binderlists) in
    alp, add_binding_env alp' sigma var disjpat
  with Not_found ->
    (* Note: all patterns of the disjunction are supposed to have the same
       variables, thus one is enough *)
    let alp = {alp with actualvars = push_pattern_binders alp.actualvars (List.hd disjpat)} in
    alp, add_binding_env alp sigma var disjpat

let bind_bindinglist_env alp (terms,termlists,binders,binderlists as sigma) var bl =
  let bl = List.rev bl in
  try
    (* If already bound to a list of binders possibly *)
    (* generating an alpha-renaming from unifying the new binders *)
    let vars, bl' = Id.List.assoc var binderlists in
    (* The shared subterm can be under two different spines of *)
    (* variables (themselves bound in the notation), so we take the *)
    (* union of both locations *)
    let alp' = {alp with actualvars = Id.Set.union vars alp.actualvars} in
    let alp, bl = unify_binders_upto alp bl bl' in
    let sigma = (terms,termlists,binders,Id.List.remove_assoc var binderlists) in
    alp, add_bindinglist_env alp' sigma var bl
  with Not_found ->
    let alp = {alp with actualvars = push_context_binders alp.actualvars bl} in
    alp, add_bindinglist_env alp sigma var bl

let bind_bindinglist_as_termlist_env alp (terms,termlists,binders,binderlists) var cl =
  try
    (* If already bound to a list of binders, unify the terms and binders *)
    let vars,bl' = Id.List.assoc var binderlists in
    let bl = unify_terms_binders alp.renaming cl bl' in
    let alp = {alp with actualvars = Id.Set.union vars alp.actualvars} in
    let sigma = (terms,termlists,binders,Id.List.remove_assoc var binderlists) in
    add_bindinglist_env alp sigma var bl
  with Not_found ->
    anomaly (str "There should be a binder list bindings this list of terms.")

let match_fix_kind fk1 fk2 =
  match (fk1,fk2) with
  | GCoFix n1, GCoFix n2 -> Int.equal n1 n2
  | GFix (nl1,n1), GFix (nl2,n2) ->
      let test n1 n2 = match n1, n2 with
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
  | (na1,Name id2) ->
      {alp with staticbinders = (na1,id2)::alp.staticbinders},sigma
  | (Anonymous,Anonymous) -> alp,sigma
  | _ -> raise No_match

let rec match_cases_pattern_binders allow_catchall metas (alp,sigma as acc) pat1 pat2 =
  match DAst.get pat1, DAst.get pat2 with
  | PatVar _, PatVar (Name id2) when is_onlybinding_pattern_like_meta true id2 metas ->
      bind_binding_env alp sigma id2 [pat1]
  | PatVar id1, PatVar (Name id2) when is_onlybindinglist_meta id2 metas ->
      let t1 = DAst.make @@ GHole(GBinderType id1) in
      bind_bindinglist_env alp sigma id2 [DAst.make @@ GLocalAssum (id1,None,Explicit,t1)]
  | _, PatVar (Name id2) when is_onlybinding_pattern_like_meta false id2 metas ->
      bind_binding_env alp sigma id2 [pat1]
  | _, PatVar (Name id2) when is_onlybindinglist_meta id2 metas ->
      (* dummy data; should not be used anyway *)
      let id1 = Namegen.next_ident_away (Id.of_string "x") Id.Set.empty in
      let t1 = DAst.make @@ GHole(GBinderType (Name id1)) in
      let ids1 = [] in
      bind_bindinglist_env alp sigma id2 [DAst.make @@ GLocalPattern (([pat1],ids1),id1,Explicit,t1)]
  | PatVar na1, PatVar na2 -> match_names metas acc na1 na2
  | _, PatVar Anonymous when allow_catchall -> acc
  | PatCstr (c1,patl1,na1), PatCstr (c2,patl2,na2)
      when Construct.CanOrd.equal c1 c2 && Int.equal (List.length patl1) (List.length patl2) ->
      List.fold_left2 (match_cases_pattern_binders false metas)
        (match_names metas acc na1 na2) patl1 patl2
  | _ -> raise No_match

let remove_sigma x (terms,termlists,binders,binderlists) =
  (Id.List.remove_assoc x terms,termlists,binders,binderlists)

let remove_bindinglist_sigma x (terms,termlists,binders,binderlists) =
  (terms,termlists,binders,Id.List.remove_assoc x binderlists)

let add_ldots_var metas = (ldots_var,NtnTypeConstr)::metas

let add_meta_bindinglist x metas = (x,NtnTypeBinderList (*arbitrary:*) NtnBinderParsedAsBinder)::metas

(* This tells if letins in the middle of binders should be included in
   the sequence of binders *)
let glue_inner_letin_with_decls = true

(* This tells if trailing letins (with no further proper binders)
   should be included in sequence of binders *)
let glue_trailing_letin_with_decls = false

exception OnlyTrailingLetIns

let match_binderlist match_iter_fun match_termin_fun alp metas sigma rest x y iter termin revert =
  let rec aux trailing_letins alp sigma bl rest =
    try
      let metas = add_ldots_var (add_meta_bindinglist y metas) in
      let (terms,_,_,binderlists as sigma) = match_iter_fun alp metas sigma rest iter in
      let _,newstaticbinders,rest = Id.List.assoc ldots_var terms in
      let b =
        match Id.List.assoc y binderlists with _,[b] -> b | _ ->assert false
      in
      let sigma = remove_bindinglist_sigma y (remove_sigma ldots_var sigma) in
      (* In case y is bound not only to a binder but also to a term *)
      let sigma = remove_sigma y sigma in
      let alp' = {alp with staticbinders = newstaticbinders} in
      aux false alp' sigma (b::bl) rest
    with No_match ->
    match DAst.get rest with
    | GLetIn (na,r,c,t,rest') when glue_inner_letin_with_decls ->
       let b = DAst.make ?loc:rest.CAst.loc @@ GLocalDef (na,r,c,t) in
       (* collect let-in *)
       (try aux true alp sigma (b::bl) rest'
        with OnlyTrailingLetIns
             when not (trailing_letins && not glue_trailing_letin_with_decls) ->
         (* renounce to take into account trailing let-ins *)
         if not (List.is_empty bl) then alp, bl, rest, sigma else raise No_match)
    | _ ->
       if trailing_letins && not glue_trailing_letin_with_decls then
         (* Backtrack to when we tried to glue letins *)
         raise OnlyTrailingLetIns;
       if not (List.is_empty bl) then alp, bl, rest, sigma else raise No_match in
  let alp,bl,rest,sigma = aux false alp sigma [] rest in
  let bl = if revert then List.rev bl else bl in
  let alp,sigma = bind_bindinglist_env alp sigma x bl in
  match_termin_fun alp metas sigma rest termin

let add_meta_term x metas = (x,NtnTypeConstr)::metas

let match_termlist match_fun alp metas sigma rest x y iter termin revert =
  let rec aux alp sigma acc rest =
    try
      let metas = add_ldots_var (add_meta_term y metas) in
      let (terms,_,_,_ as sigma) = match_fun alp metas sigma rest iter in
      let _,newstaticbinders,rest = Id.List.assoc ldots_var terms in
      let vars,_,t = Id.List.assoc y terms in
      let sigma = remove_sigma y (remove_sigma ldots_var sigma) in
      if !print_parentheses && not (List.is_empty acc) then raise No_match;
      (* The union is overkill at the current time because each term matches *)
      (* at worst the same binder metavariable of the same pattern *)
      let alp' = {actualvars = Id.Set.union vars alp.actualvars; staticbinders = newstaticbinders; renaming = alp.renaming} in
      aux alp' sigma (t::acc) rest
    with No_match when not (List.is_empty acc) ->
      alp, acc, match_fun alp metas sigma rest termin in
  let alp,l,(terms,termlists,binders,binderlists as sigma) = aux alp sigma [] rest in
  let l = if revert then l else List.rev l in
  if is_bindinglist_meta x metas then
    (* This is a recursive pattern for both bindings and terms; it is *)
    (* registered for binders *)
    bind_bindinglist_as_termlist_env alp sigma x l
  else
    bind_termlist_env alp sigma x l

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

let eta_well_typed pat =
  (* A criterion for well-typedness of the eta-expansion
     is that the head of the pattern is rigid (see #15221) *)
  match pat with NVar _ -> false | _ -> true

let is_var_term = function
  (* The kind of expressions allowed to be both a term and a binding variable *)
  | GVar _ -> true
  | GRef (GlobRef.VarRef _,None) -> true
  | _ -> false

let rec match_ inner u alp metas sigma a1 a2 =
  let open CAst in
  let loc = a1.loc in
  match DAst.get a1, a2 with
  (* Matching notation variable *)
  | r1, NVar id2 when is_term_meta id2 metas -> bind_term_env alp sigma id2 a1
  | r1, NVar id2 when is_var_term r1 && is_onlybinding_pattern_like_meta true id2 metas -> bind_binding_as_term_env alp sigma id2 a1
  | r1, NVar id2 when is_onlybinding_pattern_like_meta false id2 metas -> bind_binding_as_term_env alp sigma id2 a1
  | r1, NVar id2 when is_var_term r1 && is_onlybinding_strict_meta id2 metas -> raise No_match
  | r1, NVar id2 when is_var_term r1 && is_onlybinding_meta id2 metas -> bind_binding_as_term_env alp sigma id2 a1
  | r1, NVar id2 when is_bindinglist_meta id2 metas -> bind_singleton_bindinglist_as_term_env alp sigma id2 a1

  (* Matching recursive notations for terms *)
  | r1, NList (x,y,iter,termin,revert) ->
      match_termlist (match_hd u) alp metas sigma a1 x y iter termin revert

  (* Matching recursive notations for binders: general case *)
  | _r, NBinderList (x,y,iter,termin,revert) ->
    (* When revert=true, binders are considered "inner" and thus not cumulative, as e.g. in
       Notation "!! x .. y # A #" := (.. (A,(forall x, True)) ..,(forall y, True)) (at level 200, x binder).
       This has an impact on the heuristic of preferring using "A -> B" where
       a recursive Prod binder on a anonymous would otherwise also be possible *)
      match_binderlist (match_ revert u) (match_hd u) alp metas sigma a1 x y iter termin revert

  (* Matching a static variable (not bound in the notation) *)
  | GVar id1, NVar id2 when alpha_var id1 id2 alp.staticbinders -> sigma

  (* Matching compositionally *)
  | GRef (r1,u1), NRef (r2,u2) when (GlobRef.CanOrd.equal r1 r2) && compare_glob_universe_instances_le u1 u2 -> sigma
  | GApp (f1,l1), NApp (f2,l2) ->
      let n1 = List.length l1 and n2 = List.length l2 in
      let f1,l1,f2,l2 =
        if n1 < n2 then
          let l21,l22 = List.chop (n2-n1) l2 in f1,l1, NApp (f2,l21), l22
        else if n1 > n2 then
          let l11,l12 = List.chop (n1-n2) l1 in DAst.make ?loc @@ GApp (f1,l11),l12, f2,l2
        else f1,l1, f2, l2 in
      let may_use_eta = does_not_come_from_already_eta_expanded_var f1 && eta_well_typed f2 in
      List.fold_left2 (match_ may_use_eta u alp metas)
        (match_hd u alp metas sigma f1 f2) l1 l2
  | GProj ((cst1,u1),l1,a1), NProj ((cst2,u2),l2,a2) when GlobRef.CanOrd.equal (GlobRef.ConstRef cst1) (GlobRef.ConstRef cst2) && compare_glob_universe_instances_le u1 u2 ->
     match_in u alp metas (List.fold_left2 (match_in u alp metas) sigma l1 l2) a1 a2
  | GApp (f1,l1), NProj ((cst2,u2),l2,a2) ->
     (match DAst.get f1 with
     | GRef (r1,u1) when GlobRef.CanOrd.equal r1 (GlobRef.ConstRef cst2) && compare_glob_universe_instances_le u1 u2 &&
         List.length l1 = List.length l2 + 1 ->
        List.fold_left2 (match_in u alp metas) sigma l1 (l2@[a2])
     | _ -> raise No_match)
  | GLambda (na1,_,bk1,t1,b1), NLambda (na2,t2,b2) ->
     match_extended_binders false u alp metas na1 na2 bk1 t1 (match_in_type u alp metas sigma t1 t2) b1 b2
  | GProd (na1,_,bk1,t1,b1), NProd (na2,t2,b2) ->
     match_extended_binders (not inner) u alp metas na1 na2 bk1 t1 (match_in_type u alp metas sigma t1 t2) b1 b2
  | GLetIn (na1,_,b1,t1,c1), NLetIn (na2,b2,None,c2)
  | GLetIn (na1,_,b1,(None as t1),c1), NLetIn (na2,b2,_,c2) ->
     let t = match t1 with Some t -> t | None -> DAst.make @@ GHole(GBinderType na1) in
     match_extended_binders false u alp metas na1 na2 Explicit t (match_in u alp metas sigma b1 b2) c1 c2
  | GLetIn (na1,_,b1,Some t1,c1), NLetIn (na2,b2,Some t2,c2) ->
     match_extended_binders false u alp metas na1 na2 Explicit t1
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
        (List.fold_left2 (fun (alp,sigma) (na1,_,_,oc1,b1) (na2,oc2,b2) ->
          let sigma =
            match_in u alp metas
              (match_opt (match_in u alp metas) sigma oc1 oc2) b1 b2
          in match_names metas (alp,sigma) na1 na2)) (alp,sigma) dll1 dll2 in
      let sigma = Array.fold_left2 (match_in u alp metas) sigma tl1 tl2 in
      let alp,sigma = Array.fold_right2 (fun id1 id2 alsig ->
        match_names metas alsig (Name id1) (Name id2)) idl1 idl2 (alp,sigma) in
      Array.fold_left2 (match_in u alp metas) sigma bl1 bl2
  | GCast(c1, k1, t1), NCast(c2, k2, t2) ->
    let sigma = match_in u alp metas sigma c1 c2 in
    if not (Option.equal cast_kind_eq k1 k2) then raise No_match;
    match_in u alp metas sigma t1 t2

  (* Next pair of lines useful only if not coming from detyping *)
  | GSort (None, UNamed [(GSProp|GProp|GSet),0]), NSort (None, UAnonymous _) -> raise No_match
  | GSort _, NSort (None, UAnonymous _) when not u -> sigma

  | GSort s1, NSort s2 when glob_sort_eq s1 s2 -> sigma
  | GInt i1, NInt i2 when Uint63.equal i1 i2 -> sigma
  | GFloat f1, NFloat f2 when Float64.equal f1 f2 -> sigma
  | GString s1, NString s2 when Pstring.equal s1 s2 -> sigma
  | GPatVar _, NHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, NHole _ -> sigma

  (* On the fly eta-expansion so as to use notations of the form
     "exists x, P x" for "ex P"; ensure at least one constructor is
     consumed to avoid looping; expects type not given because don't know
     otherwise how to ensure it corresponds to a well-typed eta-expansion;
     we make an exception for types which are metavariables: this is useful e.g.
     to print "{x:_ & P x}" knowing that notation "{x & P x}" is not defined. *)
  | _b1, NLambda (Name id as na,(None | Some (NVar _) as t2),b2) when inner ->
      let avoid =
        Id.Set.union (free_glob_vars a1) (* as in Namegen: *) (glob_visible_short_qualid a1) in
      let id' = Namegen.next_ident_away id avoid in
      let t1 = DAst.make @@ GHole (GBinderType (Name id')) in
      let sigma = match t2 with
      | None -> sigma
      | Some (NVar id2) -> bind_term_env alp sigma id2 t1
      | _ -> assert false in
      let (alp,sigma) =
        if is_bindinglist_meta id metas then
          bind_bindinglist_env alp sigma id [DAst.make @@ GLocalAssum (Name id',None,Explicit,t1)]
        else
          match_names metas (alp,sigma) (Name id') na in
      match_in u alp metas sigma (mkGApp a1 [DAst.make @@ GVar id']) b2

  | GArray(_u,t,def,ty), NArray(nt,ndef,nty) ->
    if Int.equal (Array.length t) (Array.length nt) then
      let sigma = match_in u alp metas sigma def ndef in
      let sigma = match_in u alp metas sigma ty nty in
      Array.fold_left2 (match_in u alp metas) sigma t nt
    else raise No_match

  | (GRef _ | GVar _ | GEvar _ | GPatVar _ | GApp _ | GProj _ | GLambda _ | GProd _
     | GLetIn _ | GCases _ | GLetTuple _ | GIf _ | GRec _ | GSort _ | GHole _ | GGenarg _
     | GCast _ | GInt _ | GFloat _ | GString _ | GArray _), _ -> raise No_match

and match_in_type u alp metas sigma t = function
  | None -> sigma
  | Some t' -> match_in u alp metas sigma t t'

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
  | _, _, Name id when is_bindinglist_meta id metas ->
      if (isprod && na1 = Anonymous) then raise No_match (* prefer using "A -> B" for anonymous forall *);
      let alp,sigma = bind_bindinglist_env alp sigma id [DAst.make ?loc @@ GLocalAssum (na1,None,bk,t)] in
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

(* Turning substitution based on binding/term distinction into a
   substitution based on entry production: indeed some binders may
   have to be seen as terms from the parsing/printing point of view *)
let group_by_type ids (terms,termlists,binders,binderlists) =
  List.fold_right (fun (x,(scl,_,typ)) (terms',termlists',binders',binderlists') ->
    match typ with
    | NtnTypeConstr ->
       (* term -> term *)
       let vars,_alp',term = try Id.List.assoc x terms with Not_found -> raise No_match in
       (((vars,term),scl)::terms',termlists',binders',binderlists')
    | NtnTypeBinder (NtnBinderParsedAsConstr _) ->
       (* binder -> term *)
       (match Id.List.assoc x binders with
        | vars,[pat] ->
          let v = glob_constr_of_cases_pattern (Global.env()) pat in
          (((vars,v),scl)::terms',termlists',binders',binderlists')
        | _ -> raise No_match)
    | NtnTypeBinder (NtnBinderParsedAsBinder | NtnBinderParsedAsSomeBinderKind _) ->
       (* term list -> term list *)
       (terms',termlists',(Id.List.assoc x binders,scl)::binders',binderlists')
    | NtnTypeConstrList ->
       (* term list -> term list *)
       (terms',(Id.List.assoc x termlists,scl)::termlists',binders',binderlists')
    | NtnTypeBinderList (NtnBinderParsedAsConstr _) ->
       (* binder list -> term list *)
       let vars,patl = try Id.List.assoc x binderlists with Not_found -> raise No_match in
       let v = List.map (fun pat -> match DAst.get pat with
           | GLocalPattern ((disjpat,_),_,_,_) ->
             List.map (glob_constr_of_cases_pattern (Global.env())) disjpat
           | GLocalAssum (Anonymous,_,bk,t) ->
             let hole = DAst.make (GHole (GBinderType Anonymous)) in
             [DAst.make (GCast (hole, Some DEFAULTcast, t))]
           | GLocalAssum (Name id,_,bk,t) ->
             [DAst.make (GCast (DAst.make (GVar id), Some DEFAULTcast, t))]
           | GLocalDef _ -> raise No_match) patl in
       (terms',((vars,List.flatten v),scl)::termlists',binders',binderlists')
    | NtnTypeBinderList (NtnBinderParsedAsBinder | NtnBinderParsedAsSomeBinderKind _) ->
      (* binder list -> binder list *)
      let bl = try Id.List.assoc x binderlists with Not_found -> raise No_match in
       (terms',termlists',binders',(bl,scl)::binderlists'))
    ids ([],[],[],[])

let match_notation_constr ~print_univ c ~vars (metas,pat) =
  let metatyps = List.map (fun (id,(_,_,typ)) -> (id,typ)) metas in
  let subst = match_ false print_univ {actualvars=vars;staticbinders=[];renaming=[]} metatyps ([],[],[],[]) c pat in
  group_by_type metas subst

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
  | r1, NVar id2 when Id.List.mem_assoc id2 metas -> (bind_env_cases_pattern sigma id2 a1),(false,0,[])
  | PatVar Anonymous, NHole _ -> sigma,(false,0,[])
  | PatCstr ((ind,_ as r1),largs,Anonymous), NRef (GlobRef.ConstructRef r2,None) when Construct.CanOrd.equal r1 r2 ->
      let l = try add_patterns_for_params_remove_local_defs (Global.env ()) r1 largs with Not_found -> raise No_match in
      sigma,(false,0,l)
  | PatCstr ((ind,_ as r1),args1,Anonymous), NApp (NRef (GlobRef.ConstructRef r2,None),l2)
      when Construct.CanOrd.equal r1 r2 ->
      let l1 = try add_patterns_for_params_remove_local_defs (Global.env()) r1 args1 with Not_found -> raise No_match in
      let le2 = List.length l2 in
      if le2 > List.length l1
      then
        raise No_match
      else
        let l1',more_args = Util.List.chop le2 l1 in
        (* Convention: notations to @f don't keep implicit arguments *)
        let no_implicit = le2 = 0 in
        (List.fold_left2 (match_cases_pattern_no_more_args metas) sigma l1' l2),(no_implicit,le2,more_args)
  | r1, NList (x,y,iter,termin,revert) ->
      (match_cases_pattern_list (match_cases_pattern_no_more_args)
        metas (terms,termlists,(),()) a1 x y iter termin revert),(false,0,[])
  | _ -> raise No_match

and match_cases_pattern_no_more_args metas sigma a1 a2 =
    match match_cases_pattern metas sigma a1 a2 with
      | out,(_,_,[]) -> out
      | _ -> raise No_match

let match_ind_pattern metas sigma ind pats a2 =
  match a2 with
  | NRef (GlobRef.IndRef r2,None) when Ind.CanOrd.equal ind r2 ->
      sigma,(false,0,pats)
  | NApp (NRef (GlobRef.IndRef r2,None),l2)
      when Ind.CanOrd.equal ind r2 ->
      let le2 = List.length l2 in
      if Int.equal le2 0 (* Special case of a notation for a @Cstr *) || le2 > List.length pats
      then
        raise No_match
      else
        let l1',more_args = Util.List.chop le2 pats in
        let no_implicit = le2 = 0 in
        (List.fold_left2 (match_cases_pattern_no_more_args metas) sigma l1' l2),(no_implicit,le2,more_args)
  |_ -> raise No_match

let reorder_canonically_substitution terms termlists metas =
  List.fold_right (fun (x,(scl,_,typ)) (terms',termlists',binders') ->
    match typ with
      | NtnTypeConstr | NtnTypeBinder (NtnBinderParsedAsConstr _) -> ((Id.List.assoc x terms, scl)::terms',termlists',binders')
      | NtnTypeConstrList -> (terms',(Id.List.assoc x termlists,scl)::termlists',binders')
      | NtnTypeBinder (NtnBinderParsedAsBinder | NtnBinderParsedAsSomeBinderKind _) ->
         (terms',termlists',(Id.List.assoc x terms, scl)::binders')
      | NtnTypeBinderList _ -> anomaly (str "Unexpected binder in pattern notation."))
    metas ([],[],[])

let match_notation_constr_cases_pattern c (metas,pat) =
  let metatyps = List.map (fun (id,(_,_,typ)) -> (id,typ)) metas in
  let (terms,termlists,(),()),more_args = match_cases_pattern metatyps ([],[],(),()) c pat in
  reorder_canonically_substitution terms termlists metas, more_args

let match_notation_constr_ind_pattern ind args (metas,pat) =
  let metatyps = List.map (fun (id,(_,_,typ)) -> (id,typ)) metas in
  let (terms,termlists,(),()),more_args = match_ind_pattern metatyps ([],[],(),()) ind args pat in
  reorder_canonically_substitution terms termlists metas, more_args
