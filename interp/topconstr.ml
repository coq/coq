(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Pp
open CErrors
open Util
open Names
open Nameops
open Libnames
open Misctypes
open Constrexpr
open Constrexpr_ops
(*i*)


let asymmetric_patterns = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; Goptions.optdepr = false;
  Goptions.optname = "no parameters in constructors";
  Goptions.optkey = ["Asymmetric";"Patterns"];
  Goptions.optread = (fun () -> !asymmetric_patterns);
  Goptions.optwrite = (fun a -> asymmetric_patterns:=a);
}

(**********************************************************************)
(* Miscellaneous *)

let error_invalid_pattern_notation ?loc () =
  user_err ?loc  (str "Invalid notation for pattern.")

(**********************************************************************)
(* Functions on constr_expr *)

let is_constructor id =
  try Globnames.isConstructRef
        (Smartlocate.global_of_extended_global
           (Nametab.locate_extended (qualid_of_ident id)))
  with Not_found -> false

let rec cases_pattern_fold_names f a pt = match CAst.(pt.v) with
  | CPatRecord l ->
      List.fold_left (fun acc (r, cp) -> cases_pattern_fold_names f acc cp) a l
  | CPatAlias (pat,id) -> f id a
  | CPatOr (patl) ->
      List.fold_left (cases_pattern_fold_names f) a patl
  | CPatCstr (_,patl1,patl2) ->
    List.fold_left (cases_pattern_fold_names f)
      (Option.fold_left (List.fold_left (cases_pattern_fold_names f)) a patl1) patl2
  | CPatNotation (_,(patl,patll),patl') ->
      List.fold_left (cases_pattern_fold_names f)
	(List.fold_left (cases_pattern_fold_names f) a (patl@List.flatten patll)) patl'
  | CPatDelimiters (_,pat) -> cases_pattern_fold_names f a pat
  | CPatAtom (Some (Ident (_,id))) when not (is_constructor id) -> f id a
  | CPatPrim _ | CPatAtom _ -> a
  | CPatCast ({CAst.loc},_) ->
     CErrors.user_err ?loc ~hdr:"cases_pattern_fold_names"
                      (Pp.strbrk "Casts are not supported here.")

let ids_of_pattern =
  cases_pattern_fold_names Id.Set.add Id.Set.empty

let ids_of_pattern_list =
  List.fold_left
    (Loc.located_fold_left
      (List.fold_left (cases_pattern_fold_names Id.Set.add)))
    Id.Set.empty

let ids_of_cases_indtype p =
  cases_pattern_fold_names Id.Set.add Id.Set.empty p

let ids_of_cases_tomatch tms =
  List.fold_right
    (fun (_, ona, indnal) l ->
      Option.fold_right (fun t ids -> cases_pattern_fold_names Id.Set.add ids t)
      indnal
        (Option.fold_right (Loc.down_located (name_fold Id.Set.add)) ona l))
    tms Id.Set.empty

let rec fold_constr_expr_binders g f n acc b = function
  | (nal,bk,t)::l ->
      let nal = snd (List.split nal) in
      let n' = List.fold_right (name_fold g) nal n in
      f n (fold_constr_expr_binders g f n' acc b l) t
  | [] ->
      f n acc b

let rec fold_local_binders g f n acc b = function
  | CLocalAssum (nal,bk,t)::l ->
      let nal = snd (List.split nal) in
      let n' = List.fold_right (name_fold g) nal n in
      f n (fold_local_binders g f n' acc b l) t
  | CLocalDef ((_,na),c,t)::l ->
      Option.fold_left (f n) (f n (fold_local_binders g f (name_fold g na n) acc b l) c) t
  | CLocalPattern (_,(pat,t))::l ->
      let acc = fold_local_binders g f (cases_pattern_fold_names g n pat) acc b l in
      Option.fold_left (f n) acc t
  | [] ->
      f n acc b

let fold_constr_expr_with_binders g f n acc = CAst.with_val (function
  | CAppExpl ((_,_,_),l) -> List.fold_left (f n) acc l
  | CApp ((_,t),l) -> List.fold_left (f n) (f n acc t) (List.map fst l)
  | CProdN (l,b) | CLambdaN (l,b) -> fold_constr_expr_binders g f n acc b l
  | CLetIn (na,a,t,b) ->
     f (name_fold g (snd na) n) (Option.fold_left (f n) (f n acc a) t) b
  | CCast (a,(CastConv b|CastVM b|CastNative b)) -> f n (f n acc a) b
  | CCast (a,CastCoerce) -> f n acc a
  | CNotation (_,(l,ll,bll)) ->
      (* The following is an approximation: we don't know exactly if
         an ident is binding nor to which subterms bindings apply *)
      let acc = List.fold_left (f n) acc (l@List.flatten ll) in
      List.fold_left (fun acc bl -> fold_local_binders g f n acc (CAst.make @@ CHole (None,IntroAnonymous,None)) bl) acc bll
  | CGeneralization (_,_,c) -> f n acc c
  | CDelimiters (_,a) -> f n acc a
  | CHole _ | CEvar _ | CPatVar _ | CSort _ | CPrim _ | CRef _ ->
      acc
  | CRecord l -> List.fold_left (fun acc (id, c) -> f n acc c) acc l
  | CCases (sty,rtnpo,al,bl) ->
      let ids = ids_of_cases_tomatch al in
      let acc = Option.fold_left (f (Id.Set.fold g ids n)) acc rtnpo in
      let acc = List.fold_left (f n) acc (List.map (fun (fst,_,_) -> fst) al) in
      List.fold_right (fun (loc,(patl,rhs)) acc ->
	let ids = ids_of_pattern_list patl in
	f (Id.Set.fold g ids n) acc rhs) bl acc
  | CLetTuple (nal,(ona,po),b,c) ->
      let n' = List.fold_right (Loc.down_located (name_fold g)) nal n in
      f (Option.fold_right (Loc.down_located (name_fold g)) ona n') (f n acc b) c
  | CIf (c,(ona,po),b1,b2) ->
      let acc = f n (f n (f n acc b1) b2) c in
      Option.fold_left
	(f (Option.fold_right (Loc.down_located (name_fold g)) ona n)) acc po
  | CFix (_,l) ->
      let n' = List.fold_right (fun ((_,id),_,_,_,_) -> g id) l n in
      List.fold_right (fun (_,(_,o),lb,t,c) acc ->
	fold_local_binders g f n'
	  (fold_local_binders g f n acc t lb) c lb) l acc
  | CCoFix (_,_) ->
      Feedback.msg_warning (strbrk "Capture check in multiple binders not done"); acc
  )

let free_vars_of_constr_expr c =
  let rec aux bdvars l = function
  | { CAst.v = CRef (Ident (_,id),_) } -> if Id.List.mem id bdvars then l else Id.Set.add id l
  | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] Id.Set.empty c

let occur_var_constr_expr id c = Id.Set.mem id (free_vars_of_constr_expr c)

(* Interpret the index of a recursion order annotation *)

let split_at_annot bl na =
  let names = List.map snd (names_of_local_assums bl) in
  match na with
  | None ->
      begin match names with
      | [] -> error "A fixpoint needs at least one parameter."
      | _ -> ([], bl)
      end
  | Some (loc, id) ->
      let rec aux acc = function
	| CLocalAssum (bls, k, t) as x :: rest ->
            let test (_, na) = match na with
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
	| CLocalDef ((_,na),_,_) as x :: rest ->
           if Name.equal (Name id) na then
             user_err ?loc
               (Nameops.pr_id id ++ str" must be a proper parameter and not a local definition.")
           else
             aux (x :: acc) rest
        | CLocalPattern (_,_) :: rest ->
            Loc.raise ?loc (Stream.Error "pattern with quote not allowed after fix")
	| [] ->
            user_err ?loc 
			 (str "No parameter named " ++ Nameops.pr_id id ++ str".")
      in aux [] bl

(* Used in correctness and interface *)

let map_binder g e nal = List.fold_right (Loc.down_located (name_fold g)) nal e

let map_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (e,bl) (nal,bk,t) = (map_binder g e nal,(nal,bk,f e t)::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_local_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (e,bl) = function
      CLocalAssum(nal,k,ty) ->
        (map_binder g e nal, CLocalAssum(nal,k,f e ty)::bl)
    | CLocalDef((loc,na),c,ty) ->
        (name_fold g na e, CLocalDef((loc,na),f e c,Option.map (f e) ty)::bl)
    | CLocalPattern (loc,(pat,t)) ->
        let ids = ids_of_pattern pat in
        (Id.Set.fold g ids e, CLocalPattern (loc,(pat,Option.map (f e) t))::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_constr_expr_with_binders g f e = CAst.map (function
  | CAppExpl (r,l) -> CAppExpl (r,List.map (f e) l)
  | CApp ((p,a),l) ->
      CApp ((p,f e a),List.map (fun (a,i) -> (f e a,i)) l)
  | CProdN (bl,b) ->
      let (e,bl) = map_binders f g e bl in CProdN (bl,f e b)
  | CLambdaN (bl,b) ->
      let (e,bl) = map_binders f g e bl in CLambdaN (bl,f e b)
  | CLetIn (na,a,t,b) ->
      CLetIn (na,f e a,Option.map (f e) t,f (name_fold g (snd na) e) b)
  | CCast (a,c) -> CCast (f e a, Miscops.map_cast_type (f e) c)
  | CNotation (n,(l,ll,bll)) ->
      (* This is an approximation because we don't know what binds what *)
      CNotation (n,(List.map (f e) l,List.map (List.map (f e)) ll,
                     List.map (fun bl -> snd (map_local_binders f g e bl)) bll))
  | CGeneralization (b,a,c) -> CGeneralization (b,a,f e c)
  | CDelimiters (s,a) -> CDelimiters (s,f e a)
  | CHole _ | CEvar _ | CPatVar _ | CSort _
  | CPrim _ | CRef _ as x -> x
  | CRecord l -> CRecord (List.map (fun (id, c) -> (id, f e c)) l)
  | CCases (sty,rtnpo,a,bl) ->
      let bl = List.map (fun (loc,(patl,rhs)) ->
        let ids = ids_of_pattern_list patl in
        (loc,(patl,f (Id.Set.fold g ids e) rhs))) bl in
      let ids = ids_of_cases_tomatch a in
      let po = Option.map (f (Id.Set.fold g ids e)) rtnpo in
      CCases (sty, po, List.map (fun (tm,x,y) -> f e tm,x,y) a,bl)
  | CLetTuple (nal,(ona,po),b,c) ->
      let e' = List.fold_right (Loc.down_located (name_fold g)) nal e in
      let e'' = Option.fold_right (Loc.down_located (name_fold g)) ona e in
      CLetTuple (nal,(ona,Option.map (f e'') po),f e b,f e' c)
  | CIf (c,(ona,po),b1,b2) ->
      let e' = Option.fold_right (Loc.down_located (name_fold g)) ona e in
      CIf (f e c,(ona,Option.map (f e') po),f e b1,f e b2)
  | CFix (id,dl) ->
      CFix (id,List.map (fun (id,n,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        (* Note: fix names should be inserted before the arguments... *)
        let e'' = List.fold_left (fun e ((_,id),_,_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,n,bl',t',d')) dl)
  | CCoFix (id,dl) ->
      CCoFix (id,List.map (fun (id,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        let e'' = List.fold_left (fun e ((_,id),_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,bl',t',d')) dl)
  )

(* Used in constrintern *)
let rec replace_vars_constr_expr l = function
  | { CAst.loc; v = CRef (Ident (loc_id,id),us) } as x ->
      (try CAst.make ?loc @@ CRef (Ident (loc_id,Id.Map.find id l),us) with Not_found -> x)
  | c -> map_constr_expr_with_binders Id.Map.remove
           replace_vars_constr_expr l c

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

let ntn_loc ?loc (args,argslist,binderslist) =
  locs_of_notation ?loc
    (List.map constr_loc (args@List.flatten argslist)@
     List.map local_binders_loc binderslist)

let patntn_loc ?loc (args,argslist) =
  locs_of_notation ?loc
    (List.map cases_pattern_expr_loc (args@List.flatten argslist))
