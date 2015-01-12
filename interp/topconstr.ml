(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Pp
open Errors
open Util
open Names
open Nameops
open Libnames
open Misctypes
open Constrexpr
open Constrexpr_ops
(*i*)


let oldfashion_patterns = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; Goptions.optdepr = false;
  Goptions.optname =
    "Constructors in patterns require all their arguments but no parameters instead of explicit parameters and arguments";
  Goptions.optkey = ["Asymmetric";"Patterns"];
  Goptions.optread = (fun () -> !oldfashion_patterns);
  Goptions.optwrite = (fun a -> oldfashion_patterns:=a);
}

(**********************************************************************)
(* Miscellaneous *)

let error_invalid_pattern_notation loc =
  user_err_loc (loc,"",str "Invalid notation for pattern.")

(**********************************************************************)
(* Functions on constr_expr *)

let ids_of_cases_indtype =
  let rec vars_of ids = function
    (* We deal only with the regular cases *)
    | (CPatCstr (_,_,l1,l2)|CPatNotation (_,_,(l1,[]),l2)) ->
      List.fold_left vars_of (List.fold_left vars_of [] l2) l1
    (* assume the ntn is applicative and does not instantiate the head !! *)
    | CPatDelimiters(_,_,c) -> vars_of ids c
    | CPatAtom (_, Some (Libnames.Ident (_, x))) -> x::ids
    | _ -> ids in
  vars_of []

let ids_of_cases_tomatch tms =
  List.fold_right
    (fun (_,(ona,indnal)) l ->
      Option.fold_right (fun t -> (@) (ids_of_cases_indtype t))
      indnal (Option.fold_right (Loc.down_located name_cons) ona l))
    tms []

let is_constructor id =
  try ignore (Nametab.locate_extended (qualid_of_ident id)); true
  with Not_found -> true

let rec cases_pattern_fold_names f a = function
  | CPatRecord (_, l) ->
      List.fold_left (fun acc (r, cp) -> cases_pattern_fold_names f acc cp) a l
  | CPatAlias (_,pat,id) -> f id a
  | CPatOr (_,patl) ->
      List.fold_left (cases_pattern_fold_names f) a patl
  | CPatCstr (_,_,patl1,patl2) ->
    List.fold_left (cases_pattern_fold_names f)
      (List.fold_left (cases_pattern_fold_names f) a patl1) patl2
  | CPatNotation (_,_,(patl,patll),patl') ->
      List.fold_left (cases_pattern_fold_names f)
	(List.fold_left (cases_pattern_fold_names f) a (patl@List.flatten patll)) patl'
  | CPatDelimiters (_,_,pat) -> cases_pattern_fold_names f a pat
  | CPatAtom (_,Some (Ident (_,id))) when not (is_constructor id) -> f id a
  | CPatPrim _ | CPatAtom _ -> a

let ids_of_pattern_list =
  List.fold_left
    (Loc.located_fold_left
      (List.fold_left (cases_pattern_fold_names Id.Set.add)))
    Id.Set.empty

let rec fold_constr_expr_binders g f n acc b = function
  | (nal,bk,t)::l ->
      let nal = snd (List.split nal) in
      let n' = List.fold_right (name_fold g) nal n in
      f n (fold_constr_expr_binders g f n' acc b l) t
  | [] ->
      f n acc b

let rec fold_local_binders g f n acc b = function
  | LocalRawAssum (nal,bk,t)::l ->
      let nal = snd (List.split nal) in
      let n' = List.fold_right (name_fold g) nal n in
      f n (fold_local_binders g f n' acc b l) t
  | LocalRawDef ((_,na),t)::l ->
      f n (fold_local_binders g f (name_fold g na n) acc b l) t
  | [] ->
      f n acc b

let fold_constr_expr_with_binders g f n acc = function
  | CAppExpl (loc,(_,_,_),l) -> List.fold_left (f n) acc l
  | CApp (loc,(_,t),l) -> List.fold_left (f n) (f n acc t) (List.map fst l)
  | CProdN (_,l,b) | CLambdaN (_,l,b) -> fold_constr_expr_binders g f n acc b l
  | CLetIn (_,na,a,b) -> fold_constr_expr_binders g f n acc b [[na],default_binder_kind,a]
  | CCast (loc,a,(CastConv b|CastVM b|CastNative b)) -> f n (f n acc a) b
  | CCast (loc,a,CastCoerce) -> f n acc a
  | CNotation (_,_,(l,ll,bll)) ->
      (* The following is an approximation: we don't know exactly if
         an ident is binding nor to which subterms bindings apply *)
      let acc = List.fold_left (f n) acc (l@List.flatten ll) in
      List.fold_left (fun acc bl -> fold_local_binders g f n acc (CHole (Loc.ghost,None,IntroAnonymous,None)) bl) acc bll
  | CGeneralization (_,_,_,c) -> f n acc c
  | CDelimiters (loc,_,a) -> f n acc a
  | CHole _ | CEvar _ | CPatVar _ | CSort _ | CPrim _ | CRef _ ->
      acc
  | CRecord (loc,_,l) -> List.fold_left (fun acc (id, c) -> f n acc c) acc l
  | CCases (loc,sty,rtnpo,al,bl) ->
      let ids = ids_of_cases_tomatch al in
      let acc = Option.fold_left (f (List.fold_right g ids n)) acc rtnpo in
      let acc = List.fold_left (f n) acc (List.map fst al) in
      List.fold_right (fun (loc,patl,rhs) acc ->
	let ids = ids_of_pattern_list patl in
	f (Id.Set.fold g ids n) acc rhs) bl acc
  | CLetTuple (loc,nal,(ona,po),b,c) ->
      let n' = List.fold_right (Loc.down_located (name_fold g)) nal n in
      f (Option.fold_right (Loc.down_located (name_fold g)) ona n') (f n acc b) c
  | CIf (_,c,(ona,po),b1,b2) ->
      let acc = f n (f n (f n acc b1) b2) c in
      Option.fold_left
	(f (Option.fold_right (Loc.down_located (name_fold g)) ona n)) acc po
  | CFix (loc,_,l) ->
      let n' = List.fold_right (fun ((_,id),_,_,_,_) -> g id) l n in
      List.fold_right (fun (_,(_,o),lb,t,c) acc ->
	fold_local_binders g f n'
	  (fold_local_binders g f n acc t lb) c lb) l acc
  | CCoFix (loc,_,_) ->
      msg_warning (strbrk "Capture check in multiple binders not done"); acc

let free_vars_of_constr_expr c =
  let rec aux bdvars l = function
  | CRef (Ident (_,id),_) -> if Id.List.mem id bdvars then l else Id.Set.add id l
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
	| LocalRawAssum (bls, k, t) as x :: rest ->
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
              | _ -> LocalRawAssum (l, k, t) :: acc
              in
              (List.rev ans, LocalRawAssum (r, k, t) :: rest)
            end
	| LocalRawDef _ as x :: rest -> aux (x :: acc) rest
	| [] ->
            user_err_loc(loc,"",
			 str "No parameter named " ++ Nameops.pr_id id ++ str".")
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
      LocalRawAssum(nal,k,ty) ->
        (map_binder g e nal, LocalRawAssum(nal,k,f e ty)::bl)
    | LocalRawDef((loc,na),ty) ->
        (name_fold g na e, LocalRawDef((loc,na),f e ty)::bl) in
  let (e,rbl) = List.fold_left h (e,[]) bl in
  (e, List.rev rbl)

let map_constr_expr_with_binders g f e = function
  | CAppExpl (loc,r,l) -> CAppExpl (loc,r,List.map (f e) l)
  | CApp (loc,(p,a),l) ->
      CApp (loc,(p,f e a),List.map (fun (a,i) -> (f e a,i)) l)
  | CProdN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CProdN (loc,bl,f e b)
  | CLambdaN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CLambdaN (loc,bl,f e b)
  | CLetIn (loc,na,a,b) -> CLetIn (loc,na,f e a,f (name_fold g (snd na) e) b)
  | CCast (loc,a,c) -> CCast (loc,f e a, Miscops.map_cast_type (f e) c)
  | CNotation (loc,n,(l,ll,bll)) ->
      (* This is an approximation because we don't know what binds what *)
      CNotation (loc,n,(List.map (f e) l,List.map (List.map (f e)) ll,
                     List.map (fun bl -> snd (map_local_binders f g e bl)) bll))
  | CGeneralization (loc,b,a,c) -> CGeneralization (loc,b,a,f e c)
  | CDelimiters (loc,s,a) -> CDelimiters (loc,s,f e a)
  | CHole _ | CEvar _ | CPatVar _ | CSort _
  | CPrim _ | CRef _ as x -> x
  | CRecord (loc,p,l) -> CRecord (loc,p,List.map (fun (id, c) -> (id, f e c)) l)
  | CCases (loc,sty,rtnpo,a,bl) ->
      (* TODO: apply g on the binding variables in pat... *)
      let bl = List.map (fun (loc,pat,rhs) -> (loc,pat,f e rhs)) bl in
      let ids = ids_of_cases_tomatch a in
      let po = Option.map (f (List.fold_right g ids e)) rtnpo in
      CCases (loc, sty, po, List.map (fun (tm,x) -> (f e tm,x)) a,bl)
  | CLetTuple (loc,nal,(ona,po),b,c) ->
      let e' = List.fold_right (Loc.down_located (name_fold g)) nal e in
      let e'' = Option.fold_right (Loc.down_located (name_fold g)) ona e in
      CLetTuple (loc,nal,(ona,Option.map (f e'') po),f e b,f e' c)
  | CIf (loc,c,(ona,po),b1,b2) ->
      let e' = Option.fold_right (Loc.down_located (name_fold g)) ona e in
      CIf (loc,f e c,(ona,Option.map (f e') po),f e b1,f e b2)
  | CFix (loc,id,dl) ->
      CFix (loc,id,List.map (fun (id,n,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        (* Note: fix names should be inserted before the arguments... *)
        let e'' = List.fold_left (fun e ((_,id),_,_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,n,bl',t',d')) dl)
  | CCoFix (loc,id,dl) ->
      CCoFix (loc,id,List.map (fun (id,bl,t,d) ->
        let (e',bl') = map_local_binders f g e bl in
        let t' = f e' t in
        let e'' = List.fold_left (fun e ((_,id),_,_,_) -> g id e) e' dl in
        let d' = f e'' d in
        (id,bl',t',d')) dl)

(* Used in constrintern *)
let rec replace_vars_constr_expr l = function
  | CRef (Ident (loc,id),us) as x ->
      (try CRef (Ident (loc,Id.Map.find id l),us) with Not_found -> x)
  | c -> map_constr_expr_with_binders Id.Map.remove
           replace_vars_constr_expr l c

(* Returns the ranges of locs of the notation that are not occupied by args  *)
(* and which are then occupied by proper symbols of the notation (or spaces) *)

let locs_of_notation loc locs ntn =
  let (bl, el) = Loc.unloc loc in
  let locs =  List.map Loc.unloc locs in
  let rec aux pos = function
    | [] -> if Int.equal pos el then [] else [(pos,el)]
    | (ba,ea)::l -> if Int.equal pos ba then aux ea l else (pos,ba)::aux ea l
  in aux bl (List.sort (fun l1 l2 -> fst l1 - fst l2) locs)

let ntn_loc loc (args,argslist,binderslist) =
  locs_of_notation loc
    (List.map constr_loc (args@List.flatten argslist)@
     List.map local_binders_loc binderslist)

let patntn_loc loc (args,argslist) =
  locs_of_notation loc
    (List.map cases_pattern_expr_loc (args@List.flatten argslist))
