
(* $Id$ *)

open Util
open Names
open Generic
open Term

(* Given a term with variables in it, and second-order substitution,
   this function will apply the substitution.  The special
   operator "XTRA[$SOAPP]" is used to represent the second-order
   substitution.

   (1) second-order substitutions: $SOAPP(SOLAM;... soargs ...)
       This operation will take the term SOLAM, which must be
       of the form [x1][x2]...[xn]B and replace the xi with the
       soargs.  If any of the soargs are variables, then we will
       rename the binders for these variables to the name of the
       xi.
 *)

let list_assign_1 l n e = 
  let rec assrec = function 
    | (1, h::t) -> e :: t
    | (n, h::t) -> h :: (assrec (n-1,t))
    | (_, []) -> failwith "list_assign_1"
  in 
  assrec (n,l)
    

(* [propagate_name spine_map argt new_na]
 * if new_na is a real name, and argt is a (Rel idx)
 * then the entry for idx in the spine_map
 * is replaced with new_na.  In any case, a new spine_map is returned.
 *)
let propagate_name smap argt new_na = 
  match argt,new_na with 
    | (Rel idx, (Name _ as na)) ->
	(try list_assign_1 smap idx na with Failure _ -> smap)
    | (_, _) -> smap
	  
let is_soapp_operator = function
  | DOPN(XTRA("$SOAPP",[]),cl) -> true
  | DOP2(XTRA("$SOAPP",[]),_,_) -> true
  | _ -> false
	
let dest_soapp_operator = function
  | DOPN(XTRA("$SOAPP",[]),cl) -> (array_hd cl,array_list_of_tl cl)
  | DOP2(XTRA("$SOAPP",[]),c1,c2) -> (c1,[c2])
  | _ -> failwith "dest_soapp_operator"
	
let solam_names = 
  let rec namrec acc = function
    | DLAM(na,b) -> namrec (na::acc) b
    | _ -> List.rev acc
  in 
  namrec []
    
let do_propsoapp smap (solam,soargs) =
  let rec propsolam smap solam soargs =
    match (solam,soargs) with
      | ((DLAM(na,b)), (arg::argl)) ->
          propsolam (propagate_name smap arg na) b argl
      | ((DLAM _), []) -> error "malformed soapp"
      | (_, (_::_)) -> error "malformed soapp"
      | (_, []) -> smap
  in 
  propsolam smap solam soargs
    
let propsoapp smap t =
  if is_soapp_operator t then
    do_propsoapp smap (dest_soapp_operator t)
  else 
    smap

(* [propagate_names spine_map t]
 * walks t, looking for second-order applications.
 * Each time it finds one, it tries to propagate
 * backwards any names that it can for arguments of
 * the application which are debruijn references.
 *)
let propagate_names = 
  let rec proprec smap t =
    let (smap,t) = 
      (match t with
         | DOP0 oper -> (smap,t)
      	 | DOP1(op,c) ->
             let (smap',c') = proprec smap c in 
	     (smap',DOP1(op,c'))
      	 | DOP2(op,c1,c2) ->
             let (smap',c1') = proprec smap c1 in
             let (smap'',c2') = proprec smap c2 in
             (smap'',DOP2(op,c1',c2'))
      	 | DOPN(op,cl) ->
             let cllist = Array.to_list cl in
             let (smap',cl'list) =
               List.fold_right 
		 (fun c (smap,acc) ->
		    let (smap',c') = proprec smap c in (smap',c'::acc))
            	 cllist (smap,[]) 
	     in
             (smap',DOPN(op,Array.of_list cl'list))
      	 | DOPL(op,cl) ->
             let cllist = cl in
             let (smap',cl'list) =
               List.fold_right 
		 (fun c (smap,acc) ->
		    let (smap',c') = proprec smap c in (smap',c'::acc))
            	 cllist (smap,[]) 
	     in
             (smap',DOPL(op,cl'list))
	 | DLAM(na,c) ->
	     let (lna', c') = proprec (na::smap) c in
	     (List.tl lna', DLAM(List.hd lna', c'))
	 | DLAMV(na,cl) ->
             let cllist = Array.to_list cl in
             let (lna',cl'list) =
               List.fold_right 
		 (fun c (smap,acc) ->
		    let (smap',c') = proprec smap c in (smap',c'::acc))
		 cllist (na::smap,[]) 
	     in 
	     (List.tl lna',DLAMV(List.hd lna',Array.of_list cl'list))
	 | Rel i -> (smap,t)
	 | VAR id -> (smap,t))
    in 
    (propsoapp smap t,t)
  in 
  proprec  
    
let socontract = 
  let rec lamrec sigma x y = 
    match x,y with 
      | (h::t, DLAM(_,c)) -> lamrec (h::sigma) t c
      | ([], t) -> substl sigma t
      | ((_::_), _) -> error "second-order app with mismatched arguments"
  in 
  lamrec [] 

(* [soeval t]
 * evaluates t, by contracting any second-order redexes
 *)
let rec soeval t= 
  match t with
    | DOP0 _ -> t
    | Rel _ -> t
    | VAR _ -> t
    | DOP1(op,c) -> DOP1(op,soeval c)
    | DLAM(na,c) -> DLAM(na,soeval c)
    | DLAMV(na,cl) -> DLAMV(na,Array.map soeval cl)
    | DOP2(op,c1,c2) ->
        let c1' = soeval c1
	and c2' = soeval c2 in 
	if is_soapp_operator t then
          socontract [c2'] c1'
        else 
	  DOP2(op,c1',c2')
    | DOPN(op,cl) ->
        let cl' = Array.map soeval cl in
        if is_soapp_operator t then
	  let lam = array_hd cl' in
	  let args = Array.to_list (array_tl cl') in
          socontract args lam
        else 
	  DOPN(op,cl')
    | DOPL(op,cl) ->
        let cl' = List.map soeval cl in
        if is_soapp_operator t then
	  let lam = List.hd cl'
	  and args = List.tl cl' in
          socontract args lam
	else 
	  DOPL(op,cl')
	    
let rec try_soeval t = 
  match t with
    | DOP0 _ -> t
    | Rel _ -> t
    | VAR _ -> t
    | DOP1(op,c) -> DOP1(op,try_soeval c)
    | DLAM(na,c) -> DLAM(na,try_soeval c)
    | DLAMV(na,cl) -> DLAMV(na,Array.map try_soeval cl)
    | DOP2(op,c1,c2) ->
        let c1' = try_soeval c1
	and c2' = try_soeval c2 in
        if is_soapp_operator t then
          (try socontract [c2'] c1'
           with (Failure _ | UserError _) -> DOP2(op,c1',c2'))
        else 
	  DOP2(op,c1',c2')
    | DOPN(op,cl) ->
        let cl' = Array.map try_soeval cl in
        if is_soapp_operator t then
	  let lam = array_hd cl'
	  and args = Array.to_list (array_tl cl') in
          (try socontract args lam
           with (Failure _ | UserError _) -> DOPN(op,cl'))
        else 
	  DOPN(op,cl')
    | DOPL(op,cl) ->
        let cl' = List.map try_soeval cl in
        if is_soapp_operator t then
	  let lam = List.hd cl'
	  and args = List.tl cl' in
          (try socontract args lam
           with (Failure _ | UserError _) -> DOPL(op,cl'))
        else 
	  DOPL(op,cl')
	    
let soexecute t =
  let (_,t) = propagate_names [] t in 
  soeval t

let try_soexecute t =
  let (_,t) = 
    try propagate_names [] t
    with (Failure _ | UserError _) -> ([],t)
  in 
  try_soeval t
