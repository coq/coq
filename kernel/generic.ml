
(* $Id$ *)

open Util
open Pp
open Names

(********************************************************************)
(*           Generic syntax of terms with de Bruijn indexes         *)
(********************************************************************)

type 'oper term =
  | DOP0 of 'oper                            (* atomic terms *)
  | DOP1 of 'oper * 'oper term               (* operator of arity 1 *)
  | DOP2 of 'oper * 'oper term * 'oper term  (* operator of arity 2 *)
  | DOPN of 'oper * 'oper term array         (* operator of variadic arity *)
  | DOPL of 'oper * 'oper term list          (* operator of variadic arity *)
  | DLAM of name * 'oper term                (* deBruijn binder on one term*)
  | DLAMV of name * 'oper term array         (* deBruijn binder on many terms*)
  | VAR of identifier                        (* named variable *)
  | Rel of int                               (* variable as deBruijn index *)

exception FreeVar
exception Occur

let isRel = function Rel _ -> true | _ -> false
let isVAR = function VAR _ -> true | _ -> false

(* returns the list of free debruijn indices in a term *)

let free_rels m = 
  let rec frec depth acc = function
    | Rel n         -> if n >= depth then Intset.add (n-depth+1) acc else acc
    | DOPN(_,cl)    -> Array.fold_left (frec depth) acc cl
    | DOPL(_,cl)    -> List.fold_left (frec depth) acc cl
    | DOP2(_,c1,c2) -> frec depth (frec depth acc c1) c2
    | DOP1(_,c)     -> frec depth acc c
    | DLAM(_,c)     -> frec (depth+1) acc c
    | DLAMV(_,cl)   -> Array.fold_left (frec (depth+1)) acc cl
    | VAR _         -> acc
    | DOP0 _        -> acc
  in 
  frec 1 Intset.empty m

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn = 
  let rec closed_rec n = function
    | Rel(m)        -> if m>n then raise FreeVar
    | VAR _         -> ()
    | DOPN(_,cl)    -> Array.iter (closed_rec n) cl
    | DOPL(_,cl)    -> List.iter (closed_rec n) cl
    | DOP2(_,c1,c2) -> closed_rec n c1; closed_rec n c2
    | DOP1(_,c)     -> closed_rec n c
    | DLAM(_,c)     -> closed_rec (n+1) c
    | DLAMV(_,v)    -> Array.iter (closed_rec (n+1)) v
    | _             -> ()
  in 
  closed_rec

(* (closed M) is true iff M is a (deBruijn) closed term *)

let closed0 term =
  try closedn 0 term; true with FreeVar -> false

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term = 
  let rec occur_rec n = function
    | Rel(m)        -> if m = n then raise Occur
    | VAR _         -> ()
    | DOPN(_,cl)    -> Array.iter (occur_rec n) cl
    | DOPL(_,cl)    -> List.iter (occur_rec n) cl
    | DOP1(_,c)     -> occur_rec n c
    | DOP2(_,c1,c2) -> occur_rec n c1; occur_rec n c2
    | DLAM(_,c)     -> occur_rec (n+1) c
    | DLAMV(_,v)    -> Array.iter (occur_rec (n+1)) v
    | _             -> ()
  in 
  try occur_rec n term; true with Occur -> false

(* (noccur_bet n m M) returns true iff (Rel p) does NOT occur in term M 
  for n <= p < n+m *)

let noccur_bet n m term = 
  let rec occur_rec n = function
    | Rel(p)        -> if n<=p && p<n+m then raise Occur
    | VAR _         -> ()
    | DOPN(_,cl)    -> Array.iter (occur_rec n) cl
    | DOPL(_,cl)    -> List.iter (occur_rec n) cl
    | DOP1(_,c)     -> occur_rec n c
    | DOP2(_,c1,c2) -> occur_rec n c1; occur_rec n c2
    | DLAM(_,c)     -> occur_rec (n+1) c
    | DLAMV(_,v)    -> Array.iter (occur_rec (n+1)) v
    | _             -> ()
  in 
  try occur_rec n term; true with Occur -> false

(* Explicit lifts and basic operations *)
type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int (* ELSHFT(l,n) == lift of n, then apply lift l *)
  | ELLFT of int * lift_spec  (* ELLFT(n,l)  == apply l to de Bruijn > n *)
                            (*                 i.e under n binders *)

(* compose a relocation of magnitude n *)
let rec el_shft n = function
  | ELSHFT(el,k) -> el_shft (k+n) el
  | el -> if n = 0 then el else ELSHFT(el,n)


(* cross n binders *)
let rec el_liftn n = function
  | ELID -> ELID
  | ELLFT(k,el) -> el_liftn (n+k) el
  | el -> if n=0 then el else ELLFT(n, el)

let el_lift el = el_liftn 1 el

(* relocation of de Bruijn n in an explicit lift *)
let rec reloc_rel n = function
  | ELID -> n
  | ELLFT(k,el) ->
      if n <= k then n else (reloc_rel (n-k) el) + k
  | ELSHFT(el,k) -> (reloc_rel (n+k) el)


(* The generic lifting function *)
let rec exliftn el = function
  | Rel i            -> Rel(reloc_rel i el)
  | DOPN(oper,cl)    -> DOPN(oper, Array.map (exliftn el) cl)
  | DOPL(oper,cl)    -> DOPL(oper, List.map (exliftn el) cl)
  | DOP1(oper,c)     -> DOP1(oper, exliftn el c)
  | DOP2(oper,c1,c2) -> DOP2(oper, exliftn el c1, exliftn el c2)
  | DLAM(na,c)       -> DLAM(na, exliftn (el_lift el) c)
  | DLAMV(na,v)      -> DLAMV(na, Array.map (exliftn (el_lift el)) v)
  | x                -> x


(* Lifting the binding depth across k bindings *)

let liftn k n = 
  match el_liftn (pred n) (el_shft k ELID) with
    | ELID -> (fun c -> c)
    | el -> exliftn el
 
let lift k = liftn k 1
let lift1 c = exliftn (ELSHFT(ELID,1)) c


(* explicit substitutions of type 'a *)
type 'a subs =
  | ESID                   (* ESID       =          identity *)
  | CONS of 'a * 'a subs   (* CONS(t,S)  = (S.t)    parallel substitution *)
  | SHIFT of int * 'a subs (* SHIFT(n,S) = (^n o S) terms in S are relocated *)
                           (*                        with n vars *)
  | LIFT of int * 'a subs  (* LIFT(n,S) = (%n S) stands for ((^n o S).n...1) *)

(* operations of subs: collapses constructors when possible.
 * Needn't be recursive if we always use these functions
 *)
let subs_cons(x,s) = CONS(x,s)

let subs_lift = function
  | ESID -> ESID         (* the identity lifted is still the identity *)
                         (* (because (^1.1) --> id) *)
  | LIFT (n,lenv) -> LIFT (n+1, lenv)
  | lenv -> LIFT (1,lenv)

let subs_shft = function
  | (0, s)            -> s
  | (n, SHIFT (k,s1)) -> SHIFT (k+n, s1)
  | (n, s)            -> SHIFT (n,s)


(* Expands de Bruijn k in the explicit substitution subs
 * lams accumulates de shifts to perform when retrieving the i-th value
 * the rules used are the following:
 *
 *    [id]k       --> k
 *    [S.t]1      --> t
 *    [S.t]k      --> [S](k-1)  if k > 1
 *    [^n o S] k  --> [^n]([S]k)
 *    [(%n S)] k  --> k         if k <= n
 *    [(%n S)] k  --> [^n]([S](k-n))
 *
 * the result is (Inr k) when the variable is just relocated
 *) 
let rec exp_rel lams k subs =
  match (k,subs) with
    | (1, CONS (def,_)) -> Inl(lams,def)
    | (_, CONS (_,l)) -> exp_rel lams (pred k) l
    | (_, LIFT (n,_)) when k<=n -> Inr(lams+k)
    | (_, LIFT (n,l)) -> exp_rel (n+lams) (k-n) l
    | (_, SHIFT (n,s)) -> exp_rel (n+lams) k s
    | (_, ESID) -> Inr(lams+k)

let expand_rel k subs = exp_rel 0 k subs


(* (subst1 M c) substitutes M for Rel(1) in c 
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let rec lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
        s.sinfo <- if closed0 s.sit then Closed else Open;
        lift_substituend depth s

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n =
  let lv = Array.length lamv in 
  let rec substrec depth = function 
    | Rel k as x     ->
        if k<=depth then 
	  x
        else if k-depth <= lv then
          lift_substituend depth lamv.(k-depth-1)
        else 
	  Rel (k-lv)
    | VAR id           -> VAR id
    | DOPN(oper,cl)    -> DOPN(oper,Array.map (substrec depth) cl)
    | DOPL(oper,cl)    -> DOPL(oper,List.map (substrec depth) cl)
    | DOP1(oper,c)     -> DOP1(oper,substrec depth c)
    | DOP2(oper,c1,c2) -> DOP2(oper,substrec depth c1,substrec depth c2)
    | DLAM(na,c)       -> DLAM(na,substrec (depth+1) c)
    | DLAMV(na,v)      -> DLAMV(na,Array.map (substrec (depth+1)) v)
    | x                -> x
  in 
  substrec n

let substl laml =
  substn_many (Array.map make_substituend (Array.of_list laml)) 0
let subst1 lam = substl [lam]
let pop t = lift (-1) t


(* Various occurs checks *)

let occur_opern s = 
  let rec occur_rec = function
    | DOPN(oper,cl) -> s=oper or (array_exists occur_rec cl)
    | DOPL(oper,cl) -> s=oper or (List.exists occur_rec cl)
    | VAR _         -> false
    | DOP1(_,c)     -> occur_rec c 
    | DOP2(_,c1,c2) -> (occur_rec c1) or (occur_rec c2)
    | DLAM(_,c)     -> occur_rec c
    | DLAMV(_,v)    -> array_exists occur_rec v
    | _             -> false
  in 
  occur_rec 

let occur_oper0 s = 
  let rec occur_rec = function
    | DOPN(_,cl)    -> (array_exists occur_rec cl)
    | DOPL(_,cl)    -> (List.exists occur_rec cl)
    | DOP0 oper     -> s=oper
    | VAR _         -> false
    | DOP1(_,c)     -> occur_rec c 
    | DOP2(_,c1,c2) -> (occur_rec c1) or (occur_rec c2)
    | DLAM(_,c)     -> occur_rec c
    | DLAMV(_,v)    -> array_exists occur_rec v
    | _             -> false
  in 
  occur_rec 

let occur_var s = 
  let rec occur_rec = function
    | DOPN(_,cl)    -> array_exists occur_rec cl
    | DOPL(_,cl)    -> List.exists occur_rec cl
    | VAR id        -> s=id
    | DOP1(_,c)     -> occur_rec c 
    | DOP2(_,c1,c2) -> (occur_rec c1) or (occur_rec c2)
    | DLAM(_,c)     -> occur_rec c
    | DLAMV(_,v)    -> array_exists occur_rec v
    | _             -> false
  in 
  occur_rec 

let occur_oper s = 
  let rec occur_rec = function
    | DOPN(oper,cl)    -> s=oper or (array_exists occur_rec cl)
    | DOPL(oper,cl)    -> s=oper or (List.exists occur_rec cl)
    | VAR _            -> false
    | DOP0 oper        -> s=oper
    | DOP1(oper,c)     -> s=oper or occur_rec c 
    | DOP2(oper,c1,c2) -> s=oper or (occur_rec c1) or (occur_rec c2)
    | DLAM(_,c)        -> occur_rec c
    | DLAMV(_,v)       -> array_exists occur_rec v
    | _                -> false
  in 
  occur_rec 

(* Returns the list of global variables in a term *)

let global_varsl l constr = 
  let rec filtrec acc = function
    | VAR id             -> id::acc
    | DOP1(oper,c)       -> filtrec acc c
    | DOP2(oper,c1,c2)   -> filtrec (filtrec acc c1) c2
    | DOPN(oper,cl)      -> Array.fold_left filtrec acc cl
    | DOPL(oper,cl)      -> List.fold_left filtrec acc cl
    | DLAM(_,c)          -> filtrec acc c
    | DLAMV(_,v)         -> Array.fold_left filtrec acc v
    | _                  -> acc
  in 
  filtrec l constr

let global_vars constr = global_varsl [] constr

let global_vars_set constr = 
  List.fold_left (fun s x -> Idset.add x s) Idset.empty (global_vars constr)

(* alpha equality for generic terms : checks first if M and M' are equal,
   otherwise checks equality forgetting the name annotation of DLAM and DLAMV*)

let rec eq_term m m' =
     (m == m') 
  or (m = m')
  or (match (m,m') with
	| (DOP1(oper1,c1),DOP1(oper2,c2)) ->
            oper1 = oper2 & eq_term c1 c2
	| (DOP2(oper1,c1,t1),DOP2(oper2,c2,t2)) ->
            oper1 = oper2 & eq_term c1 c2 & eq_term t1 t2
	| (DOPN(oper1,cl1),DOPN(oper2,cl2)) ->
            oper1 = oper2 & array_for_all2 eq_term cl1 cl2
	| (DOPL(oper1,cl1),DOPL(oper2,cl2)) ->
            oper1 = oper2 & List.for_all2 eq_term cl1 cl2
	| (DLAM(_,c1),DLAM(_,c2)) -> eq_term c1 c2
	| (DLAMV(_,cl1),DLAMV(_,cl2)) -> array_for_all2 eq_term cl1 cl2
	| _ -> false)

(* (dependent M N) is true iff M is eq_term with a subterm of N 
   M is appropriately lifted through abstractions of N *)
let dependent =
  let rec deprec m = function t ->
       (eq_term m t)
    or (match t with
	  | VAR _       -> false
	  | DOP1(_,c)   -> deprec m c
	  | DOP2(_,c,t) -> deprec m c or deprec m t
	  | DOPN(_,cl)  -> array_exists (deprec m) cl
	  | DOPL(_,cl)  -> List.exists (deprec m) cl
	  | DLAM(_,c)   -> deprec (lift1 m) c
	  | DLAMV(_,v)  -> array_exists (deprec (lift1 m)) v
	  | _ -> false)
  in 
  deprec

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (((id,{sit=VAR id'}) as s)::tl) -> 
      if id = id' then thin_val tl else s::(thin_val tl)
  | h::tl -> h::(thin_val tl)

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist = 
  let var_alist = thin_val var_alist in 
  let rec substrec n = function
    | (VAR(x) as c)    ->
        (try lift_substituend n (List.assoc x var_alist)
         with Not_found -> c)
	
    | DOPN(oper,cl)    -> DOPN(oper,Array.map (substrec n) cl)
    | DOPL(oper,cl)    -> DOPL(oper,List.map (substrec n) cl)
    | DOP1(oper,c)     -> DOP1(oper,substrec n c)
    | DOP2(oper,c1,c2) -> DOP2(oper,substrec n c1,substrec n c2)
    | DLAM(na,c)       -> DLAM(na,substrec (n+1) c)
    | DLAMV(na,v)      -> DLAMV(na,Array.map (substrec (n+1)) v)
    | x                -> x
  in 
  if var_alist = [] then (function x -> x) else substrec 0

let subst_varn str n = replace_vars [(str,make_substituend (Rel n))]

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = subst_varn str 1


(* renames different  ocurrences of (VAR id) in t with a fresh identifier
   wrt. acc *)
let rename_diff_occ  id acc t =
  let rec rename_occ acc  = function
    | (VAR(x)  as c) -> 
	if x <> id then 
	  acc,c
        else 
	  let nid = next_ident_away id acc in (nid::acc), (VAR nid)
    | DOPN(oper,cl) -> 
	let nacc,ncl = vrename_occ acc  cl in nacc,DOPN(oper, ncl)
    | DOPL(oper,cl) -> 
	let nacc,ncl = lrename_occ acc cl in nacc, DOPL(oper,ncl)
    | DOP1(oper,c) ->
	let nacc,nc = rename_occ acc c in nacc, DOP1(oper,nc)
    | DOP2(oper,c1,c2) -> 
	let nacc,nc1 = rename_occ acc c1 in
        let nacc2,nc2 = rename_occ   nacc c2 in
        nacc2, DOP2(oper,nc1,nc2) 
    | DLAM(na,c) -> 
	let nacc,nc = rename_occ acc c in (nacc, DLAM(na,nc))
    | DLAMV(na,v) -> 
	let nacc,nv = vrename_occ acc v in (nacc, DLAMV(na, nv))
    | x -> acc,x
  and lrename_occ acc = function
    | [] -> acc,[]
    | (t::lt) -> 
	let nacc,nt = rename_occ acc t in
        let nacc2,nlt = lrename_occ nacc lt
        in nacc2,(nt::nlt)
  and vrename_occ acc v = 
    let nacc,nl = lrename_occ acc (Array.to_list v)
    in nacc, Array.of_list nl
  in 
  rename_occ acc t


let sAPP c n =
  match c with 
    | DLAM(na,m) -> subst1 n m
    | _ -> invalid_arg "SAPP"
	  
let sAPPV c n =
  match c with
    | DLAMV(na,mV) -> Array.map (subst1 n) mV
    | _ -> invalid_arg "SAPPV"

let sAPPVi i c n =
  match c with
    | DLAMV(na,mV) -> subst1 n mV.(i)
    | _ -> invalid_arg "SAPPVi"

let sAPPList constr cl = 
  let rec srec stack = function
    | (DLAM(_,c), (h::t)) -> srec (h::stack) (c,t)
    | (c,         [])     -> substl stack c
    | (_,         _)      -> failwith "SAPPList"
  in 
  srec [] (constr,cl) 

let sAPPVList constr cl = 
  let rec srec stack = function
    | (DLAM(_,c), (h::t)) -> srec (h::stack) (c,t)
    | (DLAMV(_,c), [h])   -> Array.map (substl (h::stack)) c
    | (_,             _)  -> failwith "SAPPVList"
  in 
  srec [] (constr,cl) 

let sAPPViList i constr cl= 
  let rec srec stack = function
    | (DLAM(_,c), (h::t)) -> srec (h::stack) (c,t)
    | (DLAMV(_,c), [h])   -> substl (h::stack) c.(i)
    | (_,             _)  -> failwith "SAPPViList"
  in 
  srec [] (constr,cl)

let under_dlams f = 
  let rec apprec = function 
    | DLAMV(na,c) -> DLAMV(na,Array.map f c)
    | DLAM(na,c)  -> DLAM(na,apprec c)
    | _           -> failwith "under_dlams"
  in 
  apprec 


(* utility for discharge *)
type modification_action = ABSTRACT | ERASE

let interp_modif absfun oper (oper',modif) cl = 
  let rec interprec = function
    | ([], cl) -> DOPN(oper',Array.of_list cl)
    | (ERASE::tlm, c::cl) -> interprec (tlm,cl)
    | (ABSTRACT::tlm, c::cl) -> absfun (interprec (tlm,cl)) c
    | _ -> assert false
  in 
  interprec (modif,cl)


type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * modification_action list
  | DO_REPLACE

let modify_opers replfun absfun oper_alist =
  let failure () =
    anomalylabstrm "generic__modify_opers"
      [< 'sTR"An oper which was never supposed to appear has just appeared" ;
         'sPC ; 'sTR"Either this is in system code, and you need to" ; 'sPC;
         'sTR"report this error," ; 'sPC ;
         'sTR"Or you are using a user-written tactic which calls" ; 'sPC ;
         'sTR"generic__modify_opers, in which case the user-written code" ;
         'sPC ; 'sTR"is broken - this function is an internal system" ;
         'sPC ; 'sTR"for internal system use only" >]
  in
  let rec substrec = function
    | DOPN(oper,cl) as c ->
	let cl' = Array.map substrec cl in
	(try
	   (match List.assoc oper oper_alist with
	      | NOT_OCCUR -> failure ()
	      | DO_ABSTRACT (oper',modif) ->
		  if List.length modif > Array.length cl then
		    anomaly "found a reference with too few args"
		  else 
		    interp_modif absfun oper (oper',modif) (Array.to_list cl')
	      | DO_REPLACE -> substrec (replfun (DOPN(oper,cl'))))
	 with 
	   | Not_found -> DOPN(oper,cl'))
    | DOP1(i,c) -> DOP1(i,substrec c)
    | DOPL(oper,cl) -> DOPL(oper,List.map substrec cl)
    | DOP2(oper,c1,c2) -> DOP2(oper,substrec c1,substrec c2)
    | DLAM(na,c) -> DLAM(na,substrec c)
    | DLAMV(na,v) -> DLAMV(na,Array.map substrec v)
    | x -> x
  in 
  if oper_alist = [] then fun x -> x else substrec

let put_DLAMSV lna lc = 
  match lna with 
    | [] -> anomaly "put_DLAM"
    | na::lrest -> List.fold_left (fun c na -> DLAM(na,c)) (DLAMV(na,lc)) lrest

let put_DLAMSV_subst lid lc = 
  match lid with
    | [] -> anomaly "put_DLAM"
    | id::lrest ->  
        List.fold_left (fun c id' -> DLAM(Name id',subst_var id' c)) 
          (DLAMV(Name id,Array.map (subst_var id) lc)) lrest

let rec decomp_DLAMV n = function 
  | DLAM(_,lc)  -> decomp_DLAMV (n-1) lc
  | DLAMV(_,lc) -> if n = 1 then lc else error "decomp_DLAMV 0"
  | _           -> error "decomp_DLAMV 1"

let decomp_DLAMV_name n = 
  let rec decomprec lna n = function 
    | DLAM(na,lc)  -> decomprec (na::lna) (pred n) lc
    | DLAMV(na,lc) -> if n = 1 then (na::lna,lc) else error "decomp_DLAMV 0"
    | _           -> error "decomp_DLAMV 1"
  in 
  decomprec [] n 

let decomp_all_DLAMV_name constr = 
  let rec decomprec lna = function 
    | DLAM(na,lc)  -> decomprec (na::lna) lc
    | DLAMV(na,lc) -> (na::lna,lc)
    | _ -> assert false
  in 
  decomprec [] constr
  

(* [Rel (n+m);...;Rel(n+1)] *)

let rel_vect n m = Array.init m (fun i -> Rel(n+m-i))

let rel_list n m = 
  let rec reln l p = 
    if p>m then l else reln (Rel(n+p)::l) (p+1)
  in 
  reln [] 1

let rec count_dlam = function
  | DLAM (_,c) -> 1 + (count_dlam c)
  | _ -> 0

(* Hash-consing *)
let comp_term t1 t2 =
  match (t1,t2) with
    | (DOP0 o1, DOP0 o2) -> o1==o2
    | (DOP1(o1,t1), DOP1(o2,t2)) -> o1==o2 & t1==t2
    | (DOP2(o1,t1,u1), DOP2(o2,t2,u2)) -> o1==o2 & t1==t2 & u1==u2
    | (DOPN(o1,v1), DOPN(o2,v2)) ->
        (o1==o2) & (Array.length v1 = Array.length v2)
        & array_for_all2 (==) v1 v2
    | (DOPL(o1,l1), DOPL(o2,l2)) ->
        (o1==o2) & (List.length l1 = List.length l2)
        & List.for_all2 (==) l1 l2
    | (DLAM(x1,t1), DLAM(x2,t2)) -> x1==x2 & t1==t2
    | (DLAMV(x1,v1), DLAMV(x2,v2)) ->
        (x1==x2) & (Array.length v1 = Array.length v2)
        & array_for_all2 (==) v1 v2
    | (Rel i, Rel j) -> i=j
    | (VAR x, VAR y) -> x==y
    | _ -> false

let hash_term (sh_rec,(sh_op,sh_na,sh_id)) t =
  match t with
    | DOP0 o -> DOP0 (sh_op o)
    | DOP1(o,t) -> DOP1(sh_op o, sh_rec t)
    | DOP2(o,t1,t2) -> DOP2(sh_op o, sh_rec t1, sh_rec t2)
    | DOPN(o,v) -> DOPN(sh_op o, Array.map sh_rec v)
    | DOPL(o,l) -> DOPL(sh_op o, List.map sh_rec l)
    | DLAM(n,t) -> DLAM(sh_na n, sh_rec t)
    | DLAMV(n,v) -> DLAMV(sh_na n, Array.map sh_rec v)
    | Rel i -> t
    | VAR x -> VAR (sh_id x) 
