
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

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

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

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M 
  for n <= p < n+m *)

let noccur_between n m term = 
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

let pop t = lift (-1) t

let lift_context n l = 
  let k = List.length l in 
  list_map_i (fun i (name,c) -> (name,liftn n (k-i) c)) 0 l

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

let substnl laml k =
  substn_many (Array.map make_substituend (Array.of_list laml)) k
let substl laml =
  substn_many (Array.map make_substituend (Array.of_list laml)) 0
let subst1 lam = substl [lam]

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
  let rec filtrec acc = function
    | VAR id             -> Idset.add id acc
    | DOP1(oper,c)       -> filtrec acc c
    | DOP2(oper,c1,c2)   -> filtrec (filtrec acc c1) c2
    | DOPN(oper,cl)      -> Array.fold_left filtrec acc cl
    | DOPL(oper,cl)      -> List.fold_left filtrec acc cl
    | DLAM(_,c)          -> filtrec acc c
    | DLAMV(_,v)         -> Array.fold_left filtrec acc v
    | _                  -> acc
  in 
  filtrec Idset.empty constr

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (((id,{sit=VAR id'}) as s)::tl) -> 
      if id = id' then thin_val tl else s::(thin_val tl)
  | h::tl -> h::(thin_val tl)

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist = 
  let var_alist =
    List.map (fun (str,c) -> (str,make_substituend c)) var_alist in
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

let subst_varn str n = replace_vars [(str, (Rel n))]

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = subst_varn str 1

(* [Rel (n+m);...;Rel(n+1)] *)

let rel_vect n m = Array.init m (fun i -> Rel(n+m-i))

let rel_list n m = 
  let rec reln l p = 
    if p>m then l else reln (Rel(n+p)::l) (p+1)
  in 
  reln [] 1

(* Obsolète 
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

let under_dlams f = 
  let rec apprec = function 
    | DLAMV(na,c) -> DLAMV(na,Array.map f c)
    | DLAM(na,c)  -> DLAM(na,apprec c)
    | _           -> failwith "under_dlams"
  in 
  apprec 

let put_DLAMSV lna lc = 
  match lna with 
    | [] -> anomaly "put_DLAM"
    | na::lrest -> List.fold_left (fun c na -> DLAM(na,c)) (DLAMV(na,lc)) lrest

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
*)  
