
(* $Id$ *)

(* This module instanciates the structure of generic deBruijn terms to Coq *)

open Util
open Pp
open Names
open Univ

(* Coq abstract syntax with deBruijn variables; 'a is the type of sorts *)

type existential_key = int

type pattern_source = DefaultPat of int | RegularPat
type case_style = PrintLet | PrintIf | PrintCases
type case_printing =
    inductive_path * identifier array * int
    * case_style option * pattern_source array
type case_info = int array * case_printing

type 'a oper = 
  (* DOP0 *)
  | Meta of int
  | Sort of 'a
  (* DOP2 *)
  | Cast | Prod | Lambda
  (* DOPN *)
  | AppL | Const of section_path
  | Evar of existential_key
  | MutInd of inductive_path
  | MutConstruct of constructor_path
  | MutCase of case_info
  | Fix of int array * int
  | CoFix of int

  | XTRA of string
      (* an extra slot, for putting in whatever sort of
         operator we need for whatever sort of application *)

(* Sorts. *)

type contents = Pos | Null

let contents_of_str = function
  | "Pos" -> Pos
  | "Null" -> Null
  | _ -> invalid_arg "contents_of_str"

let str_of_contents = function
  | Pos -> "Pos"
  | Null -> "Null"

type sorts =
  | Prop of contents                      (* proposition types *)
  | Type of universe
      
let mk_Set  = Prop Pos
let mk_Prop = Prop Null

let print_sort = function
  | Prop Pos -> [< 'sTR "Set" >]
  | Prop Null -> [< 'sTR "Prop" >]
  | Type _ -> [< 'sTR "Type" >]

(********************************************************************)
(*           Generic syntax of terms with de Bruijn indexes         *)
(********************************************************************)

type constr =
  | DOP0 of sorts oper                      (* atomic terms *)
  | DOP1 of sorts oper * constr             (* operator of arity 1 *)
  | DOP2 of sorts oper * constr * constr    (* operator of arity 2 *)
  | DOPN of sorts oper * constr array       (* operator of variadic arity *)
  | DLAM of name * constr                   (* deBruijn binder on one term *)
  | DLAMV of name * constr array            (* deBruijn binder on many terms *)
  | CLam of name * constr * constr
  | CPrd of name * constr * constr
  | CLet of name * constr * constr * constr
  | VAR of identifier                       (* named variable *)
  | Rel of int                              (* variable as deBruijn index *)

and
  (*
    typed_type = sorts judge
  *)
  typed_type = constr

type flat_arity = (name * constr) list * sorts

type 'a judge = { body : constr; typ : 'a }

(*
type typed_term = typed_type judge

let make_typed t s = { body = t; typ = s }
let make_typed_lazy t f = { body = t; typ = f s }

let typed_app f tt = { body = f tt.body; typ = tt.typ }

let body_of_type ty = ty.body
let level_of_type t = (t.typ : sorts)

let incast_type tty = DOP2 (Cast, tty.body, (DOP0 (Sort tty.typ)))

let outcast_type = function
   DOP2 (Cast, b, DOP0 (Sort s)) -> {body=b; typ=s}
  | _ -> anomaly "outcast_type: Not an in-casted type judgement"

let typed_combine f g t u = { f t.body u.body ; g t.typ u.typ}
*)

type typed_term = typed_type judge

let make_typed t s = t
let make_typed_lazy t f = t

let typed_app f tt = f tt

let body_of_type ty = ty
let level_of_type t = failwith "N'existe plus"

let incast_type tty = tty
let outcast_type x = x
let typed_combine f g t u = f t u
(**)

type var_declaration = identifier * constr option * typed_type
type rel_declaration = name * constr option * typed_type

(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(*********************)
(*     Occurring     *)
(*********************)

exception FreeVar
exception Occur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn = 
  let rec closed_rec n = function
    | Rel(m)        -> if m>n then raise FreeVar
    | VAR _         -> ()
    | DOPN(_,cl)    -> Array.iter (closed_rec n) cl
    | DOP2(_,c1,c2) -> closed_rec n c1; closed_rec n c2
    | DOP1(_,c)     -> closed_rec n c
    | DLAM(_,c)     -> closed_rec (n+1) c
    | DLAMV(_,v)    -> Array.iter (closed_rec (n+1)) v
    | CLam (_,t,c)   -> closed_rec n t; closed_rec (n+1) c
    | CPrd (_,t,c)   -> closed_rec n t; closed_rec (n+1) c
    | CLet (_,b,t,c) -> closed_rec n b; closed_rec n t; closed_rec (n+1) c
    | _             -> ()
  in 
  closed_rec

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

let closed0 term =
  try closedn 0 term; true with FreeVar -> false

(* returns the list of free debruijn indices in a term *)

let free_rels m = 
  let rec frec depth acc = function
    | Rel n         -> if n >= depth then Intset.add (n-depth+1) acc else acc
    | DOPN(_,cl)    -> Array.fold_left (frec depth) acc cl
    | DOP2(_,c1,c2) -> frec depth (frec depth acc c1) c2
    | DOP1(_,c)     -> frec depth acc c
    | DLAM(_,c)     -> frec (depth+1) acc c
    | DLAMV(_,cl)   -> Array.fold_left (frec (depth+1)) acc cl
    | CLam (_,t,c)   -> frec (depth+1) (frec depth acc t) c
    | CPrd (_,t,c)   -> frec (depth+1) (frec depth acc t) c
    | CLet (_,b,t,c) -> frec (depth+1) (frec depth (frec depth acc b) t) c
    | VAR _         -> acc
    | DOP0 _        -> acc
  in 
  frec 1 Intset.empty m

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term = 
  let rec occur_rec n = function
    | Rel(m)        -> if m = n then raise Occur
    | VAR _         -> ()
    | DOPN(_,cl)    -> Array.iter (occur_rec n) cl
    | DOP1(_,c)     -> occur_rec n c
    | DOP2(_,c1,c2) -> occur_rec n c1; occur_rec n c2
    | DLAM(_,c)     -> occur_rec (n+1) c
    | DLAMV(_,v)    -> Array.iter (occur_rec (n+1)) v
    | CLam (_,t,c)   -> occur_rec n t; occur_rec (n+1) c
    | CPrd (_,t,c)   -> occur_rec n t; occur_rec (n+1) c
    | CLet (_,b,t,c) -> occur_rec n b; occur_rec n t; occur_rec (n+1) c
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
    | DOP1(_,c)     -> occur_rec n c
    | DOP2(_,c1,c2) -> occur_rec n c1; occur_rec n c2
    | DLAM(_,c)     -> occur_rec (n+1) c
    | DLAMV(_,v)    -> Array.iter (occur_rec (n+1)) v
    | CLam (_,t,c)   -> occur_rec n t; occur_rec (n+1) c
    | CPrd (_,t,c)   -> occur_rec n t; occur_rec (n+1) c
    | CLet (_,b,t,c) -> occur_rec n b; occur_rec n t; occur_rec (n+1) c
    | _             -> ()
  in 
  try occur_rec n term; true with Occur -> false

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

let noccur_with_meta n m term = 
  let rec occur_rec n = function
    | Rel p -> if n<=p & p<n+m then raise Occur
    | VAR _ -> ()
    | DOPN(AppL,cl) ->
	(match cl.(0) with
           | DOP2 (Cast,DOP0 (Meta _),_) -> ()
           | DOP0 (Meta _) -> ()
	   | _ -> Array.iter (occur_rec n) cl)
    | DOPN(Evar _, _) -> ()
    | DOPN(op,cl) -> Array.iter (occur_rec n) cl
    | DOP0(_) -> ()
    | DOP1(_,c) -> occur_rec n c
    | DOP2(_,c1,c2) -> occur_rec n c1; occur_rec n c2
    | DLAM(_,c) -> occur_rec (n+1) c
    | DLAMV(_,v) -> Array.iter (occur_rec (n+1)) v
    | CLam (_,t,c)   -> occur_rec n t; occur_rec (n+1) c
    | CPrd (_,t,c)   -> occur_rec n t; occur_rec (n+1) c
    | CLet (_,b,t,c) -> occur_rec n b; occur_rec n t; occur_rec (n+1) c
  in 
  try (occur_rec n term; true) with Occur -> false


(*********************)
(*      Lifting      *)
(*********************)

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
  | DOP1(oper,c)     -> DOP1(oper, exliftn el c)
  | DOP2(oper,c1,c2) -> DOP2(oper, exliftn el c1, exliftn el c2)
  | DLAM(na,c)       -> DLAM(na, exliftn (el_lift el) c)
  | DLAMV(na,v)      -> DLAMV(na, Array.map (exliftn (el_lift el)) v)
  | CLam (n,t,c)   -> CLam (n, exliftn el t, exliftn (el_lift el) c)  
  | CPrd (n,t,c)   -> CPrd (n, exliftn el t, exliftn (el_lift el) c)
  | CLet (n,b,t,c) -> CLet (n,exliftn el b,exliftn el t,exliftn (el_lift el) c)
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

(*********************)
(*   Substituting    *)
(*********************)

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
    | DOP1(oper,c)     -> DOP1(oper,substrec depth c)
    | DOP2(oper,c1,c2) -> DOP2(oper,substrec depth c1,substrec depth c2)
    | DLAM(na,c)       -> DLAM(na,substrec (depth+1) c)
    | DLAMV(na,v)      -> DLAMV(na,Array.map (substrec (depth+1)) v)
    | CLam (n,t,c)   -> CLam (n, substrec depth t, substrec (depth+1) c)  
    | CPrd (n,t,c)   -> CPrd (n, substrec depth t, substrec (depth+1) c)
    | CLet (n,b,t,c) -> CLet (n, substrec depth b, substrec depth t, 
			      substrec (depth+1) c)
    | x                -> x
  in 
  substrec n

let substnl laml k =
  substn_many (Array.map make_substituend (Array.of_list laml)) k
let substl laml =
  substn_many (Array.map make_substituend (Array.of_list laml)) 0
let subst1 lam = substl [lam]

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
    | DOP1(oper,c)     -> DOP1(oper,substrec n c)
    | DOP2(oper,c1,c2) -> DOP2(oper,substrec n c1,substrec n c2)
    | DLAM(na,c)       -> DLAM(na,substrec (n+1) c)
    | DLAMV(na,v)      -> DLAMV(na,Array.map (substrec (n+1)) v)
    | CLam (na,t,c)     -> CLam (na, substrec n t, substrec (n+1) c)  
    | CPrd (na,t,c)     -> CPrd (na, substrec n t, substrec (n+1) c)
    | CLet (na,b,t,c)   -> CLet (na,substrec n b,substrec n t,substrec (n+1) c)
    | x                -> x
  in 
  if var_alist = [] then (function x -> x) else substrec 0

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = replace_vars [(str, Rel 1)]

(* (subst_vars [id1;...;idn] t) substitute (VAR idj) by (Rel j) in t *)
let subst_vars vars =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var,Rel n)::l)) (1,[]) vars
  in replace_vars (List.rev subst)

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let mkRel   n = (Rel n)

(* Constructs an existential variable named "?n" *)
let mkMeta  n =  DOP0 (Meta n)

(* Constructs a Variable named id *)
let mkVar id = VAR id

(* Construct an XTRA term (XTRA is an extra slot for whatever you want) *)
let mkXtra s = (DOP0 (XTRA s))

(* Construct a type *)
let mkSort s = DOP0 (Sort s)
let mkProp   = DOP0 (Sort mk_Prop)
let mkSet    = DOP0 (Sort mk_Set)
let mkType u = DOP0 (Sort (Type u))

let prop = Prop Null
and spec = Prop Pos
and types = Type dummy_univ
and type_0 = Type prop_univ
and type_1 = Type prop_univ_univ

(* Construct an implicit (see implicit arguments in the RefMan) *)
(* let mkImplicit = DOP0 Implicit*)

let implicit_univ = make_path ["Implicit"] (id_of_string "dummy") OBJ
let implicit_sort = Type { u_sp = implicit_univ ; u_num = 0}
let mkImplicit = DOP0 (Sort implicit_sort)


(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast (t1,t2) =
  match t1 with
    | DOP2(Cast,t,_) -> DOP2(Cast,t,t2)
    | _ -> (DOP2 (Cast,t1,t2))

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = CPrd (x,t1,t2)
let mkNamedProd id typ c = mkProd (Name id, typ, subst_var id c)
let mkProd_string   s t c = mkProd (Name (id_of_string s), t, c)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = CLam (x,t1,t2)
let mkNamedLambda id typ c = mkLambda (Name id, typ, subst_var id c)
let mkLambda_string s t c = mkLambda (Name (id_of_string s), t, c)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = CLet (x,c1,t,c2)
let mkNamedLetIn id c1 t c2 = mkLetIn (Name id, c1, t, subst_var id c2)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedProd_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id (body_of_type t) c
    | Some b -> mkNamedLetIn id b (body_of_type t) c

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
let mkLambda_or_LetIn (na,body,t) c =
  match body with
    | None -> mkLambda (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedLambda_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedLambda id (body_of_type t) c
    | Some b -> mkNamedLetIn id b (body_of_type t) c

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
let mkProd_wo_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, body_of_type t, c)
    | Some b -> subst1 b c

let mkNamedProd_wo_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id (body_of_type t) c
    | Some b -> subst1 b (subst_var id c)

(* non-dependent product t1 -> t2 *)
let mkArrow t1 t2 = mkProd (Anonymous, t1, t2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
let mkAppL a = DOPN (AppL, a)
let mkAppList a l = DOPN (AppL, Array.of_list (a::l))

(* Constructs a constant *) 
(* The array of terms correspond to the variables introduced in the section *)
let mkConst (sp,a) = DOPN (Const  sp, a)

(* Constructs an existential variable *)
let mkEvar (n,a) = DOPN (Evar n, a)

(* Constructs the ith (co)inductive type of the block named sp *)
(* The array of terms correspond to the variables introduced in the section *)
let mkMutInd (ind_sp,l) = DOPN (MutInd ind_sp, l)

(* Constructs the jth constructor of the ith (co)inductive type of the 
   block named sp. The array of terms correspond to the variables
   introduced in the section *)
let mkMutConstruct (cstr_sp,l) =  DOPN (MutConstruct cstr_sp,l)

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkMutCaseL (ci, p, c, ac) = 
  DOPN (MutCase ci, Array.append [|p;c|] (Array.of_list ac))
let mkMutCase (ci, p, c, ac) = 
  DOPN (MutCase ci, Array.append [|p;c|] ac)

(* If recindxs = [|i1,...in|] 
      typarray = [|t1,...tn|]
      funnames = [f1,.....fn]
      bodies   = [b1,.....bn]
   then    

      mkFix recindxs i typarray funnames bodies
   
   constructs the ith function of the block  

    Fixpoint f1 [ctx1] = b1
    with     f2 [ctx2] = b2
    ...
    with     fn [ctxn] = bn.

   where the lenght of the jth context is ij.
*)

(* Here, we assume the body already constructed *)
let mkFixDlam recindxs i jtypsarray body =
  let typsarray = (*Array.map incast_type*) jtypsarray in
  DOPN (Fix (recindxs,i),Array.append typsarray body)

let mkFix ((recindxs, i), (jtypsarray, funnames, bodies)) = 
  let rec wholebody = function 
    | [h]    -> (DLAMV (h,bodies)) 
    | (x::l) -> (DLAM  (x, wholebody l))
    | [] -> anomaly "in Term.mkFix : empty list of funnames"
  in 
  mkFixDlam recindxs i jtypsarray [|(wholebody funnames)|]

(* If typarray = [|t1,...tn|]
      funnames = [f1,.....fn]
      bodies   = [b1,.....bn]
   then

      mkCoFix i typsarray funnames bodies 

   constructs the ith function of the block  
   
    CoFixpoint f1 = b1
    with       f2 = b2
    ...
    with       fn = bn.

*)
(* Here, we assume the body already constructed *)
let mkCoFixDlam i jtypsarray body =
  let typsarray = (*Array.map incast_type*) jtypsarray in
  DOPN ((CoFix i),(Array.append typsarray body))

let mkCoFix (i, (jtypsarray, funnames, bodies)) = 
  let rec wholebody l = 
    match l with 
      | [h]    -> (DLAMV (h,bodies))
      | (x::l) -> (DLAM  (x, wholebody l))
      | [] -> anomaly "in Term.mkCoFix : empty list of funnames"
  in 
  mkCoFixDlam i jtypsarray [|(wholebody funnames)|]

(********************)
(* Term destructors *)
(********************)

(* Destructor operations : partial functions 
   Raise invalid_arg "dest*" if the const has not the expected form *)

(* Destructs a DeBrujin index *)
let destRel = function
  | (Rel n) -> n
  | _ -> invalid_arg "destRel"

(* Destructs an existential variable *)
let destMeta = function
  | (DOP0 (Meta n)) -> n
  | _ -> invalid_arg "destMeta"


(* Destructs a variable *)
let destVar = function
  | (VAR id) -> id
  | _ -> invalid_arg "destVar"

(* Destructs an XTRA *)
let destXtra = function
  | DOP0 (XTRA s) -> s
  | _ -> invalid_arg "destXtra"

(* Destructs a type *)
let destSort = function
  | (DOP0 (Sort s)) -> s
  | _ -> invalid_arg "destSort"

let rec isprop = function
  | DOP0(Sort(Prop _)) -> true
  | DOP2(Cast,c,_) -> isprop c
  | _ -> false

let rec is_Prop = function
  | DOP0(Sort(Prop Null)) -> true
  | DOP2(Cast,c,_) -> is_Prop c
  | _ -> false

let rec is_Set = function
  | DOP0(Sort(Prop Pos)) -> true
  | DOP2(Cast,c,_) -> is_Set c
  | _ -> false

let rec is_Type = function
  | DOP0(Sort(Type _)) -> true
  | DOP2(Cast,c,_) -> is_Type c
  | _ -> false

let isType = function
  | Type _ -> true
  | _ -> false

let is_small = function
  | Prop _ -> true
  | _ -> false

let iskind c = isprop c or is_Type c

let is_existential_oper = function
  | Evar _ -> true
  | _ -> false

let same_kind c1 c2 = (isprop c1 & isprop c2) or (is_Type c1 & is_Type c2)

let rec contents_of_kind = function
  | DOP0(Sort(Prop cts)) -> cts
  | DOP0(Sort(Type _)) -> Pos
  | DOP2(Cast,c,t) -> contents_of_kind c
  | _ -> invalid_arg "contents_of_kind"

(* Destructs a casted term *)
let destCast = function 
  | DOP2 (Cast, t1, t2) -> (t1,t2)
  | _ -> invalid_arg "destCast"

let isCast = function DOP2(Cast,_,_) -> true | _ -> false

let rec strip_outer_cast = function
  | DOP2(Cast,c,_) -> strip_outer_cast c
  | c -> c



(* Fonction spéciale qui laisse les cast clés sous les Fix ou les MutCase *)

let under_outer_cast f = function
  | DOP2 (Cast,b,t) -> DOP2 (Cast,f b,f t)
  | c -> f c

let rec strip_all_casts t = 
  match t with
    | DOP2 (Cast, b, _) -> strip_all_casts b
    | DOP0 _ as t -> t
    (* Cas ad hoc *)
    | DOPN(Fix _ as f,v) -> 
	let n = Array.length v in
	let ts = Array.sub v 0 (n-1) in
	let b = v.(n-1) in 
	DOPN(f, Array.append 
	       (Array.map strip_all_casts ts)
	       [|under_outer_cast strip_all_casts b|])
    | DOPN(CoFix _ as f,v) -> 
	let n = Array.length v in
	let ts = Array.sub v 0 (n-1) in
	let b = v.(n-1) in 
	DOPN(f, Array.append 
	       (Array.map strip_all_casts ts)
	       [|under_outer_cast strip_all_casts b|])
    | DOP1(oper,c) -> DOP1(oper,strip_all_casts c)
    | DOP2(oper,c1,c2) -> DOP2(oper,strip_all_casts c1,strip_all_casts c2)
    | DOPN(oper,cl) -> DOPN(oper,Array.map strip_all_casts cl)
    | DLAM(na,c) -> DLAM(na,strip_all_casts c)
    | DLAMV(na,c) -> DLAMV(na,Array.map (under_outer_cast strip_all_casts) c)
    | CLam (n,t,c)   -> CLam (n, strip_all_casts t, strip_all_casts c)  
    | CPrd (n,t,c)   -> CPrd (n, strip_all_casts t, strip_all_casts c)
    | CLet (n,b,t,c) -> CLet (n, strip_all_casts b, strip_all_casts t,
			      strip_all_casts c)
    | VAR _ as t -> t
    | Rel _ as t -> t

(* Tests if a de Bruijn index *)
let isRel = function Rel _ -> true | _ -> false

(* Tests if a variable *)
let isVar = function VAR _ -> true | _ -> false

(* Destructs the product (x:t1)t2 *)
let destProd = function 
  | CPrd (x,t1,t2) -> (x,t1,t2) 
  | _ -> invalid_arg "destProd"

let rec hd_of_prod prod =
  match strip_outer_cast prod with
    | CPrd (n,c,t') -> hd_of_prod t'
    | t -> t

let hd_is_constructor t  =  
  let is_constructor =  function
    | DOPN(MutConstruct((sp,tyi),i),cl)-> true 
    | _ ->false
  in
  match t with 
    | DOPN(AppL,v) -> is_constructor v.(0)
    | c -> is_constructor c

(* Destructs the abstraction [x:t1]t2 *)
let destLambda = function 
  | CLam (x,t1,t2) -> (x,t1,t2) 
  | _ -> invalid_arg "destLambda"

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn = function 
  | CLet (x,b,t1,t2) -> (x,b,t1,t2) 
  | _ -> invalid_arg "destProd"

(* Destructs an application *)
let destAppL = function 
  | (DOPN (AppL,a)) -> a
  | _ -> invalid_arg "destAppL"

let destApplication =  function
  | (DOPN (AppL,a)) when Array.length a <> 0 -> (a.(0), array_tl a)
  | _ -> invalid_arg "destApplication"

let args_app  = function
  | DOPN(AppL,cl) -> if Array.length cl >1  then array_tl cl else [||]
  | c -> [||]

let hd_app  = function
  | DOPN(AppL,cl) -> cl.(0)
  | c -> c

(* Destructs a constant *)
let destConst = function
  | DOPN (Const sp, a) -> (sp, a)
  | _ -> invalid_arg "destConst"

let path_of_const = function
  | DOPN (Const sp,_) -> sp
  | _ -> anomaly "path_of_const called with bad args"

let args_of_const = function
  | DOPN (Const _,args) -> args
  | _ -> anomaly "args_of_const called with bad args"

(* Destructs an existential variable *)
let destEvar = function
  | DOPN (Evar n, a) -> (n,a)
  | _ -> invalid_arg "destEvar"

let num_of_evar = function
  | DOPN (Evar n, _) -> n
  | _ -> anomaly "num_of_evar called with bad args"

(*
(* Destructs an abstract term *)
let destAbst = function
  | DOPN (Abst sp, a) -> (sp, a)
  | _ -> invalid_arg "destAbst"  

let path_of_abst = function
  | DOPN(Abst sp,_) -> sp
  | _ -> anomaly "path_of_abst called with bad args"

let args_of_abst = function
  | DOPN(Abst _,args) -> args
  | _ -> anomaly "args_of_abst called with bad args"
*)
(* Destructs a (co)inductive type named sp *)
let destMutInd = function
  | DOPN (MutInd ind_sp, l) -> (ind_sp,l)
  | _ -> invalid_arg "destMutInd"
	
let op_of_mind = function
  | DOPN(MutInd ind_sp,_) -> ind_sp
  | _ -> anomaly "op_of_mind called with bad args"

let args_of_mind = function
  | DOPN(MutInd _,args) -> args
  | _ -> anomaly "args_of_mind called with bad args"

(* Destructs a constructor *)
let destMutConstruct = function
  | DOPN (MutConstruct cstr_sp,l) -> (cstr_sp,l)
  | _ -> invalid_arg "dest"

let op_of_mconstr = function
  | DOPN(MutConstruct (spi,c),_) -> (spi,c)
  | _ -> anomaly "op_of_mconstr called with bad args"

let args_of_mconstr = function
  | DOPN(MutConstruct _,args) -> args
  | _ -> anomaly "args_of_mconstr called with bad args"

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase = function
  | DOPN (MutCase ci,v) -> (ci,v.(0),v.(1),Array.sub v 2 (Array.length v - 2))
  | _ -> anomaly "destCase"

(* Destructs the ith function of the block  
    Fixpoint f1 [ctx1] = b1
    with     f2 [ctx2] = b2
    ...
    with     fn [ctxn] = bn.

   where the lenght of the jth context is ij.
*)

let destGralFix a =
  let nbofdefs = Array.length a in
  let types    = Array.sub a 0 (nbofdefs-1) in
  let dlambody = a.(nbofdefs-1) in 
  let rec destbody l c = 
    match c with 
      | DLAMV (h,bodies) -> (List.rev (h::l), bodies) 
      | DLAM  (x,t)      -> destbody (x::l) t 
      | _ -> invalid_arg "destGralFix" 
  in 
  let funnames,bodies = destbody [] dlambody in 
  (types,funnames,bodies)

let destFix = function 
  | DOPN (Fix (recindxs,i),a) -> 
      let (types,funnames,bodies) = destGralFix a in 
      ((recindxs,i),(types,funnames,bodies))
  | _ -> invalid_arg "destFix"
	
let destCoFix = function 
  | DOPN ((CoFix i),a) ->
      let (types,funnames,bodies) = destGralFix a in
      (i,(types,funnames,bodies))
  | _ -> invalid_arg "destCoFix"

(**********************************************************************)

type binder_kind = BProd | BLambda | BLetIn

type fix_kind = RFix of (int array * int) | RCoFix of int

type 'ctxt reference =
  | RConst of section_path * 'ctxt
  | RInd of inductive_path * 'ctxt
  | RConstruct of constructor_path * 'ctxt
  | RVar of identifier
  | REVar of int * 'ctxt

type existential = int * constr array
type constant = section_path * constr array
type constructor = constructor_path * constr array
type inductive = inductive_path * constr array
type fixpoint = (int array * int) * (constr array * name list * constr array)
type cofixpoint = int * (constr array * name list * constr array)

(******************)
(* Term analysis  *)
(******************)

type hnftype =
  | HnfSort   of sorts
  | HnfProd   of name * constr * constr
  | HnfAtom   of constr
  | HnfMutInd of inductive * constr array

type kindOfTerm = 
  | IsRel          of int
  | IsMeta         of int
  | IsVar          of identifier
  | IsXtra         of string
  | IsSort         of sorts
  | IsCast         of constr * constr
  | IsProd         of name * constr * constr
  | IsLambda       of name * constr * constr
  | IsLetIn        of name * constr * constr * constr
  | IsAppL         of constr * constr list
  | IsEvar         of existential
  | IsConst        of constant
  | IsMutInd       of inductive
  | IsMutConstruct of constructor
  | IsMutCase      of case_info * constr * constr * constr array
  | IsFix          of fixpoint
  | IsCoFix        of cofixpoint

(* Discriminates which kind of term is it.  

   Note that there is no cases for DLAM and DLAMV.  These terms do not
   make sense alone, but they must be preceeded by the application of
   an operator. *)

let kind_of_term c = 
  match c with
    | Rel n                                -> IsRel n
    | VAR id                               -> IsVar id 
    | DOP0 (Meta n)                        -> IsMeta n
    | DOP0 (Sort s)                        -> IsSort s
    | DOP0 (XTRA s)                        -> IsXtra s
    | DOP2 (Cast, t1, t2)                  -> IsCast (t1,t2)
    | CPrd (x,t1,t2)                       -> IsProd (x,t1,t2) 
    | CLam (x,t1,t2)                       -> IsLambda (x,t1,t2)
    | CLet (x,b,t1,t2)                     -> IsLetIn (x,b,t1,t2)
    | DOPN (AppL,a) when Array.length a <> 0 -> 
	IsAppL (a.(0), List.tl (Array.to_list a))
    | DOPN (Const sp, a)                   -> IsConst (sp,a)
    | DOPN (Evar sp, a)                    -> IsEvar (sp,a)
    | DOPN (MutInd ind_sp, l)              -> IsMutInd (ind_sp,l)
    | DOPN (MutConstruct cstr_sp,l)        -> IsMutConstruct (cstr_sp,l)
    | DOPN (MutCase ci,v)                  -> 
	IsMutCase (ci,v.(0),v.(1),Array.sub v 2 (Array.length v - 2))
    | DOPN ((Fix (recindxs,i),a))           ->  
      	let typedbodies = destGralFix a in
	IsFix ((recindxs,i),typedbodies)
    | DOPN ((CoFix i),a)                    ->  
      	let typedbodies = destGralFix a in
      	IsCoFix (i,typedbodies)
    | _ -> errorlabstrm "Term.kind_of_term" [< 'sTR "ill-formed constr" >]

let isMeta = function DOP0(Meta _) -> true | _ -> false
let isConst = function DOPN(Const _,_) -> true | _ -> false
let isMutConstruct = function DOPN(MutCase _,_) -> true | _ -> false
let isAppL = function DOPN(AppL,_) -> true | _ -> false

(***************************)
(* Other term constructors *)
(***************************)

let abs_implicit c = mkLambda (Anonymous, mkImplicit, c)
let lambda_implicit a = mkLambda (Name(id_of_string"y"), mkImplicit, a)
let lambda_implicit_lift n a = iterate lambda_implicit n (lift n a)


(* prod_it b [xn:Tn;..;x1:T1] = (x1:T1)..(xn:Tn)b *)
let prod_it = List.fold_left (fun c (n,t)  -> mkProd (n, t, c))

(* lam_it b [xn:Tn;..;x1:T1] = [x1:T1]..[xn:Tn]b *)
let lam_it = List.fold_left (fun c (n,t)  -> mkLambda (n, t, c))

(* prodn n [xn:Tn;..;x1:T1;Gamma] b = (x1:T1)..(xn:Tn)b *)
let prodn n env b =
  let rec prodrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, CPrd (v,t,b))
    | _ -> assert false
  in 
  prodrec (n,env,b)

(* lamn n [xn:Tn;..;x1:T1;Gamma] b = [x1:T1]..[xn:Tn]b *)
let lamn n env b =
  let rec lamrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> lamrec (n-1,  l, CLam (v,t,b))
    | _ -> assert false
  in 
  lamrec (n,env,b)

let rec applist = function
  | (f,[]) -> f
  | (DOPN(AppL,cl),l2) -> 
      let c = array_hd cl in 
       if isAppL c then 
	 applist(c,array_app_tl cl l2)
       else 
	 DOPN(AppL,Array.append cl (Array.of_list l2))
  | (f,l) -> DOPN(AppL,Array.of_list(f::l))

and applistc f l = applist(f,l)

let rec appvect = function
  | (f, [||]) -> f
  | (DOPN(AppL,cl), v) ->
      let c = array_hd cl in 
      if isAppL c then
	appvect (c, Array.append (array_tl cl) v)
      else 
	DOPN(AppL, Array.append cl v)
  | (f,v) -> DOPN(AppL, array_cons f v)
	    
and appvectc f l = appvect (f,l)
		     
(* to_lambda n (x1:T1)...(xn:Tn)(xn+1:Tn+1)...(xn+j:Tn+j)T =
 * [x1:T1]...[xn:Tn](xn+1:Tn+1)...(xn+j:Tn+j)T *)
let rec to_lambda n prod =
  if n = 0 then 
    prod 
  else 
    match prod with 
      | CPrd(na,ty,bd) -> CLam(na,ty,to_lambda (n-1) bd)
      | DOP2(Cast,c,_) -> to_lambda n c
      | _   -> errorlabstrm "to_lambda" [<>]                      

let rec to_prod n lam =
  if n=0 then 
    lam
  else   
    match lam with 
      | CLam(na,ty,bd) -> CPrd(na,ty,to_prod (n-1) bd)
      | DOP2(Cast,c,_) -> to_prod n c
      | _   -> errorlabstrm "to_prod" [<>]                      
	    
(* pseudo-reduction rule:
 * [prod_app  s (Prod(_,B)) N --> B[N]
 * with an strip_outer_cast on the first argument to produce a product *)

let prod_app t n =
  match strip_outer_cast t with
    | CPrd (_,_,b) -> subst1 n b
    | _ ->
	errorlabstrm "prod_app"
	  [< 'sTR"Needed a product, but didn't find one" ; 'fNL >]


(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_appvect t nL = Array.fold_left prod_app t nL

(* prod_applist T [ a1 ; ... ; an ] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL


(*********************************)
(* Other term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let destArity = 
  let rec prodec_rec l c =
    match kind_of_term c with
    | IsProd (x,t,c) -> prodec_rec ((x,t)::l) c
    | IsCast (c,_)   -> prodec_rec l c
    | IsSort s       -> l,s
    | _              -> anomaly "decompose_arity: not an arity"
  in 
  prodec_rec [] 

let rec isArity c =
  match kind_of_term c with
  | IsProd (_,_,c) -> isArity c
  | IsCast (c,_)   -> isArity c
  | IsSort _       -> true
  | _ -> false

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod = 
  let rec prodec_rec l = function
    | CPrd(x,t,c)    -> prodec_rec ((x,t)::l) c
    | DOP2(Cast,c,_) -> prodec_rec l c
    | c              -> l,c
  in 
  prodec_rec []

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam = 
  let rec lamdec_rec l = function
    | CLam (x,t,c)    -> lamdec_rec ((x,t)::l) c
    | DOP2 (Cast,c,_) -> lamdec_rec l c
    | c              -> l,c
  in 
  lamdec_rec []

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then error "decompose_prod_n: integer parameter must be positive";
  let rec prodec_rec l n c = 
    if n=0 then l,c 
    else match c with 
      | CPrd (x,t,c)    -> prodec_rec ((x,t)::l) (n-1) c
      | DOP2 (Cast,c,_) -> prodec_rec l n c
      | c -> error "decompose_prod_n: not enough products"
  in 
  prodec_rec [] n 

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n n =
  if n < 0 then error "decompose_lam_n: integer parameter must be positive";
  let rec lamdec_rec l n c = 
    if n=0 then l,c 
    else match c with 
      | CLam (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | DOP2 (Cast,c,_)           -> lamdec_rec l n c
      | c -> error "decompose_lam_n: not enough abstractions"
  in 
  lamdec_rec [] n 

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
let nb_lam = 
  let rec nbrec n = function
    | CLam (_,_,c) -> nbrec (n+1) c
    | DOP2(Cast,c,_) -> nbrec n c
    | _ -> n
  in 
  nbrec 0
    
(* similar to nb_lam, but gives the number of products instead *)
let nb_prod = 
  let rec nbrec n = function
    | CPrd (_,_,c) -> nbrec (n+1) c
    | DOP2(Cast,c,_) -> nbrec n c
    | _ -> n
  in 
  nbrec 0

(* Misc *)
let sort_hdchar = function
  | Prop(_) -> "P"
  | Type(_) -> "T"

(* Level comparison for information extraction : Prop <= Type *)
let le_kind l m = (isprop l) or (is_Type m)

let le_kind_implicit k1 k2 = 
  (k1=mkImplicit) or (isprop k1) or (k2=mkImplicit) or (is_Type k2)

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

(* N.B.: does NOT collapse AppLs ! *)
let ensure_appl = function
  | DOPN(AppL,_) as t -> t
  | t -> DOPN(AppL,[|t|])

(* unflattens application lists *)
let rec telescope_appl = function
  | DOPN(AppL,cl) ->
      array_fold_left_from 1 (fun c e -> DOPN(AppL,[|c;e|])) (array_hd cl) cl
  | c -> c

(* flattens application lists *)
let rec collapse_appl = function
  | DOPN(AppL,cl) -> 
      let rec collapse_rec = function
	| (DOPN(AppL,cl),l2) -> collapse_rec(array_hd cl,array_app_tl cl l2)
	| (DOP2(Cast,DOPN(AppL,cl),t),l) -> collapse_rec(DOPN(AppL,cl),l)
	| (f,[]) -> f
	| (f,l) -> let v = Array.of_list (f::l) in DOPN(AppL,v)
      in 
      collapse_rec (array_hd cl, array_list_of_tl cl)
  | c -> c

let rec decomp_app c =
  match collapse_appl c with
    | DOPN(AppL,cl) -> (array_hd cl, array_list_of_tl cl)
    | DOP2(Cast,c,t) -> decomp_app c
    | c -> (c,[])

(* strips head casts and flattens head applications *)
let rec strip_head_cast = function
  | DOPN(AppL,cl) -> 
      let rec collapse_rec = function
	| (DOPN(AppL,cl),l2) -> collapse_rec(array_hd cl, array_app_tl cl l2)
	| (DOP2(Cast,c,t),l) -> collapse_rec(c,l)
	| (f,[]) -> f
	| (f,l) -> let v = Array.of_list (f::l) in DOPN(AppL,v)
      in 
      collapse_rec(array_hd cl, array_app_tl cl [])
  | DOP2(Cast,c,t) -> strip_head_cast c
  | c -> c

(* Returns the list of global variables in a term *)

let global_varsl l constr = 
  let rec filtrec acc = function
    | VAR id           -> id::acc
    | DOP1(oper,c)     -> filtrec acc c
    | DOP2(oper,c1,c2) -> filtrec (filtrec acc c1) c2
    | DOPN(oper,cl)    -> Array.fold_left filtrec acc cl
    | DLAM(_,c)        -> filtrec acc c
    | DLAMV(_,v)       -> Array.fold_left filtrec acc v
    | CLam (_,t,c)     -> filtrec (filtrec acc t) c
    | CPrd (_,t,c)     -> filtrec (filtrec acc t) c
    | CLet (_,b,t,c)   -> filtrec (filtrec (filtrec acc b) t) c
    | _                -> acc
  in 
  filtrec l constr

let global_vars constr = global_varsl [] constr

let global_vars_set constr = 
  let rec filtrec acc = function
    | VAR id           -> Idset.add id acc
    | DOP1(oper,c)     -> filtrec acc c
    | DOP2(oper,c1,c2) -> filtrec (filtrec acc c1) c2
    | DOPN(oper,cl)    -> Array.fold_left filtrec acc cl
    | DLAM(_,c)        -> filtrec acc c
    | DLAMV(_,v)       -> Array.fold_left filtrec acc v
    | CLam (_,t,c)     -> filtrec (filtrec acc t) c
    | CPrd (_,t,c)     -> filtrec (filtrec acc t) c
    | CLet (_,b,t,c)   -> filtrec (filtrec (filtrec acc b) t) c
    | _                -> acc
  in 
  filtrec Idset.empty constr

(* [Rel (n+m);...;Rel(n+1)] *)

let rel_vect n m = Array.init m (fun i -> Rel(n+m-i))

let rel_list n m = 
  let rec reln l p = 
    if p>m then l else reln (Rel(n+p)::l) (p+1)
  in 
  reln [] 1

(* Rem: end of import from old module Generic *)

(* Various occurs checks *)

let occur_opern s = 
  let rec occur_rec = function
    | DOPN(oper,cl) -> s=oper or (array_exists occur_rec cl)
    | VAR _         -> false
    | DOP1(_,c)     -> occur_rec c 
    | DOP2(_,c1,c2) -> (occur_rec c1) or (occur_rec c2)
    | DLAM(_,c)     -> occur_rec c
    | DLAMV(_,v)    -> array_exists occur_rec v
    | CLam (_,t,c)   -> occur_rec t or occur_rec c
    | CPrd (_,t,c)   -> occur_rec t or occur_rec c
    | CLet (_,b,t,c) -> occur_rec b or occur_rec t or occur_rec c
    | _             -> false
  in 
  occur_rec 

(* (occur_const (s:section_path) c) -> true if constant s occurs in c,
 * false otherwise *)
let occur_const s = occur_opern (Const s)
let occur_evar ev = occur_opern (Evar ev)

let occur_var s = 
  let rec occur_rec = function
    | DOPN(_,cl)    -> array_exists occur_rec cl
    | VAR id        -> s=id
    | DOP1(_,c)     -> occur_rec c 
    | DOP2(_,c1,c2) -> (occur_rec c1) or (occur_rec c2)
    | DLAM(_,c)     -> occur_rec c
    | DLAMV(_,v)    -> array_exists occur_rec v
    | CLam (_,t,c)   -> occur_rec t or occur_rec c
    | CPrd (_,t,c)   -> occur_rec t or occur_rec c
    | CLet (_,b,t,c) -> occur_rec b or occur_rec t or occur_rec c
    | _             -> false
  in 
  occur_rec 

(* let sigma be a finite function mapping sections paths to 
   constants represented as (identifier list * constr) option.
   (replace_consts sigma M) unfold_one_id the constants from sigma in term M

   - if (sp,NONE) is in sigma then the constant should not appear in
   term M otherwise replace_consts raises an anomaly ;

   - if (sp,SOME (idl,c)), then the constant sp is replaced by
   c in which the variables given by idl are replaced by the arguments
   of (Const sp), if the number of variables and arguments are not equal
   an anomaly is raised ;

   - if no (sp,_) appears in sigma, then sp is not unfolded.

*)
let replace_consts const_alist =
  let rec substrec = function
    | DOPN(Const sp,cl) as c ->
	let cl' = Array.map substrec cl in
	(try
	   match List.assoc sp const_alist with
	     | Some (hyps,body) ->
                 if List.length hyps <> Array.length cl then
                   anomaly "found a constant with a bad number of args"
                 else
      	       	   replace_vars (List.combine hyps (Array.to_list cl')) body
             | None -> anomaly ("a constant which was never"^
      	       	       		" supposed to appear has just appeared")
	 with Not_found -> DOPN(Const sp,cl'))

    | DOP1(i,c)         -> DOP1(i,substrec c)
    | DOPN(oper,cl)     -> DOPN(oper,Array.map substrec cl)
    | DOP2(oper,c1,c2)  -> DOP2(oper,substrec c1,substrec c2)
    | DLAM(na,c)        -> DLAM(na,substrec c)
    | DLAMV(na,v)       -> DLAMV(na,Array.map substrec v)
    | CLam (na,t,c)     -> CLam (na, substrec t, substrec c)  
    | CPrd (na,t,c)     -> CPrd (na, substrec t, substrec c)
    | CLet (na,b,t,c)   -> CLet (na, substrec b, substrec t, substrec c)
    | x                 -> x
  in 
  if const_alist = [] then function x -> x else substrec

let whd_castapp_stack = 
  let rec whrec x stack = match x with
    | DOPN(AppL,cl)  -> whrec (array_hd cl) (array_app_tl cl stack)
    | DOP2(Cast,c,_) -> whrec c stack
    | x              -> x,stack
  in 
  whrec

(* whd flattens embedded applications
   (whd_castapp ((((a b) c d) e f g) h)) -> (a b c d e f g h)
   even if some casts exist in ((((a b) c d) e f g) h))
 *)
let whd_castapp x = applist(whd_castapp_stack x [])


(***************************************)
(*  alpha and eta conversion functions *)                         
(***************************************)

(* alpha conversion : ignore print names and casts *)
let rec eq_constr_rec m n = 
  (m == n) or
  (m = n) or
  match (strip_head_cast m,strip_head_cast n) with
    | (Rel p1,Rel p2)                   -> p1=p2
    | (DOPN(oper1,cl1),DOPN(oper2,cl2)) ->
        oper1=oper2 & array_for_all2 eq_constr_rec cl1 cl2
    | (DOP0 oper1,DOP0 oper2)           -> oper1=oper2
    | (DOP1(i,c1),DOP1(j,c2))           -> (i=j) & eq_constr_rec c1 c2
    | (DOP2(i,c1,c1'),DOP2(j,c2,c2'))   ->
      	(i=j) & eq_constr_rec c1 c2 & eq_constr_rec c1' c2'
    | (DLAM(_,c1),DLAM(_,c2)) 	       -> eq_constr_rec c1 c2
    | (DLAMV(_,cl1),DLAMV(_,cl2))       -> 
      	array_for_all2 eq_constr_rec cl1 cl2
    | CLam(_,t1,c1), CLam(_,t2,c2) -> eq_constr_rec t1 t2 & eq_constr_rec c1 c2
    | CPrd(_,t1,c1), CPrd(_,t2,c2) -> eq_constr_rec t1 t2 & eq_constr_rec c1 c2
    | CLet(_,b1,t1,c1), CLet (_,b2,t2,c2) -> 
	eq_constr_rec b1 b2 & eq_constr_rec t1 t2 & eq_constr_rec c1 c2
    | _ -> false

let eq_constr = eq_constr_rec

(* (dependent M N) is true iff M is eq_term with a subterm of N 
   M is appropriately lifted through abstractions of N *)

let dependent =
  let rec deprec m t =
    (eq_constr m t) or 
    (match t with
       | VAR _       -> false
       | DOP1(_,c)   -> deprec m c
       | DOP2(_,c,t) -> deprec m c or deprec m t
       | DOPN(_,cl)  -> array_exists (deprec m) cl
       | DLAM(_,c)   -> deprec (lift 1 m) c
       | DLAMV(_,v)  -> array_exists (deprec (lift 1 m)) v
       | CLam (_,t,c)   -> deprec m t or deprec (lift 1 m) c
       | CPrd (_,t,c)   -> deprec m t or deprec (lift 1 m) c
       | CLet (_,b,t,c) -> deprec m b or deprec m t or deprec (lift 1 m) c
       | _ -> false)
  in 
  deprec

(* On reduit une serie d'eta-redex de tete ou rien du tout  *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 versions précédentes buggées                  *)

let rec eta_reduce_head c =
  match c with
    | CLam (_,c1,c') ->
	(match eta_reduce_head c' with
           | DOPN(AppL,cl) ->
               let lastn = (Array.length cl) - 1 in 
               if lastn < 1 then anomaly "application without arguments"
               else
                 (match cl.(lastn) with
                    | Rel 1 ->
                        let c' =
                          if lastn = 1 then cl.(0) 
			  else DOPN(AppL,Array.sub cl 0 lastn)
                        in
                        if (not ((dependent (mkRel 1) c'))) 
                        then lift (-1) c'
                        else c
                    | _     -> c)
           | _ -> c)
    | _ -> c

(* alpha-eta conversion : ignore print names and casts *)

let eta_eq_constr =
  let rec aux t1 t2 =
    let t1 = eta_reduce_head (strip_head_cast t1)
    and t2 = eta_reduce_head (strip_head_cast t2) in
    t1=t2 or match (t1,t2) with
    | (DOP2(Cast,c1,_),c2) -> aux c1 c2
    | (c1,DOP2(Cast,c2,_)) -> aux c1 c2
    | (Rel p1,Rel p2)                   -> p1=p2
    | (DOPN(op1,cl1),DOPN(op2,cl2)) -> op1=op2 & array_for_all2 aux cl1 cl2
    | (DOP0 oper1,DOP0 oper2)           -> oper1=oper2
    | (DOP1(i,c1),DOP1(j,c2)) -> (i=j) & aux c1 c2
    | (DOP2(i,c1,c1'),DOP2(j,c2,c2')) -> (i=j) & aux c1 c2 & aux c1' c2'
    | (DLAM(_,c1),DLAM(_,c2)) -> aux c1 c2
    | (DLAMV(_,cl1),DLAMV(_,cl2)) -> array_for_all2 aux cl1 cl2
    | CLam(_,t1,c1), CLam(_,t2,c2) -> aux t1 t2 & aux c1 c2
    | CPrd(_,t1,c1), CPrd(_,t2,c2) -> aux t1 t2 & aux c1 c2
    | CLet(_,b1,t1,c1), CLet (_,b2,t2,c2) -> aux b1 b2 & aux t1 t2 & aux c1 c2
    | _ -> false
  in aux


(* This renames bound variables with fresh and distinct names *)
(* in such a way that the printer doe not generate new names  *)
(* and therefore that printed names are the intern names      *)
(* In this way, tactics such as Induction works well          *)

let rec rename_bound_var l c =
  match kind_of_term c with
  | IsProd (Name s,c1,c2)  ->
      if dependent (mkRel 1) c2 then
        let s' = next_ident_away s (global_vars c2@l) in
        mkProd (Name s', c1, rename_bound_var (s'::l) c2)
      else 
	mkProd (Name s, c1, rename_bound_var l c2)
  | IsProd (Anonymous,c1,c2) -> mkProd (Anonymous, c1, rename_bound_var l c2)
  | IsCast (c,t) -> mkCast (rename_bound_var l c, t)
  | x -> c

(***************************)
(*  substitution functions *)                         
(***************************)

(* First utilities for avoiding telescope computation for subst_term *)

let prefix_application k (c : constr) (t : constr) = 
  match (whd_castapp c,whd_castapp t) with
    | ((DOPN(AppL,cl1)),DOPN(AppL,cl2)) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_constr (DOPN(AppL,cl1)) (DOPN(AppL,Array.sub cl2 0 l1)) then
	  Some(DOPN(AppL, array_cons (Rel k) (Array.sub cl2 l1 (l2 - l1))))
	else 
	  None
    | (_,_) -> None

let prefix_application_eta k (c : constr) (t : constr) = 
  match (whd_castapp c,whd_castapp t) with
    | ((DOPN(AppL,cl1)),DOPN(AppL,cl2)) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2 &&
           eta_eq_constr (DOPN(AppL,cl1)) (DOPN(AppL,Array.sub cl2 0 l1)) then
          Some(DOPN(AppL,array_cons (Rel k) (Array.sub cl2 l1 (l2 - l1))))
	else 
	  None
  | (_,_) -> None

let sort_increasing_snd = 
  Sort.list 
    (fun x y -> match x,y with 
	 (_,Rel m),(_,Rel n) -> m < n
       | _ -> assert false)

(* Recognizing occurrences of a given (closed) subterm in a term for Pattern :
   [subst_term c t] substitutes [(Rel 1)] for all occurrences of (closed)
   term [c] in a term [t] *)

let subst_term_gen eq_fun c t = 
  let rec substrec k c t =
    match prefix_application k c t with
      | Some x -> x
      | None ->
    (if eq_fun t c then Rel(k) else match t with
       | DOPN(Const sp,cl) -> t
       | DOPN(MutInd (x_0,x_1),cl) -> t
       | DOPN(MutConstruct (x_0,x_1),cl) -> t
       | DOPN(oper,tl)     -> DOPN(oper,Array.map (substrec k c) tl)
       | DOP1(i,t)         -> DOP1(i,substrec k c t)
       | DOP2(oper,c1,c2)  -> DOP2(oper,substrec k c c1,substrec k c c2)
       | DLAM(na,t)        -> DLAM(na,substrec (k+1) (lift 1 c) t)
       | DLAMV(na,v) -> DLAMV(na,Array.map (substrec (k+1) (lift 1 c)) v)
       | CLam(na,t,c2) -> CLam(na,substrec k c t,substrec (k+1) (lift 1 c) c2) 
       | CPrd(na,t,c2) -> CPrd(na,substrec k c t,substrec (k+1) (lift 1 c) c2) 
       | CLet(na,b,t,c2) -> CLet(na,substrec k c b,substrec k c t,
				substrec (k+1) (lift 1 c) c2)
       | _ -> t)
  in 
  substrec 1 c t

let subst_term = subst_term_gen eq_constr
let subst_term_eta = subst_term_gen eta_eq_constr

(* bl : (int,constr) Listmap.t = (int * constr) list *)
(* c : constr *)
(* for each binding (i,c_i) in bl, substitutes the metavar i by c_i in c *)
(* Raises Not_found if c contains a meta that is not in the association list *)

(* Bogué ? Pourquoi pas de lift en passant sous un lieur ?? *)
(* Et puis meta doit fusionner avec Evar *)
let rec subst_meta bl c = 
  match c with
    | DOP0(Meta(i)) -> List.assoc i bl
    | DOP1(op,c') -> DOP1(op, subst_meta bl c')
    | DOP2(op,c'1, c'2) -> DOP2(op, subst_meta bl c'1, subst_meta bl c'2)
    | DOPN(op, c') -> DOPN(op, Array.map (subst_meta bl) c')
    | DLAM(x,c') -> DLAM(x, subst_meta bl c')
    | CLam(na,t,c) -> CLam(na,subst_meta bl t,subst_meta bl c) 
    | CPrd(na,t,c) -> CPrd(na,subst_meta bl t,subst_meta bl c) 
    | CLet(na,b,t,c) -> CLet(na,subst_meta bl b,subst_meta bl t,
			     subst_meta bl c)
    | _ -> c

(* Substitute only a list of locations locs, the empty list is
   interpreted as substitute all, if 0 is in the list then no
   substitution is done the list may contain only negative occurrences
   that will not be substituted. *)

let subst_term_occ_gen locs occ c t =
  let pos = ref occ in
  let except = List.for_all (fun n -> n<0) locs in
  let rec substcheck k c t =
    if except or List.exists (function u -> u >= !pos) locs then
      substrec k c t
    else 
      t
  and substrec k c t =
    if eq_constr t c then
      let r = 
	if except then 
	  if List.mem (- !pos) locs then t else (Rel k)
	else 
	  if List.mem !pos locs then (Rel k) else t
      in incr pos; r
    else
      match t with
	| DOPN((Const _ | MutConstruct _ | MutInd _), _) -> t
	| DOPN(i,cl) -> 
	    let cl' =
	      Array.fold_left (fun lfd f -> substcheck k c f :: lfd) [] cl
            in 
	    DOPN(i,Array.of_list (List.rev cl'))
	| DOP2(i,t1,t2) -> 
	    let t1' = substrec k c t1 in
            let t2' = substcheck k c t2 in
            DOP2(i,t1',t2')
	| DOP1(i,t) -> 
	    DOP1(i,substrec k c t)
	| DLAM(n,t) -> 
            DLAM(n,substcheck (k+1) (lift 1 c) t)
	| DLAMV(n,cl) -> 
	     let cl' =   
               Array.fold_left 
		 (fun lfd f -> substcheck (k+1) (lift 1 c) f ::lfd)
		 [] cl
             in 
	     DLAMV(n,Array.of_list (List.rev cl'))
	| CLam(na,t,c2) ->
	    let t' = substrec k c t in
            let c2' = substcheck (k+1) (lift 1 c) c2 in
	    CLam(na,t',c2')
	| CPrd(na,t,c2) ->
	    let t' = substrec k c t in
            let c2' = substcheck (k+1) (lift 1 c) c2 in
	    CPrd(na,t',c2')
	| CLet(na,b,t,c2) ->
	    let b' = substrec k c b in
	    let t' = substrec k c t in
            let c2' = substcheck (k+1) (lift 1 c) c2 in
	    CLet(na,b',t',c2')
	| DOP0 _ | VAR _ | Rel _ -> t
  in
  let t' = substcheck 1 c t in
  (!pos, t')

let subst_term_occ locs c t = 
  if locs = [] then
    subst_term c t
  else if List.mem 0 locs then 
    t
  else 
    let (nbocc,t') = subst_term_occ_gen locs 1 c t in
    if List.exists (fun o -> o >= nbocc or o <= -nbocc) locs then
      errorlabstrm "subst_term_occ" [< 'sTR "Too few occurences" >];
    t'

let subst_term_occ_decl locs c (id,bodyopt,typ as d) =
  match bodyopt with
    | None -> (id,None,subst_term_occ locs c typ)
    | Some body -> 
	if locs = [] then
	  (id,Some (subst_term c body),typed_app (subst_term c) typ)
	else if List.mem 0 locs then 
	  d
	else 
	  let (nbocc,body') = subst_term_occ_gen locs 1 c body in
	  let (nbocc',t') = typed_app (subst_term_occ_gen locs nbocc c) typ in
	  if List.exists (fun o -> o >= nbocc' or o <= -nbocc') locs then
	    errorlabstrm "subst_term_occ_decl" [< 'sTR "Too few occurences" >];
	  (id,Some body',t')
  
(***************************)
(* occurs check functions  *)                         
(***************************)

let rec occur_meta = function
  | CPrd(_,t,c)      -> (occur_meta t) or (occur_meta c)
  | CLam(_,t,c)      -> (occur_meta t) or (occur_meta c)
  | CLet(_,b,t,c)    -> (occur_meta b) or (occur_meta t) or (occur_meta c)
  | DOPN(_,cl)        -> (array_exists occur_meta cl)
  | DOP2(Cast,c,t)    -> occur_meta c or occur_meta t
  | DOP0(Meta(_))     -> true
  | _                 -> false

let occur_existential = 
  let rec occrec = function
    | DOPN(Evar _,_) -> true
    | DOPN(_,cl) -> array_exists occrec cl
    | DOP2(_,c1,c2) -> occrec c1 or occrec c2
    | DOP1(_,c) -> occrec c
    | DLAM(_,c) -> occrec c
    | DLAMV(_,cl) -> array_exists occrec cl
    | CPrd(_,t,c)   -> (occrec t) or (occrec c)
    | CLam(_,t,c)   -> (occrec t) or (occrec c)
    | CLet(_,b,t,c) -> (occrec b) or (occrec t) or (occrec c)
    | _ -> false
  in 
  occrec

(***************************)
(* hash-consing functions  *)                         
(***************************)

let comp_term t1 t2 =
  match (t1,t2) with
    | (DOP0 o1, DOP0 o2) -> o1==o2
    | (DOP1(o1,t1), DOP1(o2,t2)) -> o1==o2 & t1==t2
    | (DOP2(o1,t1,u1), DOP2(o2,t2,u2)) -> o1==o2 & t1==t2 & u1==u2
    | (DOPN(o1,v1), DOPN(o2,v2)) ->
        (o1==o2) & (Array.length v1 = Array.length v2)
        & array_for_all2 (==) v1 v2
    | (DLAM(x1,t1), DLAM(x2,t2)) -> x1==x2 & t1==t2
    | (DLAMV(x1,v1), DLAMV(x2,v2)) ->
        (x1==x2) & (Array.length v1 = Array.length v2)
        & array_for_all2 (==) v1 v2
    | CLam(x1,t1,c1), CLam(x2,t2,c2) ->	(x1==x2) & (t1==t2) & (c1==c2)
    | CPrd(x1,t1,c1), CPrd(x2,t2,c2) ->	(x1==x2) & (t1==t2) & (c1==c2)
    | CLet(x1,b1,t1,c1), CLet (x2,b2,t2,c2) ->
	(x1==x2) & (b1==b2) & (t1==t2) & (c1==c2)
    | (Rel i, Rel j) -> i=j
    | (VAR x, VAR y) -> x==y
    | _ -> false

let hash_term (sh_rec,(sh_op,sh_na,sh_id)) t =
  match t with
    | DOP0 o -> DOP0 (sh_op o)
    | DOP1(o,t) -> DOP1(sh_op o, sh_rec t)
    | DOP2(o,t1,t2) -> DOP2(sh_op o, sh_rec t1, sh_rec t2)
    | DOPN(o,v) -> DOPN(sh_op o, Array.map sh_rec v)
    | DLAM(n,t) -> DLAM(sh_na n, sh_rec t)
    | DLAMV(n,v) -> DLAMV(sh_na n, Array.map sh_rec v)
    | CLam (n,t,c)   -> CLam (sh_na n, sh_rec t, sh_rec c)  
    | CPrd (n,t,c)   -> CPrd (sh_na n, sh_rec t, sh_rec c)
    | CLet (n,b,t,c) -> CLet (sh_na n, sh_rec b, sh_rec t, sh_rec c)
    | Rel i -> t
    | VAR x -> VAR (sh_id x) 

module Hsorts =
  Hashcons.Make(
    struct
      type t = sorts
      type u = section_path -> section_path
      let hash_sub hsp = function
	| Prop c -> Prop c
        | Type {u_sp=sp; u_num=n} -> Type {u_sp=hsp sp; u_num=n}
      let equal s1 s2 =
        match (s1,s2) with
          | (Prop c1, Prop c2) -> c1=c2
          | (Type {u_sp=sp1; u_num=n1}, Type {u_sp=sp2; u_num=n2}) ->
              sp1==sp2 & n1=n2
          |_ -> false
      let hash = Hashtbl.hash
    end)

module Hoper =
  Hashcons.Make(
    struct
      type t = sorts oper
      type u = (sorts -> sorts)
               * (section_path -> section_path) * (string -> string)
      let hash_sub (hsort,hsp,hstr) = function
	| XTRA s -> XTRA (hstr s)
        | Sort s -> Sort (hsort s)
        | Const sp -> Const (hsp sp)
        | MutInd (sp,i) -> MutInd (hsp sp, i)
        | MutConstruct ((sp,i),j) -> MutConstruct ((hsp sp,i),j)
        | MutCase ci as t -> t (* TO DO: extract ind_sp *)
        | t -> t
      let equal o1 o2 =
        match (o1,o2) with
          | (XTRA s1, XTRA s2) -> s1==s2
          | (Sort s1, Sort s2) -> s1==s2
          | (Const sp1, Const sp2) -> sp1==sp2
          | (MutInd (sp1,i1), MutInd (sp2,i2)) -> sp1==sp2 & i1=i2
          | (MutConstruct((sp1,i1),j1), MutConstruct((sp2,i2),j2)) ->
              sp1==sp2 & i1=i2 & j1=j2
          | (MutCase ci1,MutCase ci2) -> ci1==ci2 (* A simplification ?? *)
          | _ -> o1=o2
      let hash = Hashtbl.hash
    end)    

module Hconstr =
  Hashcons.Make(
    struct
      type t = constr
      type u = (constr -> constr)
               * ((sorts oper -> sorts oper) * (name -> name) 
                  * (identifier -> identifier))
      let hash_sub = hash_term
      let equal = comp_term
      let hash = Hashtbl.hash
    end)

let hcons_oper (hsorts,hsp,hstr) =
  Hashcons.simple_hcons Hoper.f (hsorts,hsp,hstr)

let hcons_term (hsorts,hsp,hname,hident,hstr) =
  let hoper = hcons_oper (hsorts,hsp,hstr) in
  Hashcons.recursive_hcons Hconstr.f (hoper,hname,hident)

module Htype =
  Hashcons.Make(
    struct
      type t = typed_type
      type u = (constr -> constr) * (sorts -> sorts)
(*
      let hash_sub (hc,hs) j = {body=hc j.body; typ=hs j.typ}
      let equal j1 j2 = j1.body==j2.body & j1.typ==j2.typ
*)
(**)
      let hash_sub (hc,hs) j = hc j
      let equal j1 j2 = j1==j2
(**)
      let hash = Hashtbl.hash
    end)

let hcons_constr (hspcci,hspfw,hname,hident,hstr) =
  let hsortscci = Hashcons.simple_hcons Hsorts.f hspcci in
  let hsortsfw = Hashcons.simple_hcons Hsorts.f hspfw in
  let hcci = hcons_term (hsortscci,hspcci,hname,hident,hstr) in
  let hfw = hcons_term (hsortsfw,hspfw,hname,hident,hstr) in
  let htcci = Hashcons.simple_hcons Htype.f (hcci,hsortscci) in
  (hcci,hfw,htcci)

let hcons1_constr c =
  let hnames = hcons_names() in
  let (hc,_,_) = hcons_constr hnames in
  hc c

(* Puts off the casts *)
let put_off_casts = strip_outer_cast

(*Verifies if the constr has an head constant*)
let is_hd_const=function
  | DOPN(AppL,t) ->
      (match (t.(0)) with
         | DOPN(Const c,_) ->
             Some (Const c,Array.of_list (List.tl (Array.to_list t)))
         |_ -> None)
  |_ -> None

(* Abstract decomposition of constr to deal with generic functions *)

type constr_operator =
  | OpMeta of int
  | OpSort of sorts
  | OpRel of int | OpVar of identifier
  | OpCast | OpProd of name | OpLambda of name | OpLetIn of name
  | OpAppL | OpConst of section_path
  | OpEvar of existential_key
  | OpMutInd of inductive_path
  | OpMutConstruct of constructor_path
  | OpMutCase of case_info
  | OpRec of fix_kind * name list

let splay_constr = function
  | Rel n                         -> OpRel n, [||]
  | VAR id                        -> OpVar id, [||] 
  | DOP0 (Meta n)                 -> OpMeta n, [||]
  | DOP0 (Sort s)                 -> OpSort s, [||]
  | DOP2 (Cast, t1, t2)           -> OpCast, [|t1;t2|]
  | CPrd (x, t1, t2)              -> OpProd x, [|t1;t2|]
  | CLam (x, t1, t2)              -> OpLambda x, [|t1;t2|]
  | CLet (x, b, t1, t2)           -> OpLetIn x, [|b;t1;t2|]
  | DOPN (AppL,a)                 -> OpAppL, a
  | DOPN (Const sp, a)            -> OpConst sp, a
  | DOPN (Evar sp, a)             -> OpEvar sp, a
  | DOPN (MutInd ind_sp, l)       -> OpMutInd ind_sp, l
  | DOPN (MutConstruct cstr_sp,l) -> OpMutConstruct cstr_sp, l
  | DOPN (MutCase ci,v)           -> OpMutCase ci, v
  | DOPN ((Fix (f,i),a)) as c     ->
      let (fi,(tl,lna,bl)) = destFix c in
      OpRec (RFix fi,lna), Array.append tl bl
  | DOPN ((CoFix i),a) as c       ->
      let (fi,(tl,lna,bl)) = destCoFix c in
      OpRec (RCoFix fi,lna), Array.append tl bl
  | _ -> errorlabstrm "Term.splay_term" [< 'sTR "ill-formed constr" >]

let gather_constr = function
  | OpRel n, [||]  -> Rel n
  | OpVar id, [||] -> VAR id
  | OpMeta n, [||] -> DOP0 (Meta n)
  | OpSort s, [||] -> DOP0 (Sort s)
  | OpCast, [|t1;t2|]     -> DOP2 (Cast, t1, t2)
  | OpProd x, [|t1;t2|]   -> mkProd (x, t1, t2)
  | OpLambda x, [|t1;t2|] -> mkLambda (x, t1, t2)
  | OpLetIn x, [|b;t1;t2|] -> mkLetIn (x, b, t1, t2)
  | OpAppL, a     -> DOPN (AppL, a)
  | OpConst sp, a -> DOPN (Const sp, a)
  | OpEvar sp, a  -> DOPN (Evar sp, a) 
  | OpMutInd ind_sp, l        -> DOPN (MutInd ind_sp, l) 
  | OpMutConstruct cstr_sp, l -> DOPN (MutConstruct cstr_sp, l)
  | OpMutCase ci,  v    -> DOPN (MutCase ci, v)   
  | OpRec (RFix fi,lna), a  ->
      let n = Array.length a / 2 in
      mkFix (fi,(Array.sub a 0 n, lna, Array.sub a n n))
  | OpRec (RCoFix i,lna), a ->
      let n = Array.length a / 2 in
      mkCoFix (i,(Array.sub a 0 n, lna, Array.sub a n n))
  | _ -> errorlabstrm "Term.gather_term" [< 'sTR "ill-formed constr" >]

let rec mycombine l1 l3 =
  match (l1, l3) with
    ([], []) -> []
  | (a1::l1, a3::l3) -> (a1, None, a3) :: mycombine l1 l3
  | (_, _) -> invalid_arg "mycombine"

let rec mysplit = function
    [] -> ([], [])
  | (x, _, z)::l -> let (rx, rz) = mysplit l in (x::rx, z::rz)

let splay_constr_with_binders = function
  | Rel n                         -> OpRel n, [], [||]
  | VAR id                        -> OpVar id, [], [||] 
  | DOP0 (Meta n)                 -> OpMeta n, [], [||]
  | DOP0 (Sort s)                 -> OpSort s, [], [||]
  | DOP2 (Cast, t1, t2)           -> OpCast, [], [|t1;t2|]
  | CPrd (x, t1, t2)              -> OpProd x, [x,None,t1], [|t2|]
  | CLam (x, t1, t2)              -> OpLambda x, [x,None,t1], [|t2|]
  | CLet (x, b, t1, t2)           -> OpLetIn x, [x,Some b,t1], [|t2|]
  | DOPN (AppL,a)                 -> OpAppL, [], a
  | DOPN (Const sp, a)            -> OpConst sp, [], a
  | DOPN (Evar sp, a)             -> OpEvar sp, [], a
  | DOPN (MutInd ind_sp, l)       -> OpMutInd ind_sp, [], l
  | DOPN (MutConstruct cstr_sp,l) -> OpMutConstruct cstr_sp, [], l
  | DOPN (MutCase ci,v)           -> OpMutCase ci, [], v
  | DOPN ((Fix (f,i),a)) as c     ->
      let (fi,(tl,lna,bl)) = destFix c in
      let n = Array.length bl in
      let ctxt = mycombine
		   (List.rev lna)
		   (Array.to_list (Array.mapi lift tl)) in
      OpRec (RFix fi,lna), ctxt, bl
  | DOPN ((CoFix i),a) as c       ->
      let (fi,(tl,lna,bl)) = destCoFix c in
      let n = Array.length bl in
      let ctxt = mycombine
		   (List.rev lna)
		   (Array.to_list (Array.mapi lift tl)) in
      OpRec (RCoFix fi,lna), ctxt, bl
  | _ -> errorlabstrm "Term.splay_term" [< 'sTR "ill-formed constr" >]

let gather_constr_with_binders = function
  | OpRel n, [], [||]  -> Rel n
  | OpVar id, [], [||] -> VAR id
  | OpMeta n, [], [||] -> DOP0 (Meta n)
  | OpSort s, [], [||] -> DOP0 (Sort s)
  | OpCast, [], [|t1;t2|]     -> DOP2 (Cast, t1, t2)
  | OpProd _, [x,None,t1], [|t2|]   -> mkProd (x, t1, t2)
  | OpLambda _, [x,None,t1], [|t2|] -> mkLambda (x, t1, t2)
  | OpLetIn _, [x,Some b,t1], [|t2|] -> mkLetIn (x, b, t1, t2)
  | OpAppL, [], a     -> DOPN (AppL, a)
  | OpConst sp, [], a -> DOPN (Const sp, a)
  | OpEvar sp, [], a  -> DOPN (Evar sp, a) 
  | OpMutInd ind_sp, [], l        -> DOPN (MutInd ind_sp, l) 
  | OpMutConstruct cstr_sp, [], l -> DOPN (MutConstruct cstr_sp, l)
  | OpMutCase ci, [], v    -> DOPN (MutCase ci, v)   
  | OpRec (RFix fi,lna), ctxt, bl  ->
      let (lna, tl) = mysplit ctxt in
      let tl = Array.mapi (fun i -> lift (-i)) (Array.of_list tl) in
      mkFix (fi,(tl, List.rev lna, bl))
  | OpRec (RCoFix i,lna), ctxt, bl ->
      let (lna, tl) = mysplit ctxt in
      let tl = Array.mapi (fun i -> lift (-i)) (Array.of_list tl) in
      mkCoFix (i,(tl, List.rev lna, bl))
  | _ -> errorlabstrm "Term.gather_term" [< 'sTR "ill-formed constr" >]

let generic_fold_left f acc bl tl =
  let acc =
    List.fold_left 
      (fun acc (_,bo,t) ->
	 match bo with
	   | None -> f acc t
	   | Some b -> f (f acc b) t) acc bl in
  Array.fold_left f acc tl

let fold_constr f acc c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> acc
  | IsCast (c,t) -> f (f acc c) t
  | IsProd (_,t,c) -> f (f acc t) c
  | IsLambda (_,t,c) -> f (f acc t) c
  | IsLetIn (_,b,t,c) -> f (f (f acc b) t) c
  | IsAppL (c,l) -> List.fold_left f (f acc c) l
  | IsEvar (_,l) -> Array.fold_left f acc l
  | IsConst (_,l) -> Array.fold_left f acc l
  | IsMutInd (_,l) -> Array.fold_left f acc l
  | IsMutConstruct (_,l) -> Array.fold_left f acc l
  | IsMutCase (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | IsFix (_,(tl,_,bl)) -> Array.fold_left f (Array.fold_left f acc tl) bl
  | IsCoFix (_,(tl,_,bl)) -> Array.fold_left f (Array.fold_left f acc tl) bl

let fold_constr_with_binders g f n acc c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> acc
  | IsCast (c,t) -> f n (f n acc c) t
  | IsProd (_,t,c) -> f (g n) (f n acc t) c
  | IsLambda (_,t,c) -> f (g n) (f n acc t) c
  | IsLetIn (_,b,t,c) -> f (g n) (f n (f n acc b) t) c
  | IsAppL (c,l) -> List.fold_left (f n) (f n acc c) l
  | IsEvar (_,l) -> Array.fold_left (f n) acc l
  | IsConst (_,l) -> Array.fold_left (f n) acc l
  | IsMutInd (_,l) -> Array.fold_left (f n) acc l
  | IsMutConstruct (_,l) -> Array.fold_left (f n) acc l
  | IsMutCase (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | IsFix (_,(tl,_,bl)) -> 
      let n' = iterate g (Array.length tl) n in
      Array.fold_left (f n') (Array.fold_left (f n) acc tl) bl
  | IsCoFix (_,(tl,_,bl)) ->
      let n' = iterate g (Array.length tl) n in
      Array.fold_left (f n') (Array.fold_left (f n) acc tl) bl

let iter_constr_with_binders g f n c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> ()
  | IsCast (c,t) -> f n c; f n t
  | IsProd (_,t,c) -> f n t; f (g n) c
  | IsLambda (_,t,c) -> f n t; f (g n) c
  | IsLetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | IsAppL (c,l) -> f n c; List.iter (f n) l
  | IsEvar (_,l) -> Array.iter (f n) l
  | IsConst (_,l) -> Array.iter (f n) l
  | IsMutInd (_,l) -> Array.iter (f n) l
  | IsMutConstruct (_,l) -> Array.iter (f n) l
  | IsMutCase (_,p,c,bl) -> f n p; f n c; Array.iter (f n) bl
  | IsFix (_,(tl,_,bl)) -> 
      Array.iter (f n) tl; Array.iter (f (iterate g (Array.length tl) n)) bl
  | IsCoFix (_,(tl,_,bl)) ->
      Array.iter (f n) tl; Array.iter (f (iterate g (Array.length tl) n)) bl

let map_constr f c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> mkCast (f c, f t)
  | IsProd (na,t,c) -> mkProd (na, f t, f c)
  | IsLambda (na,t,c) -> mkLambda (na, f t, f c)
  | IsLetIn (na,b,t,c) -> mkLetIn (na, f b, f t, f c)
  | IsAppL (c,l) -> applist (f c, List.map f l)
  | IsEvar (e,l) -> mkEvar (e, Array.map f l)
  | IsConst (c,l) -> mkConst (c, Array.map f l)
  | IsMutInd (c,l) -> mkMutInd (c, Array.map f l)
  | IsMutConstruct (c,l) -> mkMutConstruct (c, Array.map f l)
  | IsMutCase (ci,p,c,bl) -> mkMutCase (ci, f p, f c, Array.map f bl)
  | IsFix (ln,(tl,lna,bl)) -> mkFix (ln,(Array.map f tl,lna,Array.map f bl))
  | IsCoFix(ln,(tl,lna,bl)) -> mkCoFix (ln,(Array.map f tl,lna,Array.map f bl))

let map_constr_with_binders g f l c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> mkCast (f l c, f l t)
  | IsProd (na,t,c) -> mkProd (na, f l t, f (g na l) c)
  | IsLambda (na,t,c) -> mkLambda (na, f l t, f (g na l) c)
  | IsLetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g na l) c)
  | IsAppL (c,al) -> applist (f l c, List.map (f l) al)
  | IsEvar (e,al) -> mkEvar (e, Array.map (f l) al)
  | IsConst (c,al) -> mkConst (c, Array.map (f l) al)
  | IsMutInd (c,al) -> mkMutInd (c, Array.map (f l) al)
  | IsMutConstruct (c,al) -> mkMutConstruct (c, Array.map (f l) al)
  | IsMutCase (ci,p,c,bl) -> mkMutCase (ci, f l p, f l c, Array.map (f l) bl)
  | IsFix (ln,(tl,lna,bl)) ->
      let l' = List.fold_right g lna l in
      mkFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))
  | IsCoFix(ln,(tl,lna,bl)) ->
      let l' = List.fold_right g lna l in
      mkCoFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))
