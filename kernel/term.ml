
(* $Id$ *)

(* This module instanciates the structure of generic deBruijn terms to Coq *)

open Util
open Pp
open Names
open Generic
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
  | AppL | Const of section_path | Abst of section_path
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

type constr = sorts oper term

type 'a judge = { body : constr; typ : 'a }

type typed_type = sorts judge
type typed_term = typed_type judge

let make_typed t s = { body = t; typ = s }

let typed_app f tt = { body = f tt.body; typ = tt.typ }

let body_of_type ty = ty.body
let level_of_type t = (t.typ : sorts)

let incast_type tty = DOP2 (Cast, tty.body, (DOP0 (Sort tty.typ)))

let outcast_type = function
   DOP2 (Cast, b, DOP0 (Sort s)) -> {body=b; typ=s}
  | _ -> anomaly "outcast_type: Not an in-casted type judgement"

(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let mkRel   n = (Rel n)

(* Constructs an existential variable named "?" *)
let mkExistential = (DOP0 (XTRA "ISEVAR"))

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
let mkCast t1 t2 =
  match t1 with
    | DOP2(Cast,t,_) -> DOP2(Cast,t,t2)
    | _ -> (DOP2 (Cast,t1,t2))

(* Constructs the product (x:t1)t2 *)
let mkProd x t1 t2 = (DOP2 (Prod,t1,(DLAM (x,t2))))

(* non-dependant product t1 -> t2 *)
let mkArrow t1 t2 = mkProd Anonymous t1 t2

(* named product *)
let mkNamedProd name typ c = mkProd (Name name) typ (subst_var name c)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda x t1 t2 = (DOP2 (Lambda,t1,(DLAM (x,t2))))
let mkNamedLambda name typ c = mkLambda (Name name) typ (subst_var name c)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
let mkAppL a = DOPN (AppL, a)
let mkAppList a l = DOPN (AppL, Array.of_list (a::l))

(* Constructs a constant *) 
(* The array of terms correspond to the variables introduced in the section *)
let mkConst (sp,a) = DOPN (Const  sp, a)

(* Constructs an existential variable *)
let mkEvar n a = DOPN (Evar n, a)

(* Constructs an abstract object *)
let mkAbst sp a = DOPN (Abst sp, a)

(* Constructs the ith (co)inductive type of the block named sp *)
(* The array of terms correspond to the variables introduced in the section *)
let mkMutInd (ind_sp,l) = DOPN (MutInd ind_sp, l)

(* Constructs the jth constructor of the ith (co)inductive type of the 
   block named sp. The array of terms correspond to the variables
   introduced in the section *)
let mkMutConstruct (cstr_sp,l) =  DOPN (MutConstruct cstr_sp,l)

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkMutCase ci p c ac = 
  DOPN (MutCase ci, Array.append [|p;c|] (Array.of_list ac))
let mkMutCaseA ci p c ac = 
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

   Warning: as an invariant the ti are casted during the Fix formation;
   these casts are then used by destFix
*)
let in_fixcast {body=b; typ=s} = DOP2 (Cast, b, DOP0 (Sort s))

(* Here, we assume the body already constructed *)
let mkFixDlam recindxs i jtypsarray body =
  let typsarray = Array.map in_fixcast jtypsarray in
  DOPN (Fix (recindxs,i),Array.append typsarray body)

let mkFix recindxs i jtypsarray funnames bodies = 
  let rec wholebody l = 
    match l with 
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
  let typsarray = Array.map in_fixcast jtypsarray in
  DOPN ((CoFix i),(Array.append typsarray body))

let mkCoFix i jtypsarray funnames bodies = 
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

let isMETA = function DOP0(Meta _) -> true | _ -> false

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

let cast_term = function
  | DOP2(Cast,c,t) -> c
  | _ -> anomaly "found a type which did not contain a cast (cast_term)"

let cast_type = function
  | DOP2(Cast,c,t) -> t
  | _ -> anomaly "found a type which did not contain a cast (cast_type)"

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
    | DOPL(oper,cl) -> DOPL(oper,List.map strip_all_casts cl)
    | DLAM(na,c) -> DLAM(na,strip_all_casts c)
    | DLAMV(na,c) -> DLAMV(na,Array.map (under_outer_cast strip_all_casts) c)
    | VAR _ as t -> t
    | Rel _ as t -> t

(* Destructs the product (x:t1)t2 *)
let destProd = function 
  | DOP2 (Prod, t1, (DLAM (x,t2))) -> (x,t1,t2) 
  | _ -> invalid_arg "destProd"

let rec hd_of_prod prod =
  match strip_outer_cast prod with
    | DOP2(Prod,c,DLAM(n,t')) -> hd_of_prod t'
    |  t -> t

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
  | DOP2 (Lambda, t1, (DLAM (x,t2))) -> (x,t1,t2) 
  | _ -> invalid_arg "destLambda"

(* Destructs an application *)
let destAppL = function 
  | (DOPN (AppL,a)) -> a
  | _ -> invalid_arg "destAppL"

let destApplication =  function
  | (DOPN (AppL,a)) when Array.length a <> 0 -> (a.(0), array_tl a)
  | _ -> invalid_arg "destApplication"

let isAppL = function DOPN(AppL,_) -> true | _ -> false

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

let out_fixcast = function
  | DOP2 (Cast, b, DOP0 (Sort s)) -> { body = b; typ = s }
  | _ -> anomaly "destFix: malformed recursive definition"

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
      (recindxs,i,Array.map out_fixcast types,funnames,bodies)
  | _ -> invalid_arg "destFix"
	
let destCoFix = function 
  | DOPN ((CoFix i),a) ->
      let (types,funnames,bodies) = destGralFix a in
      (i,Array.map out_fixcast types,funnames,bodies)
  | _ -> invalid_arg "destCoFix"

(* Provisoire, le temps de maitriser les cast *)
let destUntypedFix = function 
  | DOPN (Fix (recindxs,i),a) -> 
      let (types,funnames,bodies) = destGralFix a in 
      (recindxs,i,types,funnames,bodies)
  | _ -> invalid_arg "destFix"

let destUntypedCoFix = function 
  | DOPN (CoFix i,a) -> 
      let (types,funnames,bodies) = destGralFix a in 
      (i,types,funnames,bodies)
  | _ -> invalid_arg "destCoFix"


(******************)
(* Term analysis  *)
(******************)

type existential = int * constr array
type constant = section_path * constr array
type constructor = constructor_path * constr array
type inductive = inductive_path * constr array

type kindOfTerm = 
  | IsRel          of int
  | IsMeta         of int
  | IsVar          of identifier
  | IsXtra         of string
  | IsSort         of sorts
  | IsCast         of constr * constr
  | IsProd         of name * constr * constr
  | IsLambda       of name * constr * constr
  | IsAppL         of constr * constr list
  | IsAbst         of section_path * constr array
  | IsEvar         of existential
  | IsConst        of constant
  | IsMutInd       of inductive
  | IsMutConstruct of constructor
  | IsMutCase      of case_info * constr * constr * constr array
  | IsFix          of int array * int * constr array * name list * constr array
  | IsCoFix        of int * constr array * name list * constr array


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
    | DOP2 (Prod, t1, (DLAM (x,t2)))       -> IsProd (x,t1,t2) 
    | DOP2 (Lambda, t1, (DLAM (x,t2)))     -> IsLambda (x,t1,t2)
    | DOPN (AppL,a) when Array.length a <> 0 -> 
	IsAppL (a.(0), List.tl (Array.to_list a))
    | DOPN (Const sp, a)                   -> IsConst (sp,a)
    | DOPN (Evar sp, a)                    -> IsEvar (sp,a)
    | DOPN (Abst sp, a)                    -> IsAbst (sp, a)
    | DOPN (MutInd ind_sp, l)              -> IsMutInd (ind_sp,l)
    | DOPN (MutConstruct cstr_sp,l)        -> IsMutConstruct (cstr_sp,l)
    | DOPN (MutCase ci,v)                  -> 
	IsMutCase (ci,v.(0),v.(1),Array.sub v 2 (Array.length v - 2))
    | DOPN ((Fix (recindxs,i),a))           ->  
      	let (types,funnames,bodies) = destGralFix a in
	IsFix (recindxs,i,types,funnames,bodies)
    | DOPN ((CoFix i),a)                    ->  
      	let (types,funnames,bodies) = destGralFix a in
      	IsCoFix (i,types,funnames,bodies)
    | _ -> errorlabstrm "Term.kind_of_term" [< 'sTR "ill-formed constr" >]

(***************************)
(* Other term constructors *)
(***************************)

let abs_implicit c = mkLambda Anonymous mkImplicit c
let lambda_implicit a = mkLambda (Name(id_of_string"y")) mkImplicit a
let lambda_implicit_lift n a = iterate lambda_implicit n (lift n a)

(* prod_it b [xn:Tn;..;x1:T1] = (x1:T1)..(xn:Tn)b *)
let prod_it = List.fold_left (fun c (n,t)  -> mkProd n t c)

(* lam_it b [xn:Tn;..;x1:T1] = [x1:T1]..[xn:Tn]b *)
let lam_it = List.fold_left (fun c (n,t)  -> mkLambda n t c)

(* prodn n [xn:Tn;..;x1:T1;Gamma] b = (x1:T1)..(xn:Tn)b *)
let prodn n env b =
  let rec prodrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, DOP2(Prod,t,DLAM(v,b)))
    | _ -> assert false
  in 
  prodrec (n,env,b)

(* lamn n [xn:Tn;..;x1:T1;Gamma] b = [x1:T1]..[xn:Tn]b *)
let lamn n env b =
  let rec lamrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> lamrec (n-1,  l, DOP2(Lambda,t,DLAM(v,b)))
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
      | DOP2(Prod,ty,DLAM(na,bd)) -> 
          DOP2(Lambda,ty,DLAM(na, to_lambda (n-1) bd))
      | DOP2(Cast,c,_) -> to_lambda n c
      | _   -> errorlabstrm "to_lambda" [<>]                      

let rec to_prod n lam =
  if n=0 then 
    lam
  else   
    match lam with 
      | DOP2(Lambda,ty,DLAM(na,bd)) -> 
          DOP2(Prod,ty,DLAM(na, to_prod (n-1) bd))
      | DOP2(Cast,c,_) -> to_prod n c
      | _   -> errorlabstrm "to_prod" [<>]                      
	    
(* pseudo-reduction rule:
 * [prod_app  s (Prod(_,B)) N --> B[N]
 * with an strip_outer_cast on the first argument to produce a product *)

let prod_app t n =
  match strip_outer_cast t with
    | DOP2(Prod,_,b) -> sAPP b n
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
let decompose_prod = 
  let rec prodec_rec l = function
    | DOP2(Prod,t,DLAM(x,c)) -> prodec_rec ((x,t)::l) c
    | DOP2(Cast,c,_)         -> prodec_rec l c
    | c                      -> l,c
  in 
  prodec_rec [] 

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam = 
  let rec lamdec_rec l = function
    | DOP2(Lambda,t,DLAM(x,c)) -> lamdec_rec ((x,t)::l) c
    | DOP2(Cast,c,_)         -> lamdec_rec l c
    | c                      -> l,c
  in 
  lamdec_rec [] 

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then error "decompose_prod_n: integer parameter must be positive";
  let rec prodec_rec l n c = 
    if n=0 then l,c 
    else match c with 
      | DOP2(Prod,t,DLAM(x,c)) -> prodec_rec ((x,t)::l) (n-1) c
      | DOP2(Cast,c,_)         -> prodec_rec l n c
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
      | DOP2(Lambda,t,DLAM(x,c)) -> lamdec_rec ((x,t)::l) (n-1) c
      | DOP2(Cast,c,_)           -> lamdec_rec l n c
      | c -> error "decompose_lam_n: not enough abstractions"
  in 
  lamdec_rec [] n 

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
let nb_lam = 
  let rec nbrec n = function
    | DOP2(Lambda,_,DLAM(_,c)) -> nbrec (n+1) c
    | DOP2(Cast,c,_) -> nbrec n c
    | _ -> n
  in 
  nbrec 0
    
(* similar to nb_lam, but gives the number of products instead *)
let nb_prod = 
  let rec nbrec n = function
    | DOP2(Prod,_,DLAM(_,c)) -> nbrec (n+1) c
    | DOP2(Cast,c,_) -> nbrec n c
    | _ -> n
  in 
  nbrec 0


(********************************************************************)
(*   various utility functions for implementing terms with bindings *)
(********************************************************************)

let extract_lifted (n,x) = lift n x
let insert_lifted x = (0,x)

(* l is a list of pairs (n:nat,x:constr), env is a stack of (na:name,T:constr)
   push_and_lift adds a component to env and lifts l one step *)
let push_and_lift (na,t) env l =
  ((na,t)::env, List.map (fun (n,x) -> (n+1,x)) l)


(* if T is not (x1:A1)(x2:A2)....(xn:An)T' then (push_and_liftl n env T l)
   raises an error else it gives ([x1,A1 ; x2,A2 ; ... ; xn,An]@env,T',l')
   where l' is l lifted n steps *)
let push_and_liftl n env t l = 
  let rec pushrec n t (env,l) =
    match (n,t) with
      | (0, _) -> (env,t,l)
      | (_, DOP2(Prod,t,DLAM(na,b))) -> 
          pushrec (n-1) b (push_and_lift (na,t) env l)
      | (_, DOP2(Cast,t,_)) -> pushrec n t (env,l)
      | _ -> error "push_and_liftl"
  in 
  pushrec n t (env,l)

(* if T is not (x1:A1)(x2:A2)....(xn:An)T' then (push_and_liftl n env T l)
   raises an error else it gives ([x1,A1 ; x2,A2 ; ... ; xn,An]@env,T',l')
   where l' is l lifted n steps *)
let push_lam_and_liftl n env t l = 
  let rec pushrec n t (env,l) =
    match (n,t) with
      | (0, _) -> (env,t,l)
      | (_, DOP2(Lambda,t,DLAM(na,b))) -> 
	  pushrec (n-1) b (push_and_lift (na,t) env l)
      | (_, DOP2(Cast,t,_)) -> pushrec n t (env,l)
      | _ -> error "push_lam_and_liftl"
  in 
  pushrec n t (env,l)

(* l is a list of pairs (n:nat,x:constr), tlenv is a stack of
(na:name,T:constr), B : constr, na : name
(prod_and_pop ((na,T)::tlenv) B l) gives (tlenv, (na:T)B, l')
where l' is l lifted down one step *)
let prod_and_pop env b l =
  match env with
    | [] -> error "prod_and_pop"
    | (na,t)::tlenv ->
        (tlenv,DOP2(Prod,t,DLAM(na,b)),
         List.map (function 
                       (0,x) -> (0,lift (-1) x)
                     | (n,x) -> (n-1,x)) l)

(* recusively applies prod_and_pop :
if env = [na1:T1 ; na2:T2 ; ... ; nan:Tn]@tlenv
then
(prod_and_popl n env T l) gives (tlenv,(nan:Tn)...(na1:Ta1)T,l') where
l' is l lifted down n steps *)
let prod_and_popl n env t l = 
  let rec poprec = function
    | (0, (env,b,l)) -> (env,b,l)
    | (n, ([],_,_))  -> error "prod_and_popl"
    | (n, (env,b,l)) -> poprec (n-1, prod_and_pop env b l)
  in 
  poprec (n,(env,t,l))

(* similar to prod_and_pop, but gives [na:T]B intead of (na:T)B *)
let lam_and_pop env b l =
  match env with
    | [] -> error "lam_and_pop"
    | (na,t)::tlenv ->
        (tlenv,DOP2(Lambda,t,DLAM(na,b)),
         List.map (function
                       (0,x) -> (0,lift (-1) x)
                     | (n,x) -> (n-1,x)) l)

(* similar to lamn_and_pop but generates new names whenever the name is 
 *  Anonymous *)
let lam_and_pop_named env body l acc_ids =
  match env with
    | [] -> error "lam_and_pop"
    | (na,t)::tlenv ->
 	let id = match na with
	  | Anonymous -> next_ident_away (id_of_string "a") acc_ids
	  | Name id -> id
	in
	(tlenv,DOP2(Lambda,t,DLAM((Name id),body)),
         List.map (function
                     | (0,x) -> (0,lift (-1) x)
                     | (n,x) -> (n-1,x)) l,
         (id::acc_ids))

(* similar to prod_and_popl but gives [nan:Tan]...[na1:Ta1]B instead of
 * (nan:Tan)...(na1:Ta1)B *)
let lam_and_popl n env t l = 
  let rec poprec = function
    | (0, (env,b,l)) -> (env,b,l)
    | (n, ([],_,_)) -> error "lam_and_popl"
    | (n, (env,b,l)) -> poprec (n-1, lam_and_pop env b l)
  in 
  poprec (n,(env,t,l))

(* similar to prod_and_popl but gives [nan:Tan]...[na1:Ta1]B instead of
 * but it generates names whenever nai=Anonymous *)

let lam_and_popl_named  n env t l = 
  let rec poprec = function
    | (0, (env,b,l,_)) -> (env,b,l)
    | (n, ([],_,_,_)) -> error "lam_and_popl"
    | (n, (env,b,l,acc_ids)) -> poprec (n-1, lam_and_pop_named env b l acc_ids)
  in 
  poprec (n,(env,t,l,[]))

(* [lambda_ize n T endpt]
 * will pop off the first [n] products in [T], then stick in [endpt],
 * properly lifted, and then push back the products, but as lambda-
 * abstractions *)
let lambda_ize n t endpt =
  let env = [] 
  and carry = [insert_lifted endpt] in
  let env, endpt = 
    match push_and_liftl n env t carry with
      | (env,_,[endpt]) ->   env, endpt
      | _ -> anomaly "bud in Term.lamda_ize" 
  in
  let t = extract_lifted endpt in
  match lam_and_popl n env t [] with
    | (_,t,[]) -> t
    | _ -> anomaly "bud in Term.lamda_ize"
	  
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
let strip_head_cast = function
  | DOPN(AppL,cl) -> 
      let rec collapse_rec = function
	| (DOPN(AppL,cl),l2) -> collapse_rec(array_hd cl, array_app_tl cl l2)
	| (DOP2(Cast,c,t),l) -> collapse_rec(c,l)
	| (f,[]) -> f
	| (f,l) -> let v = Array.of_list (f::l) in DOPN(AppL,v)
      in 
      collapse_rec(array_hd cl, array_app_tl cl [])
  | c -> c

(* (occur_const (s:section_path) c) -> true if constant s occurs in c,
 * false otherwise *)
let occur_const s = occur_opern (Const s)

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

   NOTE : the case of DOPL is not handled...
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
      	       	   replace_vars
      	       	     (List.combine hyps 
			(array_map_to_list make_substituend cl')) body
             | None -> anomaly ("a constant which was never"^
      	       	       		" supposed to appear has just appeared")
	 with Not_found -> DOPN(Const sp,cl'))

    | DOP1(i,c)         -> DOP1(i,substrec c)
    | DOPN(oper,cl)     -> DOPN(oper,Array.map substrec cl)
    | DOP2(oper,c1,c2)  -> DOP2(oper,substrec c1,substrec c2)
    | DLAM(na,c)        -> DLAM(na,substrec c)
    | DLAMV(na,v)       -> DLAMV(na,Array.map substrec v)
    | x                 -> x
  in 
  if const_alist = [] then function x -> x else substrec

(* NOTE : the case of DOPL is not handled by whd_castapp_stack *)
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
  (m = n) or
  match (strip_head_cast m,strip_head_cast n) with
    | (DOP2(Cast,c1,_),c2) 	       -> eq_constr_rec c1 c2
    | (c1,DOP2(Cast,c2,_))              -> eq_constr_rec c1 c2
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
    | _ -> false

let eq_constr = eq_constr_rec

let rec eq_constr_with_meta_rec m n=
  (m=n) or 
  (match (strip_head_cast m,strip_head_cast n) with
     | (DOP2(Cast,c1,_),c2) 	       -> eq_constr_rec c1 c2
     | (c1,DOP2(Cast,c2,_))              -> eq_constr_rec c1 c2
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
     | _ -> false)

(* On reduit une serie d'eta-redex de tete ou rien du tout  *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 versions précédentes buggées                  *)

let rec eta_reduce_head c =
  match c with
    | DOP2(Lambda,c1,DLAM(_,c')) ->
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
                        if (not ((dependent (Rel 1) c'))) 
                        then lift (-1) c'
                        else c
                    | _     -> c)
           | _ -> c)
    | _ -> c

(* alpha-eta conversion : ignore print names and casts *)

let rec eta_eq_constr t1 t2 =
  let t1 = eta_reduce_head (strip_head_cast t1)
  and t2 = eta_reduce_head (strip_head_cast t2) in
  t1=t2 or match (t1,t2) with
    | (DOP2(Cast,c1,_),c2) -> eta_eq_constr c1 c2
    | (c1,DOP2(Cast,c2,_)) -> eta_eq_constr c1 c2
    | (Rel p1,Rel p2)                   -> p1=p2
    | (DOPN(oper1,cl1),DOPN(oper2,cl2)) ->
	oper1=oper2 & array_for_all2 eta_eq_constr cl1 cl2
    | (DOP0 oper1,DOP0 oper2)                 -> oper1=oper2
    | (DOP1(i,c1),DOP1(j,c2)) -> (i=j) & eta_eq_constr c1 c2
    | (DOP2(i,c1,c1'),DOP2(j,c2,c2')) ->
	(i=j) & eta_eq_constr c1 c2 & eta_eq_constr c1' c2'
    | (DLAM(_,c1),DLAM(_,c2)) -> eta_eq_constr c1 c2
    | (DLAMV(_,cl1),DLAMV(_,cl2)) -> array_for_all2 eta_eq_constr cl1 cl2
    | _ -> false


(* This renames bound variablew with fresh and distinct names *)
(* in such a way that the printer doe not generate new names  *)
(* and therefore that printed names are the intern names      *)
(* In this way, tactics such as Induction works well          *)

let rec rename_bound_var l = function
  | DOP2(Prod,c1,DLAM(Name(s),c2))  ->
      if dependent (Rel 1) c2 then
        let s' = next_ident_away s (global_vars c2@l) in
        DOP2(Prod,c1,DLAM(Name(s'),rename_bound_var (s'::l) c2))
      else 
	DOP2(Prod,c1,DLAM(Name(s),rename_bound_var l c2))
  | DOP2(Prod,c1,DLAM(Anonymous,c2)) ->
      DOP2(Prod,c1,DLAM(Anonymous,rename_bound_var l c2))
  | DOP2(Cast,c,t) -> DOP2(Cast,rename_bound_var l c,t)
  |  x -> x

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

(* Recognizing occurrences of a given subterm in a term for Pattern :
   (subst_term c t) substitutes (Rel 1) for all occurrences of term c 
   in a (closed) term t *)

let subst_term c t = 
  let rec substrec k c t =
    match prefix_application k c t with
      | Some x -> x
      | None ->
	  (if eq_constr t c then Rel(k) else match t with
	     | DOPN(Const sp,cl) -> t
	     | DOPN(MutInd (x_0,x_1),cl) -> t
	     | DOPN(MutConstruct (x_0,x_1),cl) -> t
	     | DOPN(oper,tl)     -> DOPN(oper,Array.map (substrec k c) tl)
	     | DOP1(i,t)         -> DOP1(i,substrec k c t)
	     | DOP2(oper,c1,c2)  -> DOP2(oper,substrec k c c1,substrec k c c2)
	     | DLAM(na,t)        -> DLAM(na,substrec (k+1) (lift 1 c) t)
	     | DLAMV(na,v) -> DLAMV(na,Array.map (substrec (k+1) (lift 1 c)) v)
	     | _ -> t)
  in 
  substrec 1 c t

(* same as subst_term, but modulo eta *)

let subst_term_eta_eq c t = 
  let rec substrec k c t =
    match prefix_application_eta k c t with
      | Some x -> x
      | None ->
	  (if eta_eq_constr t c then Rel(k) else match t with
	     | DOPN(Const sp,cl) -> t
	     | DOPN(oper,tl)     -> DOPN(oper,Array.map (substrec k c) tl)
	     | DOP1(i,t)         -> DOP1(i,substrec k c t)
	     | DOP2(oper,c1,c2)  -> DOP2(oper,substrec k c c1,substrec k c c2)
	     | DLAM(na,t)        -> DLAM(na,substrec (k+1) (lift 1 c) t)
	     | DLAMV(na,v)-> DLAMV(na,Array.map (substrec (k+1) (lift 1 c)) v)
	     | _ -> t)
  in 
  substrec 1 c t

(* bl : (int,constr) Listmap.t = (int * constr) list *)
(* c : constr *)
(* for each binding (i,c_i) in bl, substitutes the metavar i by c_i in c *)
(* Raises Not_found if c contains a meta that is not in the association list *)

let rec subst_meta bl c = 
  match c with
    | DOP0(Meta(i)) -> List.assoc i bl
    | DOP1(op,c') -> DOP1(op, subst_meta bl c')
    | DOP2(op,c'1, c'2) -> DOP2(op, subst_meta bl c'1, subst_meta bl c'2)
    | DOPN(op, c') -> DOPN(op, Array.map (subst_meta bl) c')
    | _ -> c

(* Substitute only a list of locations locs, the empty list is
   interpreted as substitute all, if 0 is in the list then no
   substitution is done the list may contain only negative occurrences
   that will not be substituted. *)

let subst_term_occ locs c t = 
  let rec substcheck except k occ c t =
    if except or List.exists (function u -> u>=occ) locs then
      substrec except k occ c t
    else 
      (occ,t)
  and substrec except k occ c t =
    if eq_constr t c then
      if except then 
	if List.mem (-occ) locs then (occ+1,t) else (occ+1,Rel(k))
      else 
	if List.mem occ locs then (occ+1,Rel(k)) else  (occ+1,t)
    else 
      match t with
	| DOPN(Const sp,tl) -> occ,t
	|  DOPN(MutConstruct _,tl) -> occ,t
	|  DOPN(MutInd _,tl) -> occ,t
	|  DOPN(i,cl) -> 
	     let (occ',cl') =   
               Array.fold_left 
		 (fun (nocc',lfd) f ->
		    let (nocc'',f') = substcheck except k nocc' c f in
                    (nocc'',f'::lfd)) 
		 (occ,[]) cl
             in 
	     (occ',DOPN(i,Array.of_list (List.rev cl')))
	|  DOP2(i,t1,t2) -> 
	     let (nocc1,t1')=substrec except k occ c t1 in
             let (nocc2,t2')=substcheck except k nocc1 c t2 in
             nocc2,DOP2(i,t1',t2')
	|  DOP1(i,t) -> 
	     let (nocc,t')= substrec except k occ c t in
	     nocc,DOP1(i,t')
	|  DLAM(n,t) -> 
	     let (occ',t') = substcheck except (k+1) occ (lift 1 c) t in
             (occ',DLAM(n,t'))
	|  DLAMV(n,cl) -> 
	     let (occ',cl') =   
               Array.fold_left 
		 (fun (nocc',lfd) f ->
		    let (nocc'',f') = 
		      substcheck except (k+1) nocc' (lift 1 c) f
                    in (nocc'',f'::lfd)) 
		 (occ,[]) cl
             in 
	     (occ',DLAMV(n,Array.of_list (List.rev cl') ))
	|  _ -> occ,t
  in 
  if locs = [] then 
    subst_term c t
  else if List.mem 0 locs then 
    t
  else 
    let except = List.for_all (fun n -> n<0) locs in
    let (nbocc,t') = substcheck except 1 1 c t in
    if List.exists (fun o -> o >= nbocc or o <= -nbocc) locs then
      failwith "subst_term_occ: too few occurences";
    t'

  
(***************************)
(* occurs check functions  *)                         
(***************************)

let rec occur_meta = function
  | DOP2(Prod,t,DLAM(_,c))   -> (occur_meta t) or (occur_meta c)
  | DOP2(Lambda,t,DLAM(_,c)) -> (occur_meta t) or (occur_meta c)
  | DOPN(_,cl)        -> (array_exists occur_meta cl)
  | DOP2(Cast,c,t)    -> occur_meta c or occur_meta t
  | DOP0(Meta(_))     -> true
  | _                 -> false

let rel_vect = (Generic.rel_vect : int -> int -> constr array)
		 
let occur_existential = 
  let rec occrec = function
    | DOPN(Evar _,_) -> true
    | DOPN(_,cl) -> array_exists occrec cl
    | DOPL(_,cl) -> List.exists occrec cl
    | DOP2(_,c1,c2) -> occrec c1 or occrec c2
    | DOP1(_,c) -> occrec c
    | DLAM(_,c) -> occrec c
    | DLAMV(_,cl) -> array_exists occrec cl
    | _ -> false
  in 
  occrec

(***************************)
(* hash-consing functions  *)                         
(***************************)

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
        | Abst sp -> Abst (hsp sp)
        | MutInd (sp,i) -> MutInd (hsp sp, i)
        | MutConstruct ((sp,i),j) -> MutConstruct ((hsp sp,i),j)
        | MutCase ci as t -> t (* TO DO: extract ind_sp *)
        | t -> t
      let equal o1 o2 =
        match (o1,o2) with
          | (XTRA s1, XTRA s2) -> s1==s2
          | (Sort s1, Sort s2) -> s1==s2
          | (Const sp1, Const sp2) -> sp1==sp2
          | (Abst sp1, Abst sp2) -> sp1==sp2
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
      let hash_sub (hc,hs) j = {body=hc j.body; typ=hs j.typ}
      let equal j1 j2 = j1.body==j2.body & j1.typ==j2.typ
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
	 
(*Gives the occurences number of t in u*)
let rec nb_occ_term t u=
  let one_step t=function
    | DOP1(_,c) -> nb_occ_term t c
    | DOP2(_,c0,c1) -> (nb_occ_term t c0)+(nb_occ_term t c1)
    | DOPN(_,a) -> Array.fold_left (fun a x -> a+(nb_occ_term t x)) 0 a
    | DOPL(_,l) -> List.fold_left (fun a x -> a+(nb_occ_term t x)) 0 l
    | DLAM(_,c) -> nb_occ_term t c
    | DLAMV(_,a) -> Array.fold_left (fun a x -> a+(nb_occ_term t x)) 0 a
    | _ -> 0
  in
  if t=u then
    1
  else
    one_step t u

(*Alpha-conversion*)
let bind_eq=function
  | (Anonymous,Anonymous) -> true
  | (Name _,Name _) -> true
  | _ -> false
	
	(*Tells if two constrs are equal modulo unification*)
let rec eq_mod_rel l_meta=function
  | (t,DOP0(Meta n)) ->
      if not(List.mem n (fst (List.split l_meta))) then
	Some ([(n,t)]@l_meta)
      else if (List.assoc n l_meta)=t then
	Some l_meta
      else
	None
  | DOP1(op0,c0), DOP1(op1,c1) ->
      if op0=op1 then
	eq_mod_rel l_meta (c0,c1)
      else
	None
  | DOP2(op0,t0,c0), DOP2(op1,t1,c1) ->
      if op0=op1 then
	match (eq_mod_rel l_meta (t0,t1)) with
          | None -> None
          | Some l -> eq_mod_rel l (c0,c1)	
      else
	None
  | DOPN(op0,t0), DOPN(op1,t1) ->
      if (op0=op1) & ((Array.length t0)=(Array.length t1)) then
	List.fold_left2
          (fun a c1 c2 ->
             match a with
	       | None -> None
               | Some l -> eq_mod_rel l (c1,c2)) (Some l_meta)
          (Array.to_list t0) (Array.to_list t1)
      else
	None
  | DLAM(n0,t0),DLAM(n1,t1) ->
      if (bind_eq (n0,n1)) then
	eq_mod_rel l_meta (t0,t1)
      else
	None
  | (t,u) ->
      if t=u then Some l_meta else None

(*Substitutes a list of meta l in t*)
let rec subst_with_lmeta l=function
  | DOP0(Meta n) -> List.assoc n l
  | DOP1(op,t) -> DOP1(op,subst_with_lmeta l t)
  | DOP2(op,t0,t1) -> DOP2(op,subst_with_lmeta l t0,subst_with_lmeta l t1)
  | DOPN(op,t) -> DOPN(op,Array.map (subst_with_lmeta l) t)
  | DOPL(op,ld) -> DOPL(op,List.map (subst_with_lmeta l) ld)
  | DLAM(n,t) -> DLAM(n,subst_with_lmeta l t)
  | DLAMV(n,t) -> DLAMV(n,Array.map (subst_with_lmeta l) t)
  | t -> t

(*Carries out the following translation: DOPN(AppL,[|t|]) -> t and
  DOPN(AppL,[|DOPN(AppL,t);...;t'|]) -> DOPN(AppL;[|t;...;t'|])*)
let rec appl_elim=function
  | DOPN(AppL,t) ->
      if (Array.length t)=1 then
	appl_elim t.(0)
      else
	(match t.(0) with
           | DOPN(AppL,t') -> 
	       appl_elim (DOPN(AppL,Array.append t' 
				 (Array.of_list
				    (List.tl (Array.to_list t)))))
           |_ -> DOPN(AppL,Array.map appl_elim t))
  | DOP1(op,t) -> DOP1(op,appl_elim t)
  | DOP2(op,t0,t1) -> DOP2(op,appl_elim t0,appl_elim t1)
  | DOPN(op,t) -> DOPN(op,Array.map appl_elim t)
  | DOPL(op,ld) -> DOPL(op,List.map appl_elim ld)
  | DLAM(n,t) -> DLAM(n,appl_elim t)
  | DLAMV(n,t) -> DLAMV(n,Array.map appl_elim t)
  | t -> t

(*Gives Some(first instance of ceq in cref,occurence number for this
  instance) or None if no instance of ceq can be found in cref*)
let sub_term_with_unif cref ceq=
  let rec find_match l_meta nb_occ op_ceq t_eq=function
    | DOPN(AppL,t) as u ->
	(match (t.(0)) with
           | DOPN(op,t_op) ->
               let t_args=Array.of_list (List.tl (Array.to_list t)) in
               if op=op_ceq then
                 match
                   (List.fold_left2 
                      (fun a c0 c1 ->
                         match a with
                           | None -> None
                           | Some l -> eq_mod_rel l (c0,c1)) (Some l_meta)
                      (Array.to_list t_args) (Array.to_list t_eq))
                 with
                   | None ->
                       List.fold_left
                         (fun (l_meta,nb_occ) x -> find_match l_meta nb_occ
                              op_ceq t_eq x) (l_meta,nb_occ) (Array.to_list
								t_args)
                   | Some l -> (l,nb_occ+1)
               else
                 List.fold_left 
		   (fun (l_meta,nb_occ) x -> find_match l_meta
			nb_occ op_ceq t_eq x) 
		   (l_meta,nb_occ) (Array.to_list t)
           | VAR _ ->
	       List.fold_left 
		 (fun (l_meta,nb_occ) x -> find_match l_meta
		      nb_occ op_ceq t_eq x) 
		 (l_meta,nb_occ) (Array.to_list t)
           |_ -> (l_meta,nb_occ))
    | DOP2(_,t,DLAM(_,c)) ->
	let (lt,nbt)=find_match l_meta nb_occ op_ceq t_eq t in
        find_match lt nbt op_ceq t_eq c
    | DOPN(_,t) -> 
	List.fold_left 
	  (fun (l_meta,nb_occ) x -> find_match l_meta nb_occ op_ceq t_eq x) 
	  (l_meta,nb_occ) (Array.to_list t)
    |_ -> (l_meta,nb_occ)
  in
  match (is_hd_const ceq) with
    | None ->
        if (occur_meta ceq) then
          None
        else
          let nb_occ=nb_occ_term ceq cref in
          if nb_occ=0 then
            None
          else
            Some (ceq,nb_occ)
    | Some (head,t_args) ->
        let (l,nb)=find_match [] 0 head t_args cref in
        if nb=0 then
          None
        else
          Some ((subst_with_lmeta l ceq),nb)
