
(* $Id$ *)

open Names
open Generic

(* The Type of Constructions Terms. *)

(* Coq abstract syntax with deBruijn variables; 'a is the type of sorts *)

type 'a oper = 
  (* DOP0 *)
  | Meta of int
  | Sort of 'a
  | Implicit
  (* DOP2 *)
  | Cast | Prod | Lambda
  (* DOPN *)
  | AppL | Const of section_path | Abst of section_path
  | MutInd of section_path * int
  | MutConstruct of (section_path * int) * int
  | MutCase of case_info
  | Fix of int array * int
  | CoFix of int

  | XTRA of string * Coqast.t list
      (* an extra slot, for putting in whatever sort of
         operator we need for whatever sort of application *)

and case_info = (section_path * int) option

type contents = Pos | Null

val str_of_contents : contents -> string
val contents_of_str : string -> contents

type sorts =
  | Prop of contents       (* Prop and Set *)
  | Type of Univ.universe  (* Type *)

val mk_Set  : sorts
val mk_Prop : sorts

type constr = sorts oper term

type 'a judge = { body : constr; typ : 'a }

type type_judgment = sorts judge
type term_judgment = type_judgment judge

type conv_pb = CONV | CONV_LEQ | CONV_X | CONV_X_LEQ


(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(* The following functions are intended to simplify and to uniform the 
   manipulation of terms. Some of these functions may be overlapped with
   previous ones. *)

(* Concrete type for making pattern-matching *)

type kindOfTerm =
  | IsRel          of int
  | IsMeta         of int
  | IsVar          of identifier
  | IsXtra         of string * Coqast.t list
  | IsSort         of sorts
  | IsImplicit
  | IsCast         of constr * constr
  | IsProd         of name * constr * constr
  | IsLambda       of name * constr * constr
  | IsAppL         of constr array
  | IsConst        of section_path  * constr array
  | IsAbst         of section_path  * constr array
  | IsMutInd       of section_path * int * constr array
  | IsMutConstruct of section_path * int * int * constr array
  | IsMutCase      of case_info * constr * constr * constr array
  | IsFix          of int array * int * constr array * name list *
                      constr array
  | IsCoFix        of int * constr array * name list * constr array

(* Discriminates which kind of term is it.  
   Note that there is no cases for [[DLAM] and [DLAMV].  These terms do not
   make sense alone, but they must be preceeded by the application of
   an operator.  
*)

val kind_of_term : constr -> kindOfTerm

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index *)
val mkRel          : int -> constr

(* Constructs an existential variable named "?" *)
val mkExistential  : constr

(* Constructs an existential variable named "?n" *)
val mkMeta         : int -> constr

(* Constructs a Variable *)
val mkVar          : identifier -> constr

(* Construct an XTRA term (XTRA is an extra slot for whatever you want) *)
val mkXtra         : string -> Coqast.t list -> constr

(* Construct a type *)
val mkSort         : sorts -> constr
val mkProp         : constr
val mkSet          : constr 
val mkType         : Univ.universe -> constr
val prop : sorts
val spec : sorts
val types : sorts 
val type_0 : sorts
val type_1 : sorts

(* Construct an implicit (see implicit arguments in the RefMan) *)
(* Used for extraction *)
val mkImplicit     : constr
val implicit_sort  : sorts

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
val mkCast         : constr -> constr -> constr

(* Constructs the product (x:t1)t2  -- x may be anonymous *)
val mkProd         : name -> constr -> constr -> constr

(* non-dependant product t1 -> t2 *)
val mkArrow : constr -> constr -> constr

(* named product *)
val mkNamedProd : identifier -> constr -> constr -> constr

(* Constructs the abstraction [x:t1]t2 *)
val mkLambda       : name -> constr -> constr -> constr
val mkNamedLambda : identifier -> constr -> constr -> constr

(* If a = [| t1; ...; tn |], constructs the application (t1 ... tn) *)
val mkAppL         : constr array -> constr
val mkAppList      : constr list  -> constr

(* Constructs a constant *) 
(* The array of terms correspond to the variables introduced in the section *)
val mkConst        : section_path -> constr array -> constr

(* Constructs an abstract object *)
val mkAbst         : section_path -> constr array -> constr

(* Constructs the ith (co)inductive type of the block named sp *)
(* The array of terms correspond to the variables introduced in the section *)
val mkMutInd       : section_path -> int -> constr array -> constr

(* Constructs the jth constructor of the ith (co)inductive type of the 
   block named sp. The array of terms correspond to the variables
   introduced in the section *)
val mkMutConstruct : section_path -> int -> int -> constr array -> constr

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
val mkMutCase      : case_info -> constr -> constr -> constr list -> constr
val mkMutCaseA     : case_info -> constr -> constr -> constr array -> constr

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
val mkFix          : int array -> int -> type_judgment array -> name list 
                      -> constr array -> constr

(* Similarly, but we assume the body already constructed *)
val mkFixDlam      : int array -> int -> type_judgment array
                     -> constr array -> constr 

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
val mkCoFix        : int -> type_judgment array -> name list 
                     -> constr array -> constr

(* Similarly, but we assume the body already constructed *)
val mkCoFixDlam    : int -> type_judgment array -> constr array -> constr

(********************)
(* Term destructors *)
(********************)

(* Destructor operations : partial functions 
   Raise invalid_arg "dest*" if the const has not the expected form *)

(* Destructs a DeBrujin index *)
val destRel          : constr -> int

(* Destructs an existential variable *)
val destMeta         : constr -> int
val isMETA : constr -> bool

(* Destructs a variable *)
val destVar          : constr -> identifier

(* Destructs an XTRA *)
val destXtra        : constr -> string * Coqast.t list

(* Destructs a sort *)
val destSort         : constr -> sorts
val contents_of_kind : constr -> contents
val is_Prop          : constr -> bool (* true for Prop *) 
val is_Set           : constr -> bool  (* true for Set *)
val isprop           : constr -> bool (* true for DOP0 (Sort (Prop _)) *)
val is_Type          : constr -> bool (* true for DOP0 (Sort (Type _)) *)
val iskind           : constr -> bool (* true for Prop, Set and Type(_) *)

val isType           : sorts -> bool (* true for Type(_) *)
val is_small         : sorts -> bool (* true for Prop and Set *)

(* Destructs a casted term *)
val destCast         : constr -> constr * constr
val cast_type : constr -> constr (* 2nd proj *)
val cast_term : constr -> constr (* 1st proj *)
val isCast : constr -> bool
(* removes recursively the casts around a term *)
(* strip_outer_cast (Cast (Cast ... (Cast c, t) ... )) is c *)
val strip_outer_cast : constr -> constr

(* Destructs the product (x:t1)t2 *)
val destProd          : constr -> name * constr * constr
val hd_of_prod        : constr -> constr
val hd_is_constructor : constr -> bool

(* Destructs the abstraction [x:t1]t2 *)
val destLambda       : constr -> name * constr * constr

(* Destructs an application *)
val destAppL   : constr -> constr array
val isAppL     : constr -> bool
val hd_app     : constr -> constr 
val args_app   : constr -> constr array

(* Destructs a constant *)
val destConst     : constr -> section_path * constr array
val path_of_const : constr -> section_path
val args_of_const : constr -> constr array

(* Destrucy an abstract term *)
val destAbst         : constr -> section_path * constr array
val path_of_abst : constr -> section_path
val args_of_abst : constr -> constr array

(* Destructs a (co)inductive type *)
val destMutInd    : constr -> section_path * int * constr array
val op_of_mind    : constr -> section_path * int
val args_of_mind  : constr -> constr array
val ci_of_mind    : constr -> case_info

(* Destructs a constructor *)
val destMutConstruct : constr -> section_path * int * int * constr array
val op_of_mconstr    : constr -> (section_path * int) * int
val args_of_mconstr  : constr -> constr array

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
val destCase         : constr -> case_info * constr * constr * constr array

(* Destructs the ith function of the block  
    Fixpoint f1 [ctx1] = b1
    with     f2 [ctx2] = b2
    ...
    with     fn [ctxn] = bn.

   where the lenght of the jth context is ij.
*)
val destGralFix      : constr array -> constr array * Names.name list 
                                        * constr array
val destFix          : constr -> int array * int * type_judgment array
                                  * Names.name list * constr array
val destCoFix        : constr -> int * type_judgment array * Names.name list 
                                  * constr array

(* Provisoire, le temps de maitriser les cast *)
val destUntypedFix          : constr -> int array * int * constr array
                                  * Names.name list * constr array
val destUntypedCoFix        : constr -> int * constr array * Names.name list 
                                  * constr array

(***********************************)
(* Other term constructors         *)
(***********************************)

val abs_implicit : constr -> constr
val lambda_implicit : constr -> constr
val lambda_implicit_lift : int -> constr -> constr

val applist : constr * constr list -> constr
val applistc : constr -> constr list -> constr
val appvect : constr * constr array -> constr
val appvectc : constr -> constr array -> constr
(* prodn n ([x1:T1]..[xn:Tn]Gamma) b = (x1:T1)..(xn:Tn)b *)
val prodn   : int -> (name * constr) list -> constr -> constr
(* lamn n ([x1:T1]..[xn:T]Gamma) b = [x1:T1]..[xn:Tn]b *)
val lamn : int -> (name * constr) list -> constr -> constr

(* prod_it b [x1:T1;..xn:Tn] = (x1:T1)..(xn:Tn)b *)
val prod_it : constr -> (name * constr) list -> constr
(* lam_it b [x1:T1;..xn:Tn] = [x1:T1]..[xn:Tn]b *)
val lam_it : constr -> (name * constr) list -> constr


(* to_lambda n (x1:T1)...(xn:Tn)(xn+1:Tn+1)...(xn+j:Tn+j)T =
   [x1:T1]...[xn:Tn](xn+1:Tn+1)...(xn+j:Tn+j)T *)
val to_lambda : int -> constr -> constr
val to_prod : int -> constr -> constr

(*********************************)
(* Other term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
val decompose_prod  : constr -> (name*constr) list * constr

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
val decompose_lam   : constr -> (name*constr) list * constr

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
val decompose_prod_n  : int -> constr -> (name*constr) list * constr

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
val decompose_lam_n   : int -> constr -> (name*constr) list * constr

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
val nb_lam : constr -> int

(* similar to nb_lam, but gives the number of products instead *)
val nb_prod : constr -> int

(********************************************************************)
(*   various utility functions for implementing terms with bindings *)
(********************************************************************)

val extract_lifted : int * constr -> constr
val insert_lifted : constr -> int * constr

(* l is a list of pairs (n:nat,x:constr), env is a stack of (na:name,T:constr)
   push_and_lift adds a component to env and lifts l one step *)
val push_and_lift :
  name * constr -> (name * constr) list -> (int * constr) list 
    -> (name * constr) list * (int * constr) list

(* if T is not (x1:A1)(x2:A2)....(xn:An)T' then (push_and_liftl n env T l)
   raises an error else it gives ([x1,A1 ; x2,A2 ; ... ; xn,An]@env,T',l')
   where l' is l lifted n steps *)
val push_and_liftl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* if T is not [x1:A1][x2:A2]....[xn:An]T' then (push_lam_and_liftl n env T l)
   raises an error else it gives ([x1,A1 ; x2,A2 ; ... ; xn,An]@env,T',l')
   where l' is l lifted n steps *)
val push_lam_and_liftl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* l is a list of pairs (n:nat,x:constr), tlenv is a stack of
(na:name,T:constr), B : constr, na : name
(prod_and_pop ((na,T)::tlenv) B l) gives (tlenv, (na:T)B, l')
where l' is l lifted down one step *)
val prod_and_pop :
  (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* recusively applies prod_and_pop :
if env = [na1:T1 ; na2:T2 ; ... ; nan:Tn]@tlenv
then
(prod_and_popl n env T l) gives (tlenv,(nan:Tn)...(na1:Ta1)T,l') where
l' is l lifted down n steps *)
val prod_and_popl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* similar to prod_and_pop, but gives [na:T]B intead of (na:T)B *)
val lam_and_pop :
  (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* similar to prod_and_popl but gives [nan:Tan]...[na1:Ta1]B instead of
 * (nan:Tan)...(na1:Ta1)B *)
val lam_and_popl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* similar to lamn_and_pop but generates new names whenever the name is 
 * Anonymous *)
val lam_and_pop_named :
  (name * constr) list -> constr ->(int * constr) list ->identifier list 
    -> (name * constr) list * constr * (int * constr) list * identifier list

(* similar to prod_and_popl but gives [nan:Tan]...[na1:Ta1]B instead of
 * but it generates names whenever nai=Anonymous *)
val lam_and_popl_named :
 int ->  (name * constr) list -> constr ->  (int * constr) list 
  -> (name * constr) list * constr * (int * constr) list 
(* [lambda_ize n T endpt]
 * will pop off the first n products in T, then stick in endpt,
 * properly lifted, and then push back the products, but as lambda-
 * abstractions
 *)
val lambda_ize :int ->'a oper term -> 'a oper term -> 'a oper term

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

(* if c is not an AppL, it is transformed into mkAppL [| c |] *)
val ensure_appl : constr -> constr

(* unflattens application lists *)
val telescope_appl : constr -> constr
(* flattens application lists *)
val collapse_appl : constr -> constr
val decomp_app : constr -> constr * constr list


(********************************************)
(* Misc functions on terms, judgments, etc  *)
(********************************************)

(* Level comparison for information extraction : Prop <= Type *)
val same_kind : constr -> constr -> bool
val le_kind : constr -> constr -> bool
val le_kind_implicit : constr -> constr -> bool

val pb_is_univ_adjust : conv_pb -> bool
val pb_is_equal : conv_pb -> bool
val pb_equal : conv_pb -> conv_pb
val sort_hdchar : sorts -> string


(***************************)
(* occurs check functions  *)                         
(***************************)
val occur_meta : constr -> bool
val rel_vect : int -> int -> constr array

(* (occur_const (s:section_path) c) -> true if constant s occurs in c,
 * false otherwise *)
val occur_const : section_path -> constr -> bool

(* strips head casts and flattens head applications *)
val strip_head_cast : constr -> constr
val whd_castapp_stack : constr -> constr list -> constr * constr list
val whd_castapp : constr -> constr
val rename_bound_var : identifier list -> constr -> constr
val eta_reduce_head : constr -> constr
val eq_constr : constr -> constr -> bool
val eta_eq_constr : constr -> constr -> bool
val rename_rels : int -> constr -> (identifier * constr) list -> constr
val clean_rhs : constr -> (identifier * constr) list -> constr
val subst_term : constr -> constr -> constr
val subst_term_eta_eq : constr -> constr -> constr
val replace_consts :
  (section_path * (identifier list * constr) option) list -> constr -> constr

(* bl : (int,constr) Listmap.t = (int * constr) list *)
(* c : constr *)
(* for each binding (i,c_i) in bl, substitutes the metavar i by c_i in c *)
(* Raises Not_found if c contains a meta that is not in the association list *)

val subst_meta : (int * constr) list -> constr -> constr

(* Transforms a constr into a matchable constr *)
val matchable : constr -> constr
val unmatchable: constr -> constr

(* New hash-cons functions *)

val hcons_constr:
  (section_path -> section_path) *
  (section_path -> section_path) *
  (name -> name) *
  (identifier -> identifier) *
  (string -> string) 
  ->
    (constr -> constr) *
    (constr -> constr) *
    (type_judgment -> type_judgment)

val hcons1_constr : constr -> constr
