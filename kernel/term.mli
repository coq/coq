
(* $Id$ *)

(*i*)
open Util
open Pp
open Names
(* open Generic *)
(*i*)

(*s The sorts of CCI. *)

type contents = Pos | Null

type sorts =
  | Prop of contents       (* Prop and Set *)
  | Type of Univ.universe  (* Type *)

val str_of_contents : contents -> string
val contents_of_str : string -> contents

val mk_Set  : sorts
val mk_Prop : sorts

val print_sort : sorts -> std_ppcmds

(*s The operators of the Calculus of Inductive Constructions. 
  ['a] is the type of sorts. ([XTRA] is an extra slot, for putting in 
  whatever sort of operator we need for whatever sort of application.) *)

type existential_key = int

type pattern_source = DefaultPat of int | RegularPat
type case_style = PrintLet | PrintIf | PrintCases
type case_printing =
    inductive_path * identifier array * int
    * case_style option * pattern_source array
(* the integer is the number of real args, needed for reduction *)
type case_info = int array * case_printing

type 'a oper = 
  | Meta of int
  | Sort of 'a
  | Cast | Prod | Lambda
  | AppL | Const of section_path
  | Evar of existential_key
  | MutInd of inductive_path
  | MutConstruct of constructor_path
  | MutCase of case_info
  | Fix of int array * int
  | CoFix of int
  | XTRA of string

(*s The type [constr] of the terms of CCI
  is obtained by instanciating a generic notion of terms
  on the above operators, themselves instanciated
  on the above sorts. *)

(* [VAR] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)

type constr =
  | DOP0 of sorts oper
  | DOP1 of sorts oper * constr
  | DOP2 of sorts oper * constr * constr
  | DOPN of sorts oper * constr array
  | DLAM of name * constr
  | DLAMV of name * constr array
  | CLam of name * typed_type * constr
  | CPrd of name * typed_type * constr
  | CLet of name * constr * typed_type * constr
  | VAR of identifier
  | Rel of int

and typed_type

type flat_arity = (name * constr) list * sorts

(*s Functions about [typed_type] *)

val make_typed : constr -> sorts -> typed_type
val make_typed_lazy : constr -> (constr -> sorts) -> typed_type

val typed_app : (constr -> constr) -> typed_type -> typed_type
val typed_combine : (constr -> constr -> constr) -> (sorts -> sorts -> sorts)
      -> (typed_type -> typed_type -> typed_type)

val body_of_type : typed_type -> constr
val level_of_type : typed_type -> sorts

val incast_type : typed_type -> constr

val outcast_type : constr -> typed_type

type var_declaration = identifier * constr option * typed_type
type rel_declaration = name * constr option * typed_type

(**********************************************************************)
type binder_kind = BProd | BLambda | BLetIn

type fix_kind = RFix of (int array * int) | RCoFix of int

type 'ctxt reference =
  | RConst of section_path * 'ctxt
  | RInd of inductive_path * 'ctxt
  | RConstruct of constructor_path * 'ctxt
  | RVar of identifier
  | REVar of int * 'ctxt

(*s Functions for dealing with constr terms.
  The following functions are intended to simplify and to uniform the 
  manipulation of terms. Some of these functions may be overlapped with
  previous ones. *)

(* Concrete type for making pattern-matching. *)

(* [constr array] is an instance matching definitional [var_context] in
   the same order (i.e. last argument first) *)
type existential = int * constr array
type constant = section_path * constr array
type constructor = constructor_path * constr array
type inductive = inductive_path * constr array
type fixpoint = (int array * int) * (constr array * name list * constr array)
type cofixpoint = int * (constr array * name list * constr array)


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
  Note that there is no cases for [DLAM] and [DLAMV].  These terms do not
  make sense alone, but they must be preceeded by the application of
  an operator. *)

val kind_of_term : constr -> kindOfTerm


(*s Term constructors. *)

(* Constructs a DeBrujin index *)
val mkRel : int -> constr

(* Constructs an existential variable named "?n" *)
val mkMeta : int -> constr

(* Constructs a Variable *)
val mkVar : identifier -> constr

(* Construct an  [XTRA] term. *)
val mkXtra : string -> constr

(* Construct a type *)
val mkSort : sorts -> constr
val mkProp : constr
val mkSet : constr 
val mkType : Univ.universe -> constr
val prop : sorts
val spec : sorts
val types : sorts 
val type_0 : sorts
val type_1 : sorts

(* Construct an implicit (see implicit arguments in the RefMan).
   Used for extraction *)
val mkImplicit : constr
val implicit_sort : sorts

(* Constructs the term $t_1::t2$, i.e. the term $t_1$ casted with the 
   type $t_2$ (that means t2 is declared as the type of t1). *)
val mkCast : constr * constr -> constr

(* Constructs the product $(x:t_1)t_2$ *)
val mkProd : name * constr * constr -> constr
val mkNamedProd : identifier -> constr -> constr -> constr
val mkProd_string : string -> constr -> constr -> constr

(* Constructs the product $(x:t_1)t_2$ *)
val mkLetIn : name * constr * constr * constr -> constr
val mkNamedLetIn : identifier -> constr -> constr -> constr -> constr

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
val mkProd_or_LetIn : rel_declaration -> constr -> constr
val mkNamedProd_or_LetIn : var_declaration -> constr -> constr

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
val mkLambda_or_LetIn : rel_declaration -> constr -> constr
val mkNamedLambda_or_LetIn : var_declaration -> constr -> constr

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
val mkProd_wo_LetIn : rel_declaration -> constr -> constr
val mkNamedProd_wo_LetIn : var_declaration -> constr -> constr

(* non-dependant product $t_1 \rightarrow t_2$ *)
val mkArrow : constr -> constr -> constr

(* Constructs the abstraction $[x:t_1]t_2$ *)
val mkLambda : name * constr * constr -> constr
val mkNamedLambda : identifier -> constr -> constr -> constr

(* [mkLambda_string s t c] constructs $[s:t]c$ *)
val mkLambda_string : string -> constr -> constr -> constr

(* If $a = [| t_1; \dots; t_n |]$, constructs the application 
   $(t_1~\dots~t_n)$. *)
val mkAppL : constr array -> constr
val mkAppList : constr -> constr list  -> constr

(* Constructs a constant *) 
(* The array of terms correspond to the variables introduced in the section *)
val mkConst : constant -> constr

(* Constructs an existential variable *)
val mkEvar : existential -> constr

(* Constructs the ith (co)inductive type of the block named sp *)
(* The array of terms correspond to the variables introduced in the section *)
val mkMutInd : inductive -> constr

(* Constructs the jth constructor of the ith (co)inductive type of the 
   block named sp. The array of terms correspond to the variables
   introduced in the section *)
val mkMutConstruct : constructor -> constr

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
val mkMutCaseL : case_info * constr * constr * constr list -> constr
val mkMutCase : case_info * constr * constr * constr array -> constr

(* If [recindxs = [|i1,...in|]]
      [typarray = [|t1,...tn|]]
      [funnames = [f1,.....fn]]
      [bodies   = [b1,.....bn]]
   then [ mkFix ((recindxs,i),typarray, funnames, bodies) ]
   constructs the $i$th function of the block (counting from 0)

    [Fixpoint f1 [ctx1] = b1
     with     f2 [ctx2] = b2
     ...
     with     fn [ctxn] = bn.]

   \noindent where the lenght of the $j$th context is $ij$.
*)
val mkFix : fixpoint -> constr

(* Similarly, but we assume the body already constructed *)
val mkFixDlam : int array -> int -> constr array -> constr array -> constr 

(* If [typarray = [|t1,...tn|]]
      [funnames = [f1,.....fn]]
      [bodies   = [b1,.....bn]] \par\noindent
   then [mkCoFix (i, (typsarray, funnames, bodies))]
   constructs the ith function of the block  
   
    [CoFixpoint f1 = b1
     with       f2 = b2
     ...
     with       fn = bn.]
 *)
val mkCoFix : cofixpoint -> constr

(* Similarly, but we assume the body already constructed *)
val mkCoFixDlam : int -> constr array -> constr array -> constr


(*s Term destructors. 
   Destructor operations are partial functions and
   raise [invalid_arg "dest*"] if the term has not the expected form. *)

(* Destructs a term of the form $(x_1:T_1)..(x_n:T_n)s$ into the pair *)
val destArity : constr -> flat_arity
val isArity : constr -> bool

(* Destructs a DeBrujin index *)
val destRel : constr -> int

(* Destructs an existential variable *)
val destMeta : constr -> int
val isMeta : constr -> bool

(* Destructs a variable *)
val destVar : constr -> identifier

(* Destructs an XTRA *)
val destXtra : constr -> string

(* Destructs a sort. [is_Prop] recognizes the sort \textsf{Prop}, whether 
   [isprop] recognizes both \textsf{Prop} and \textsf{Set}. *)
val destSort : constr -> sorts
val contents_of_kind : constr -> contents
val is_Prop : constr -> bool
val is_Set : constr -> bool
val isprop : constr -> bool
val is_Type : constr -> bool
val iskind : constr -> bool

val is_existential_oper : sorts oper -> bool

val isType : sorts -> bool
val is_small : sorts -> bool (* true for \textsf{Prop} and \textsf{Set} *)

(* Destructs a casted term *)
val destCast : constr -> constr * constr
val isCast : constr -> bool

(* Removes recursively the casts around a term i.e.
   [strip_outer_cast] (Cast (Cast ... (Cast c, t) ... ))] is [c]. *)
val strip_outer_cast : constr -> constr

(* Special function, which keep the key casts under Fix and MutCase. *)
val strip_all_casts : constr -> constr

(* Tests if a de Bruijn index *)
val isRel  : constr -> bool

(* Tests if a variable *)
val isVar  : constr -> bool

(* Destructs the product $(x:t_1)t_2$ *)
val destProd : constr -> name * constr * constr
val hd_of_prod : constr -> constr
val hd_is_constructor : constr -> bool

(* Destructs the abstraction $[x:t_1]t_2$ *)
val destLambda : constr -> name * constr * constr

(* Destructs the let $[x:=b:t_1]t_2$ *)
val destLetIn : constr -> name * constr * constr * constr

(* Destructs an application *)
val destAppL : constr -> constr array
val isAppL : constr -> bool
val hd_app : constr -> constr 
val args_app : constr -> constr array
val destApplication : constr -> constr * constr array

(* Destructs a constant *)
val destConst : constr -> section_path * constr array
val isConst : constr -> bool
val path_of_const : constr -> section_path
val args_of_const : constr -> constr array

(* Destructs an existential variable *)
val destEvar : constr -> int * constr array
val num_of_evar : constr -> int

(* Destructs a (co)inductive type *)
val destMutInd : constr -> inductive
val op_of_mind : constr -> inductive_path
val args_of_mind : constr -> constr array

(* Destructs a constructor *)
val destMutConstruct : constr -> constructor
val isMutConstruct : constr -> bool
val op_of_mconstr : constr -> constructor_path
val args_of_mconstr : constr -> constr array

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
val destCase : constr -> case_info * constr * constr * constr array

(* Destructs the $i$th function of the block  
   $\mathit{Fixpoint} ~ f_1 ~ [ctx_1] = b_1
    \mathit{with}     ~ f_2 ~ [ctx_2] = b_2
    \dots
    \mathit{with}     ~ f_n ~ [ctx_n] = b_n$,
   where the lenght of the $j$th context is $ij$.
*)
val destGralFix : 
  constr array -> constr array * Names.name list * constr array
val destFix : constr -> fixpoint

val destCoFix : constr -> cofixpoint

(*s Other term constructors. *)

val abs_implicit : constr -> constr
val lambda_implicit : constr -> constr
val lambda_implicit_lift : int -> constr -> constr

(* [applist (f,args)] and co build [mkAppL (f,args)] if [args] non
   empty and build [f] otherwise *)

val applist : constr * constr list -> constr
val applistc : constr -> constr list -> constr
val appvect : constr * constr array -> constr
val appvectc : constr -> constr array -> constr

(* [prodn n l b] = $(x_1:T_1)..(x_n:T_n)b$ 
   where $l = [(x_n,T_n);\dots;(x_1,T_1);Gamma]$ *)
val prodn : int -> (name * constr) list -> constr -> constr

(* [lamn n l b] = $[x_1:T_1]..[x_n:T_n]b$
   where $l = [(x_n,T_n);\dots;(x_1,T_1);Gamma]$ *)
val lamn : int -> (name * constr) list -> constr -> constr

(* [prod_it b l] = $(x_1:T_1)..(x_n:T_n)b$ 
   where $l = [(x_n,T_n);\dots;(x_1,T_1)]$ *)
val prod_it : constr -> (name * constr) list -> constr

(* [lam_it b l] = $[x_1:T_1]..[x_n:T_n]b$ 
   where $l = [(x_n,T_n);\dots;(x_1,T_1)]$ *)
val lam_it : constr -> (name * constr) list -> constr

(* [to_lambda n l] 
   = $[x_1:T_1]...[x_n:T_n](x_{n+1}:T_{n+1})...(x_{n+j}:T_{n+j})T$
   where $l = (x_1:T_1)...(x_n:T_n)(x_{n+1}:T_{n+1})...(x_{n+j}:T_{n+j})T$ *)
val to_lambda : int -> constr -> constr
val to_prod : int -> constr -> constr

(* pseudo-reduction rule *)
(* [prod_applist] $(x1:B1;...;xn:Bn)B a1...an \rightarrow B[a1...an]$ *)
val prod_applist : constr -> constr list -> constr

(*s Other term destructors. *)

(* Transforms a product term $(x_1:T_1)..(x_n:T_n)T$ into the pair
   $([(x_n,T_n);...;(x_1,T_1)],T)$, where $T$ is not a product.
   It includes also local definitions *)
val decompose_prod : constr -> (name*constr) list * constr

(* Transforms a lambda term $[x_1:T_1]..[x_n:T_n]T$ into the pair
   $([(x_n,T_n);...;(x_1,T_1)],T)$, where $T$ is not a lambda. *)
val decompose_lam : constr -> (name*constr) list * constr

(* Given a positive integer n, transforms a product term 
   $(x_1:T_1)..(x_n:T_n)T$
   into the pair $([(xn,Tn);...;(x1,T1)],T)$. *)
val decompose_prod_n : int -> constr -> (name * constr) list * constr

(* Given a positive integer $n$, transforms a lambda term 
   $[x_1:T_1]..[x_n:T_n]T$ into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$ *)
val decompose_lam_n : int -> constr -> (name * constr) list * constr

(* [nb_lam] $[x_1:T_1]...[x_n:T_n]c$ where $c$ is not an abstraction
   gives $n$ (casts are ignored) *)
val nb_lam : constr -> int

(* similar to [nb_lam], but gives the number of products instead *)
val nb_prod : constr -> int

(*i*)(* Trop compliqué 
(*s Various utility functions for implementing terms with bindings. *)

val extract_lifted : int * constr -> constr
val insert_lifted : constr -> int * constr

(* If [l] is a list of pairs $(n:nat,x:constr)$, [env] is a stack of 
   $(na:name,T:constr)$, then
   [push_and_lift (id,c) env l] adds a component [(id,c)] to [env] 
   and lifts [l] one step *)
val push_and_lift :
  name * constr -> (name * constr) list -> (int * constr) list 
    -> (name * constr) list * (int * constr) list

(* if [T] is not $(x_1:A_1)(x_2:A_2)....(x_n:A_n)T'$ 
   then [(push_and_liftl n env T l)]
   raises an error else it gives $([x1,A1 ; x2,A2 ; ... ; xn,An]@env,T',l')$
   where $l'$ is [l] lifted [n] steps *)
val push_and_liftl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* if $T$ is not $[x_1:A_1][x_2:A_2]....[x_n:A_n]T'$ then 
   [(push_lam_and_liftl n env T l)]
   raises an error else it gives $([x_1,A_1; x_2,A_2; ...; x_n,A_n]@env,T',l')$
   where $l'$ is [l] lifted [n] steps *)
val push_lam_and_liftl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* If [l] is a list of pairs $(n:nat,x:constr)$, [tlenv] is a stack of
   $(na:name,T:constr)$, [B] is a constr, [na] a name, then
   [(prod_and_pop ((na,T)::tlenv) B l)] gives $(tlenv, (na:T)B, l')$
   where $l'$ is [l] lifted down one step *)
val prod_and_pop :
  (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* recusively applies [prod_and_pop] :
   if [env] = $[na_1:T_1 ; na_2:T_2 ; ... ; na_n:T_n]@tlenv$ then
   [(prod_and_popl n env T l)] gives $(tlenv,(na_n:T_n)...(na_1:T_1)T,l')$
   where $l'$ is [l] lifted down [n] steps *)
val prod_and_popl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* similar to [prod_and_pop], but gives $[na:T]B$ intead of $(na:T)B$ *)
val lam_and_pop :
  (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* similar to [prod_and_popl] but gives $[na_n:T_n]...[na_1:T_1]B$ instead of
   $(na_n:T_n)...(na_1:T_1)B$ *)
val lam_and_popl :
  int -> (name * constr) list -> constr -> (int * constr) list
    -> (name * constr) list * constr * (int * constr) list

(* similar to [lamn_and_pop] but generates new names whenever the name is 
   [Anonymous] *)
val lam_and_pop_named :
  (name * constr) list -> constr ->(int * constr) list ->identifier list 
    -> (name * constr) list * constr * (int * constr) list * identifier list

(* similar to [prod_and_popl] but gives $[na_n:T_n]...[na_1:T_1]B$ instead of
   but it generates names whenever $na_i$ = [Anonymous] *)
val lam_and_popl_named :
  int ->  (name * constr) list -> constr ->  (int * constr) list 
    -> (name * constr) list * constr * (int * constr) list 

(* [lambda_ize n T endpt]
   will pop off the first [n] products in [T], then stick in [endpt],
   properly lifted, and then push back the products, but as lambda-
   abstractions *)
val lambda_ize : int ->'a oper term -> 'a oper term -> 'a oper term
*)(*i*)

(*s Flattening and unflattening of embedded applications and casts. *)

(* if [c] is not an [AppL], it is transformed into [mkAppL [| c |]] *)
val ensure_appl : constr -> constr

(* unflattens application lists *)
val telescope_appl : constr -> constr
(* flattens application lists *)
val collapse_appl : constr -> constr
val decomp_app : constr -> constr * constr list


(*s Misc functions on terms, sorts and conversion problems. *)

(* Level comparison for information extraction : Prop <= Type *)
val same_kind : constr -> constr -> bool
val le_kind : constr -> constr -> bool
val le_kind_implicit : constr -> constr -> bool

val sort_hdchar : sorts -> string

(* Generic functions *)
val free_rels : constr -> Intset.t

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)
val closed0 : constr -> bool

(* [noccurn n M] returns true iff [Rel n] does NOT occur in term [M]  *)
val noccurn : int -> constr -> bool

(* [noccur_between n m M] returns true iff [Rel p] does NOT occur in term [M]
  for n <= p < n+m *)
val noccur_between : int -> int -> constr -> bool

(* Checking function for terms containing existential- or
   meta-variables.  The function [noccur_with_meta] considers only
   meta-variable applied to some terms (intented to be its local
   context) (for existential variables, it is necessarily the case) *)
val noccur_with_meta : int -> int -> constr -> bool

(* [liftn n k c] lifts by [n] indexes above [k] in [c] *)
val liftn : int -> int -> constr -> constr

(* [lift n c] lifts by [n] the positive indexes in [c] *)
val lift : int -> constr -> constr

(* [pop c] lifts by -1 the positive indexes in [c] *)
val pop : constr -> constr

(* [lift_context n ctxt] lifts terms in [ctxt] by [n] preserving
   (i.e. not lifting) the internal references between terms of [ctxt];
   more recent terms come first in [ctxt] *)
val lift_context : int -> (name * constr) list -> (name * constr) list

(* [substnl [a1;...;an] k c] substitutes in parallele [a1],...,[an]
    for respectively [Rel(k+1)],...,[Rel(k+n)] in [c]; it relocates
    accordingly indexes in [a1],...,[an] *)
val substnl : constr list -> int -> constr -> constr
val substl : constr list -> constr -> constr
val subst1 : constr -> constr -> constr

(* [global_vars c] returns the list of [id]'s occurring as [VAR id] in [c] *)
val global_vars : constr -> identifier list

val global_vars_set : constr -> Idset.t
val replace_vars : (identifier * constr) list -> constr -> constr
val subst_var : identifier -> constr -> constr

(* [subst_vars [id1;...;idn] t] substitute [VAR idj] by [Rel j] in [t]
   if two names are identical, the one of least indice is keeped *)
val subst_vars : identifier list -> constr -> constr

(* [rel_list n m] and [rel_vect n m] compute [[Rel (n+m);...;Rel(n+1)]] *)
val rel_vect : int -> int -> constr array
val rel_list : int -> int -> constr list

(*i************************************************************************i*)
(*i Pour Closure 
(* Explicit substitutions of type ['a]. [ESID] = identity. 
  [CONS(t,S)] = $S.t$ i.e. parallel substitution. [SHIFT(n,S)] = 
  $(\uparrow n~o~S)$ i.e. terms in S are relocated with n vars. 
  [LIFT(n,S)] = $(\%n~S)$ stands for $((\uparrow n~o~S).n...1)$. *)
type 'a subs =
  | ESID
  | CONS of 'a * 'a subs
  | SHIFT of int * 'a subs
  | LIFT of int * 'a subs
val subs_cons  : 'a * 'a subs -> 'a subs
val subs_liftn  : int -> 'a subs -> 'a subs
val subs_lift  : 'a subs -> 'a subs
val subs_shft  : int * 'a subs -> 'a subs
val expand_rel : int -> 'a subs -> (int * 'a, int) union
i*)
(*s Lifts. [ELSHFT(l,n)] == lift of [n], then apply [lift l].
  [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders. *)
type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int
  | ELLFT of int * lift_spec
val el_shft : int -> lift_spec -> lift_spec
val el_lift : lift_spec -> lift_spec
val reloc_rel: int -> lift_spec -> int
(*i*)

(*s Occur check functions. *)                         

val occur_meta : constr -> bool

(*i Returns the maximum of metas. Returns -1 if there is no meta i*)
(*i val max_occur_meta : constr -> int i*)

val occur_existential : constr -> bool

(* [(occur_const (s:section_path) c)] returns [true] if constant [s] occurs 
   in c, [false] otherwise *)
val occur_const : section_path -> constr -> bool

(* [(occur_evar ev c)] returns [true] if existential variable [ev] occurs 
   in c, [false] otherwise *)
val occur_evar : existential_key -> constr -> bool

(* [(occur_var id c)] returns [true] if variable [id] occurs free
   in c, [false] otherwise *)
val occur_var : identifier -> constr -> bool

(* [dependent M N] is true iff M is eq\_constr with a subterm of N 
   M is appropriately lifted through abstractions of N *)
val dependent : constr -> constr -> bool

(* strips head casts and flattens head applications *)
val strip_head_cast : constr -> constr
val whd_castapp_stack : constr -> constr list -> constr * constr list
val whd_castapp : constr -> constr
val rename_bound_var : identifier list -> constr -> constr
val eta_reduce_head : constr -> constr
val eq_constr : constr -> constr -> bool
val eta_eq_constr : constr -> constr -> bool

(*s The following functions substitutes [what] by [Rel 1] in [where] *)
val subst_term : what:constr -> where:constr -> constr
val subst_term_occ : occs:int list -> what:constr -> where:constr -> constr
val subst_term_occ_decl : occs:int list -> what:constr ->
      where:var_declaration -> var_declaration

val replace_consts :
  (section_path * (identifier list * constr) option) list -> constr -> constr

(* [subst_meta bl c] substitutes the metavar $i$ by $c_i$ in [c] 
   for each binding $(i,c_i)$ in [bl],
   and raises [Not_found] if [c] contains a meta that is not in the 
   association list *) 

val subst_meta : (int * constr) list -> constr -> constr

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
  | OpRec of fix_kind * Names.name list

val splay_constr : constr -> constr_operator * constr array
val gather_constr : constr_operator * constr array -> constr

val splay_constr_with_binders : constr ->
      constr_operator * (name * constr option * constr) list * constr array
val gather_constr_with_binders : 
  constr_operator * (name * constr option * constr) list * constr array
  -> constr

val generic_fold_left :
  ('a -> constr -> 'a) -> 'a -> (name * constr option * constr) list
      -> constr array -> 'a

val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a

val fold_constr_with_binders :
  ('a -> 'a) -> ('a -> 'b -> constr -> 'b) -> 'a -> 'b -> constr -> 'b

val iter_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit

val map_constr : (constr -> constr) -> constr -> constr

val map_constr_with_binders :
  (name -> 'a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr


(*s Hash-consing functions for constr. *)

val hcons_constr:
  (section_path -> section_path) *
  (section_path -> section_path) *
  (name -> name) *
  (identifier -> identifier) *
  (string -> string) 
  ->
    (constr -> constr) *
    (constr -> constr) *
    (typed_type -> typed_type)

val hcons1_constr : constr -> constr
