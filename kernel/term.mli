
(*i $Id$ i*)

(*i*)
open Util
open Pp
open Names
(*i*)

(*s The sorts of CCI. *)

type contents = Pos | Null

type sorts =
  | Prop of contents       (* Prop and Set *)
  | Type of Univ.universe  (* Type *)

val mk_Set  : sorts
val mk_Prop : sorts

val print_sort : sorts -> std_ppcmds


type existential_key = int

type pattern_source = DefaultPat of int | RegularPat
type case_style = PrintLet | PrintIf | PrintCases
type case_printing =
    inductive_path * identifier array * int
    * case_style option * pattern_source array
(* the integer is the number of real args, needed for reduction *)
type case_info = int array * case_printing

(********************************************************************)
(* type of global reference *)

type global_reference =
  | VarRef of section_path
  | ConstRef of constant_path
  | IndRef of inductive_path
  | ConstructRef of constructor_path
  | EvarRef of int

(********************************************************************)
(* The type of constructions *)

type constr

(* [types] is the same as [constr] but is intended to be used where a
   {\em type} in CCI sense is expected (Rem:plurial form since [type] is a
   reserved ML keyword) *)

type types = constr

(*s Functions about [types] *)

val type_app : (constr -> constr) -> types -> types

val body_of_type : types -> constr

(*s A {\em declaration} has the form (name,body,type). It is either an
    {\em assumption} if [body=None] or a {\em definition} if
    [body=Some actualbody]. It is referred by {\em name} if [na] is an
    identifier or by {\em relative index} if [na] is not an identifier
    (in the latter case, [na] is of type [name] but just for printing
    purpose *)

type named_declaration = identifier * constr option * types
type rel_declaration = name * constr option * types

type arity = rel_declaration list * sorts

(*s Functions for dealing with constr terms.
  The following functions are intended to simplify and to uniform the 
  manipulation of terms. Some of these functions may be overlapped with
  previous ones. *)

(* Concrete type for making pattern-matching. *)

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type existential = int * constr array
type constant = constant_path * constr array
type constructor = constructor_path * constr array
type inductive = inductive_path * constr array
type rec_declaration = constr array * name list * constr array
type fixpoint = (int array * int) * rec_declaration
type cofixpoint = int * rec_declaration

(* [IsVar] is used for named variables and [IsRel] for variables as
   de Bruijn indices. *)

type kind_of_term =
  | IsRel          of int
  | IsMeta         of int
  | IsVar          of identifier
  | IsXtra         of string
  | IsSort         of sorts
  | IsCast         of constr * constr
  | IsProd         of name * types * constr 
  | IsLambda       of name * types * constr
  | IsLetIn        of name * constr * types * constr
  | IsApp         of constr * constr array
  | IsEvar         of existential
  | IsConst        of constant
  | IsMutInd       of inductive
  | IsMutConstruct of constructor
  | IsMutCase      of case_info * constr * constr * constr array
  | IsFix          of fixpoint
  | IsCoFix        of cofixpoint

(* User view of [constr]. For [IsApp], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

val kind_of_term : constr -> kind_of_term


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
val mkProd : name * types * constr -> constr
val mkNamedProd : identifier -> constr -> constr -> constr
val mkProd_string : string -> constr -> constr -> constr

(* Constructs the product $(x:t_1)t_2$ *)
val mkLetIn : name * constr * types * constr -> constr
val mkNamedLetIn : identifier -> constr -> constr -> constr -> constr

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
val mkProd_or_LetIn : rel_declaration -> constr -> constr
val mkNamedProd_or_LetIn : named_declaration -> constr -> constr

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
val mkLambda_or_LetIn : rel_declaration -> constr -> constr
val mkNamedLambda_or_LetIn : named_declaration -> constr -> constr

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
val mkProd_wo_LetIn : rel_declaration -> constr -> constr
val mkNamedProd_wo_LetIn : named_declaration -> constr -> constr

(* non-dependant product $t_1 \rightarrow t_2$ *)
val mkArrow : constr -> constr -> constr

(* Constructs the abstraction $[x:t_1]t_2$ *)
val mkLambda : name * types * constr -> constr
val mkNamedLambda : identifier -> constr -> constr -> constr

(* [mkLambda_string s t c] constructs $[s:t]c$ *)
val mkLambda_string : string -> constr -> constr -> constr

(* [mkApp (f,[| t_1; ...; t_n |]] constructs the application
   $(f~t_1~\dots~t_n)$. *)
val mkApp : constr * constr array -> constr
val mkAppA : constr array -> constr

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

(*s Term destructors. 
   Destructor operations are partial functions and
   raise [invalid_arg "dest*"] if the term has not the expected form. *)

(* Destructs a term of the form $(x_1:T_1)..(x_n:T_n)s$ into the pair *)
val destArity : constr -> arity
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
val is_Prop : constr -> bool
val is_Set : constr -> bool
val isprop : constr -> bool
val is_Type : constr -> bool
val iskind : constr -> bool
val isSort : constr -> bool

val isType : sorts -> bool
val is_small : sorts -> bool (* true for \textsf{Prop} and \textsf{Set} *)

(* Destructs a casted term *)
val destCast : constr -> constr * constr
val isCast : constr -> bool

(* Removes recursively the casts around a term i.e.
   [strip_outer_cast] (Cast (Cast ... (Cast c, t) ... ))] is [c]. *)
val strip_outer_cast : constr -> constr

(* Apply a function letting Casted types in place *)
val under_casts : (constr -> constr) -> constr -> constr

(* Tests if a de Bruijn index *)
val isRel  : constr -> bool

(* Tests if a variable *)
val isVar  : constr -> bool

(* Destructs the product $(x:t_1)t_2$ *)
val destProd : constr -> name * constr * constr
val hd_of_prod : constr -> constr
(*i
val hd_is_constructor : constr -> bool
i*)

(* Destructs the abstraction $[x:t_1]t_2$ *)
val destLambda : constr -> name * constr * constr

(* Destructs the let $[x:=b:t_1]t_2$ *)
val destLetIn : constr -> name * constr * constr * constr

(* Destructs an application *)
val isApp : constr -> bool
(*i
val hd_app : constr -> constr 
val args_app : constr -> constr array
i*)
val destApplication : constr -> constr * constr array

(* Destructs a constant *)
val destConst : constr -> constant_path * constr array
val isConst : constr -> bool
val path_of_const : constr -> constant_path
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
val destFix : constr -> fixpoint

val destCoFix : constr -> cofixpoint

(*s Other term constructors. *)

val abs_implicit : constr -> constr
val lambda_implicit : constr -> constr
val lambda_implicit_lift : int -> constr -> constr

(* [applist (f,args)] and co work as [mkApp] *)

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

(* [substnl [a1;...;an] k c] substitutes in parallel [a1],...,[an]
    for respectively [Rel(k+1)],...,[Rel(k+n)] in [c]; it relocates
    accordingly indexes in [a1],...,[an] *)
val substnl : constr list -> int -> constr -> constr
val substl : constr list -> constr -> constr
val subst1 : constr -> constr -> constr

val substl_decl : constr list -> named_declaration -> named_declaration
val subst1_decl : constr -> named_declaration -> named_declaration

(* [global_vars c] returns the list of [id]'s occurring as [VAR id] in [c] *)
val global_vars : constr -> identifier list

(* [global_vars_decl d] returns the list of [id]'s occurring as [VAR
    id] in declaration [d] (type and body if any) *)
val global_vars_decl : named_declaration -> identifier list

val global_vars_set : constr -> Idset.t
val replace_vars : (identifier * constr) list -> constr -> constr
val subst_var : identifier -> constr -> constr

(* [subst_vars [id1;...;idn] t] substitute [VAR idj] by [Rel j] in [t]
   if two names are identical, the one of least indice is keeped *)
val subst_vars : identifier list -> constr -> constr

(* [rel_list n m] and [rel_vect n m] compute [[Rel (n+m);...;Rel(n+1)]] *)
val rel_vect : int -> int -> constr array
val rel_list : int -> int -> constr list

(*s Compact representation of implicit lifts. \\
   [ELSHFT(l,n)] == lift of [n], then apply [lift l].
  [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders. *)
type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int
  | ELLFT of int * lift_spec
val el_shft : int -> lift_spec -> lift_spec
val el_liftn : int -> lift_spec -> lift_spec
val el_lift : lift_spec -> lift_spec
val reloc_rel : int -> lift_spec -> int

(*s Occur check functions. *)                         

val occur_meta : constr -> bool

(*i Returns the maximum of metas. Returns -1 if there is no meta i*)
(*i val max_occur_meta : constr -> int i*)

val occur_existential : constr -> bool

(* [(occur_const (s:section_path) c)] returns [true] if constant [s] occurs 
   in c, [false] otherwise *)
val occur_const : constant_path -> constr -> bool

(* [(occur_evar ev c)] returns [true] if existential variable [ev] occurs 
   in c, [false] otherwise *)
val occur_evar : existential_key -> constr -> bool

(* [(occur_var id c)] returns [true] if variable [id] occurs free
   in c, [false] otherwise *)
val occur_var : identifier -> constr -> bool

val occur_var_in_decl : identifier -> named_declaration -> bool

(* [dependent M N] is true iff M is eq\_constr with a subterm of N 
   M is appropriately lifted through abstractions of N *)
val dependent : constr -> constr -> bool

(* strips head casts and flattens head applications *)
val strip_head_cast : constr -> constr
val rename_bound_var : identifier list -> constr -> constr
val eta_reduce_head : constr -> constr
val eq_constr : constr -> constr -> bool
val eta_eq_constr : constr -> constr -> bool

(*s The following functions substitutes [what] by [Rel 1] in [where] *)
val subst_term : what:constr -> where:constr -> constr
val subst_term_occ : occs:int list -> what:constr -> where:constr -> constr
val subst_term_occ_decl : occs:int list -> what:constr ->
      where:named_declaration -> named_declaration

(* [subst_meta bl c] substitutes the metavar $i$ by $c_i$ in [c] 
   for each binding $(i,c_i)$ in [bl],
   and raises [Not_found] if [c] contains a meta that is not in the 
   association list *) 

val subst_meta : (int * constr) list -> constr -> constr

(*s Generic representation of constructions *)

type fix_kind = RFix of (int array * int) | RCoFix of int

type constr_operator =
  | OpMeta of int
  | OpSort of sorts
  | OpRel of int | OpVar of identifier
  | OpCast | OpProd of name | OpLambda of name | OpLetIn of name
  | OpApp | OpConst of constant_path
  | OpEvar of existential_key
  | OpMutInd of inductive_path
  | OpMutConstruct of constructor_path
  | OpMutCase of case_info
  | OpRec of fix_kind * Names.name list
  | OpXtra of string

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

(*s Functionals working on the immediate subterm of a construction *)

(* [fold_constr f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

val fold_constr_with_binders :
  ('a -> 'a) -> ('a -> 'b -> constr -> 'b) -> 'a -> 'b -> constr -> 'b

(* [iter_constr f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val iter_constr : (constr -> unit) -> constr -> unit

(* [iter_constr_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val iter_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit

(* [map_constr f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val map_constr : (constr -> constr) -> constr -> constr

(* [map_constr_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val map_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr

(* [map_constr_with_named_binders g f l c] maps [f l] on the immediate
   subterms of [c]; it carries an extra data [l] (typically a name
   list) which is processed by [g na] (which typically cons [na] to
   [l]) at each binder traversal (with name [na]); it is not recursive
   and the order with which subterms are processed is not specified *)

val map_constr_with_named_binders :
  (name -> 'a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr

(* [map_constr_with_binders_left_to_right g f n c] maps [f n] on the
   immediate subterms of [c]; it carries an extra data [n] (typically
   a lift index) which is processed by [g] (which typically add 1 to
   [n]) at each binder traversal; the subterms are processed from left
   to right according to the usual representation of the constructions
   (this may matter if [f] does a side-effect); it is not recursive *)

val map_constr_with_binders_left_to_right :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr

(* [map_constr_with_named_binders g f l c] maps [f l] on the immediate
   subterms of [c]; it carries an extra data [l] (typically a name
   list) which is processed by [g na] (which typically cons [na] to
   [l]) at each binder traversal (with name [na]); it is not recursive
   and the order with which subterms are processed is not specified *)

val map_constr_with_full_binders :
  (rel_declaration -> 'a -> 'a) -> ('a -> constr -> constr) ->
      'a -> constr -> constr

(* [compare_constr f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's, binders
   name and Cases annotations are not taken into account *)

val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool

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
    (types -> types)

val hcons1_constr : constr -> constr
