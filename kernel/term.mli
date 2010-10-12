(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names


(** {6 The sorts of CCI. } *)

type contents = Pos | Null

type sorts =
  | Prop of contents       (** Prop and Set *)
  | Type of Univ.universe  (** Type *)

val set_sort  : sorts
val prop_sort : sorts
val type1_sort  : sorts

(** {6 The sorts family of CCI. } *)

type sorts_family = InProp | InSet | InType

val family_of_sort : sorts -> sorts_family

(** {6 Useful types } *)

(** {6 Existential variables } *)
type existential_key = int

(** {6 Existential variables } *)
type metavariable = int

(** {6 Case annotation } *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle 
  | RegularStyle (** infer printing form from number of constructor *)
type case_printing =
  { ind_nargs : int; (** length of the arity of the inductive type *)
    style     : case_style }

(** the integer is the number of real args, needed for reduction *)
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (** number of real args of each constructor *)
    ci_pp_info    : case_printing (** not interpreted by the kernel *)
  }

(** {6 The type of constructions } *)

type constr

(** [eq_constr a b] is true if [a] equals [b] modulo alpha, casts,
   and application grouping *)
val eq_constr : constr -> constr -> bool

(** [types] is the same as [constr] but is intended to be used for
   documentation to indicate that such or such function specifically works
   with {e types} (i.e. terms of type a sort).
   (Rem:plurial form since [type] is a reserved ML keyword) *)

type types = constr

(** {5 Functions for dealing with constr terms. }
  The following functions are intended to simplify and to uniform the
  manipulation of terms. Some of these functions may be overlapped with
  previous ones. *)

(** {6 Term constructors. } *)

(** Constructs a DeBrujin index (DB indices begin at 1) *)
val mkRel : int -> constr

(** Constructs a Variable *)
val mkVar : identifier -> constr

(** Constructs an patvar named "?n" *)
val mkMeta : metavariable -> constr

(** Constructs an existential variable *)
type existential = existential_key * constr array
val mkEvar : existential -> constr

(** Construct a sort *)
val mkSort : sorts -> types
val mkProp : types
val mkSet  : types
val mkType : Univ.universe -> types


(** This defines the strategy to use for verifiying a Cast *)
type cast_kind = VMcast | DEFAULTcast

(** Constructs the term [t1::t2], i.e. the term t{_ 1} casted with the
   type t{_ 2} (that means t2 is declared as the type of t1). *)
val mkCast : constr * cast_kind * constr -> constr

(** Constructs the product [(x:t1)t2] *)
val mkProd : name * types * types -> types
val mkNamedProd : identifier -> types -> types -> types

(** non-dependent product [t1 -> t2], an alias for
   [forall (_:t1), t2]. Beware [t_2] is NOT lifted.
   Eg: in context [A:Prop], [A->A] is built by [(mkArrow (mkRel 0) (mkRel 1))]
*)
val mkArrow : types -> types -> constr

(** Constructs the abstraction \[x:t{_ 1}\]t{_ 2} *)
val mkLambda : name * types * constr -> constr
val mkNamedLambda : identifier -> types -> constr -> constr

(** Constructs the product [let x = t1 : t2 in t3] *)
val mkLetIn : name * constr * types * constr -> constr
val mkNamedLetIn : identifier -> constr -> types -> constr -> constr

(** [mkApp (f,[| t_1; ...; t_n |]] constructs the application
   {% $(f~t_1~\dots~t_n)$ %}. *)
val mkApp : constr * constr array -> constr

(** Constructs a constant 
   The array of terms correspond to the variables introduced in the section *)
val mkConst : constant -> constr

(** Inductive types *)

(** Constructs the ith (co)inductive type of the block named kn 
   The array of terms correspond to the variables introduced in the section *)
val mkInd : inductive -> constr

(** Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. The array of terms correspond to the variables
   introduced in the section *)
val mkConstruct : constructor -> constr

(** Constructs a destructor of inductive type.
    
    [mkCase ci p c ac] stand for match [c] as [x] in [I args] return [p] with [ac] 
    presented as describe in [ci].

    [p] stucture is [fun args x -> "return clause"]

    [ac]{^ ith} element is ith constructor case presented as 
    {e lambda construct_args (without params). case_term } *)
val mkCase : case_info * constr * constr * constr array -> constr

(** If [recindxs = [|i1,...in|]]
      [funnames = [|f1,.....fn|]]
      [typarray = [|t1,...tn|]]
      [bodies   = [|b1,.....bn|]]
   then [mkFix ((recindxs,i), funnames, typarray, bodies) ]
   constructs the {% $ %}i{% $ %}th function of the block (counting from 0)

    [Fixpoint f1 [ctx1] = b1
     with     f2 [ctx2] = b2
     ...
     with     fn [ctxn] = bn.]

   where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
*)
type rec_declaration = name array * types array * constr array
type fixpoint = (int array * int) * rec_declaration
val mkFix : fixpoint -> constr

(** If [funnames = [|f1,.....fn|]]
      [typarray = [|t1,...tn|]]
      [bodies   = [b1,.....bn]] 
   then [mkCoFix (i, (funnames, typarray, bodies))]
   constructs the ith function of the block
   
    [CoFixpoint f1 = b1
     with       f2 = b2
     ...
     with       fn = bn.]
 *)
type cofixpoint = int * rec_declaration
val mkCoFix : cofixpoint -> constr

(* Constructs native term *)
val mkInt : Native.Uint31.t -> constr
val mkArray : types * constr array  -> constr


(** {6 Concrete type for making pattern-matching. } *)

(** [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type ('constr, 'types) prec_declaration =
    name array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of identifier
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of sorts
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of name * 'types * 'types
  | Lambda    of name * 'types * 'constr
  | LetIn     of name * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | NativeInt of Native.Uint31.t
  | NativeArr of 'types * 'constr array

(** User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

val kind_of_term : constr -> (constr, types) kind_of_term

(** Experimental, used in Presburger contrib *)
type ('constr, 'types) kind_of_type =
  | SortType   of sorts
  | CastType   of 'types * 'types
  | ProdType   of name * 'types * 'types
  | LetInType  of name * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

val kind_of_type : types -> (constr, types) kind_of_type

(** {6 Simple term case analysis. } *)

val isRel  : constr -> bool
val isVar  : constr -> bool
val isInd  : constr -> bool
val isEvar : constr -> bool
val isMeta : constr -> bool
val isEvar_or_Meta : constr -> bool
val isSort : constr -> bool
val isCast : constr -> bool
val isApp : constr -> bool
val isLambda : constr -> bool
val isLetIn : constr -> bool
val isProd : constr -> bool
val isConst : constr -> bool
val isConstruct : constr -> bool
val isFix : constr -> bool
val isCoFix : constr -> bool
val isCase : constr -> bool
val isInt : constr -> bool
val isArray : constr -> bool

val is_Prop : constr -> bool
val is_Set  : constr -> bool
val isprop : constr -> bool
val is_Type : constr -> bool
val iskind : constr -> bool
val is_small : sorts -> bool


(** {6 Term destructors } *)
(** Destructor operations are partial functions and
    @raise Invalid_argument "dest*" if the term has not the expected form. *)

(** Destructs a DeBrujin index *)
val destRel : constr -> int

(** Destructs an existential variable *)
val destMeta : constr -> metavariable

(** Destructs a variable *)
val destVar : constr -> identifier

(** Destructs a sort. [is_Prop] recognizes the sort {% \textsf{%}Prop{% }%}, whether
   [isprop] recognizes both {% \textsf{%}Prop{% }%} and {% \textsf{%}Set{% }%}. *)
val destSort : constr -> sorts

(** Destructs a casted term *)
val destCast : constr -> constr * cast_kind * constr

(** Destructs the product {% $ %}(x:t_1)t_2{% $ %} *)
val destProd : types -> name * types * types

(** Destructs the abstraction {% $ %}[x:t_1]t_2{% $ %} *)
val destLambda : constr -> name * types * constr

(** Destructs the let {% $ %}[x:=b:t_1]t_2{% $ %} *)
val destLetIn : constr -> name * constr * types * constr

(** Destructs an application *)
val destApp : constr -> constr * constr array

(** Obsolete synonym of destApp *)
val destApplication : constr -> constr * constr array

(** Decompose any term as an applicative term; the list of args can be empty *)
val decompose_app : constr -> constr * constr list

(** Destructs a constant *)
val destConst : constr -> constant

(** Destructs an existential variable *)
val destEvar : constr -> existential

(** Destructs a (co)inductive type *)
val destInd : constr -> inductive

(** Destructs a constructor *)
val destConstruct : constr -> constructor

(** Destructs a [match c as x in I args return P with ... |
Ci(...yij...) => ti | ... end] (or [let (..y1i..) := c as x in I args
return P in t1], or [if c then t1 else t2])
@return [(info,c,fun args x => P,[|...|fun yij => ti| ...|])]
where [info] is pretty-printing information *)
val destCase : constr -> case_info * constr * constr * constr array

(** Destructs the {% $ %}i{% $ %}th function of the block
   [Fixpoint f{_ 1} ctx{_ 1} = b{_ 1}
    with    f{_ 2} ctx{_ 2} = b{_ 2}
    ...
    with    f{_ n} ctx{_ n} = b{_ n}],
   where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
*)
val destFix : constr -> fixpoint

val destCoFix : constr -> cofixpoint

(* Destructs native term *)
val destInt : constr -> Native.Uint31.t
val destArray : constr -> types * constr array

(** {6 Local } *)
(** A {e declaration} has the form [(name,body,type)]. It is either an
    {e assumption} if [body=None] or a {e definition} if
    [body=Some actualbody]. It is referred by {e name} if [na] is an
    identifier or by {e relative index} if [na] is not an identifier
    (in the latter case, [na] is of type [name] but just for printing
    purpose) *)

type named_declaration = identifier * constr option * types
type rel_declaration = name * constr option * types

val map_named_declaration :
  (constr -> constr) -> named_declaration -> named_declaration
val map_rel_declaration :
  (constr -> constr) -> rel_declaration -> rel_declaration

val fold_named_declaration :
  (constr -> 'a -> 'a) -> named_declaration -> 'a -> 'a
val fold_rel_declaration :
  (constr -> 'a -> 'a) -> rel_declaration -> 'a -> 'a

(** {6 Contexts of declarations referred to by de Bruijn indices } *)

(** In [rel_context], more recent declaration is on top *)
type rel_context = rel_declaration list

val empty_rel_context : rel_context
val add_rel_decl : rel_declaration -> rel_context -> rel_context

val lookup_rel : int -> rel_context -> rel_declaration
val rel_context_length : rel_context -> int
val rel_context_nhyps : rel_context -> int

(** Constructs either [(x:t)c] or [[x=b:t]c] *)
val mkProd_or_LetIn : rel_declaration -> types -> types
val mkProd_wo_LetIn : rel_declaration -> types -> types
val mkNamedProd_or_LetIn : named_declaration -> types -> types
val mkNamedProd_wo_LetIn : named_declaration -> types -> types

(** Constructs either [[x:t]c] or [[x=b:t]c] *)
val mkLambda_or_LetIn : rel_declaration -> constr -> constr
val mkNamedLambda_or_LetIn : named_declaration -> constr -> constr

(** {6 Other term constructors. } *)

val abs_implicit : constr -> constr
val lambda_implicit : constr -> constr
val lambda_implicit_lift : int -> constr -> constr

(** [applist (f,args)] and its variants work as [mkApp] *)

val applist : constr * constr list -> constr
val applistc : constr -> constr list -> constr
val appvect : constr * constr array -> constr
val appvectc : constr -> constr array -> constr

(** [prodn n l b] = [forall (x_1:T_1)...(x_n:T_n), b]
   where [l] is [(x_n,T_n)...(x_1,T_1)...]. *)
val prodn : int -> (name * constr) list -> constr -> constr

(** [compose_prod l b]
   @return [forall (x_1:T_1)...(x_n:T_n), b]
   where [l] is [(x_n,T_n)...(x_1,T_1)].
   Inverse of [decompose_prod]. *)
val compose_prod : (name * constr) list -> constr -> constr

(** [lamn n l b]
    @return [fun (x_1:T_1)...(x_n:T_n) => b]
   where [l] is [(x_n,T_n)...(x_1,T_1)...]. *)
val lamn : int -> (name * constr) list -> constr -> constr

(** [compose_lam l b]
   @return [fun (x_1:T_1)...(x_n:T_n) => b]
   where [l] is [(x_n,T_n)...(x_1,T_1)].
   Inverse of [it_destLam] *)
val compose_lam : (name * constr) list -> constr -> constr

(** [to_lambda n l]
   @return [fun (x_1:T_1)...(x_n:T_n) => T]
   where [l] is [forall (x_1:T_1)...(x_n:T_n), T] *)
val to_lambda : int -> constr -> constr

(** [to_prod n l]
   @return [forall (x_1:T_1)...(x_n:T_n), T]
   where [l] is [fun (x_1:T_1)...(x_n:T_n) => T] *)
val to_prod : int -> constr -> constr

(** pseudo-reduction rule *)

(** [prod_appvect] [forall (x1:B1;...;xn:Bn), B] [a1...an] @return [B[a1...an]] *)
val prod_appvect : constr -> constr array -> constr
val prod_applist : constr -> constr list -> constr

val it_mkLambda_or_LetIn : constr -> rel_context -> constr
val it_mkProd_or_LetIn : types -> rel_context -> types

(** {6 Other term destructors. } *)

(** Transforms a product term {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a product.
   It includes also local definitions *)
val decompose_prod : constr -> (name*constr) list * constr

(** Transforms a lambda term {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a lambda. *)
val decompose_lam : constr -> (name*constr) list * constr

(** Given a positive integer n, transforms a product term
   {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %}
   into the pair {% $ %}([(xn,Tn);...;(x1,T1)],T){% $ %}. *)
val decompose_prod_n : int -> constr -> (name * constr) list * constr

(** Given a positive integer {% $ %}n{% $ %}, transforms a lambda term
   {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %} *)
val decompose_lam_n : int -> constr -> (name * constr) list * constr

(** Extract the premisses and the conclusion of a term of the form
   "(xi:Ti) ... (xj:=cj:Tj) ..., T" where T is not a product nor a let *)
val decompose_prod_assum : types -> rel_context * types

(** Idem with lambda's *)
val decompose_lam_assum : constr -> rel_context * constr

(** Idem but extract the first [n] premisses *)
val decompose_prod_n_assum : int -> types -> rel_context * types
val decompose_lam_n_assum : int -> constr -> rel_context * constr

(** [nb_lam] {% $ %}[x_1:T_1]...[x_n:T_n]c{% $ %} where {% $ %}c{% $ %} is not an abstraction
   gives {% $ %}n{% $ %} (casts are ignored) *)
val nb_lam : constr -> int

(** Similar to [nb_lam], but gives the number of products instead *)
val nb_prod : constr -> int

(** Returns the premisses/parameters of a type/term (let-in included) *)
val prod_assum : types -> rel_context
val lam_assum : constr -> rel_context

(** Returns the first n-th premisses/parameters of a type/term (let included)*)
val prod_n_assum : int -> types -> rel_context
val lam_n_assum : int -> constr -> rel_context

(** Remove the premisses/parameters of a type/term *)
val strip_prod : types -> types
val strip_lam : constr -> constr

(** Remove the first n-th premisses/parameters of a type/term *)
val strip_prod_n : int -> types -> types
val strip_lam_n : int -> constr -> constr

(** Remove the premisses/parameters of a type/term (including let-in) *)
val strip_prod_assum : types -> types
val strip_lam_assum : constr -> constr

(** flattens application lists *)
val collapse_appl : constr -> constr


(** Removes recursively the casts around a term i.e.
   [strip_outer_cast (Cast (Cast ... (Cast c, t) ... ))] is [c]. *)
val strip_outer_cast : constr -> constr

(** Apply a function letting Casted types in place *)
val under_casts : (constr -> constr) -> constr -> constr

(** Apply a function under components of Cast if any *)
val under_outer_cast : (constr -> constr) -> constr -> constr

(** {6 ... } *)
(** An "arity" is a term of the form [[x1:T1]...[xn:Tn]s] with [s] a sort.
    Such a term can canonically be seen as the pair of a context of types
    and of a sort *)

type arity = rel_context * sorts

(** Build an "arity" from its canonical form *)
val mkArity : arity -> types

(** Destructs an "arity" into its canonical form *)
val destArity : types -> arity

(** Tells if a term has the form of an arity *)
val isArity : types -> bool

(** {6 Occur checks } *)

(** [closedn n M] is true iff [M] is a (deBruijn) closed term under n binders *)
val closedn : int -> constr -> bool

(** [closed0 M] is true iff [M] is a (deBruijn) closed term *)
val closed0 : constr -> bool

(** [noccurn n M] returns true iff [Rel n] does NOT occur in term [M]  *)
val noccurn : int -> constr -> bool

(** [noccur_between n m M] returns true iff [Rel p] does NOT occur in term [M]
  for n <= p < n+m *)
val noccur_between : int -> int -> constr -> bool

(** Checking function for terms containing existential- or
   meta-variables.  The function [noccur_with_meta] does not consider
   meta-variables applied to some terms (intented to be its local
   context) (for existential variables, it is necessarily the case) *)
val noccur_with_meta : int -> int -> constr -> bool

(** {6 Relocation and substitution } *)

(** [exliftn el c] lifts [c] with lifting [el] *)
val exliftn : Esubst.lift -> constr -> constr

(** [liftn n k c] lifts by [n] indexes above or equal to [k] in [c] *)
val liftn : int -> int -> constr -> constr

(** [lift n c] lifts by [n] the positive indexes in [c] *)
val lift : int -> constr -> constr

(** [substnl [a1;...;an] k c] substitutes in parallel [a1],...,[an]
    for respectively [Rel(k+1)],...,[Rel(k+n)] in [c]; it relocates
    accordingly indexes in [a1],...,[an] *)
val substnl : constr list -> int -> constr -> constr
val substl : constr list -> constr -> constr
val subst1 : constr -> constr -> constr

val substnl_decl : constr list -> int -> rel_declaration -> rel_declaration
val substl_decl : constr list -> rel_declaration -> rel_declaration
val subst1_decl : constr -> rel_declaration -> rel_declaration

val subst1_named_decl : constr -> named_declaration -> named_declaration
val substl_named_decl : constr list -> named_declaration -> named_declaration

val replace_vars : (identifier * constr) list -> constr -> constr
val subst_var : identifier -> constr -> constr

(** [subst_vars [id1;...;idn] t] substitute [VAR idj] by [Rel j] in [t]
   if two names are identical, the one of least indice is kept *)
val subst_vars : identifier list -> constr -> constr

(** [substn_vars n [id1;...;idn] t] substitute [VAR idj] by [Rel j+n-1] in [t]
   if two names are identical, the one of least indice is kept *)
val substn_vars : int -> identifier list -> constr -> constr


(** {6 Functionals working on the immediate subterm of a construction } *)

(** [fold_constr f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a

(** [map_constr f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val map_constr : (constr -> constr) -> constr -> constr

(** [map_constr_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val map_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr

(** [iter_constr f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val iter_constr : (constr -> unit) -> constr -> unit

(** [iter_constr_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val iter_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit

(** [compare_constr f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's, binders
   name and Cases annotations are not taken into account *)

val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool

(*********************************************************************)

val hcons_constr:
  (constant -> constant) *
  (mutual_inductive -> mutual_inductive) *
  (dir_path -> dir_path) *
  (name -> name) *
  (identifier -> identifier) *
  (string -> string)
  ->
    (constr -> constr) *
    (types -> types)

val hcons1_constr : constr -> constr
val hcons1_types : types -> types

(**************************************)

type values
