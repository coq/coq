(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Context

(** {5 Redeclaration of types from module Constr and Sorts}

    This reexports constructors of inductive types defined in module [Constr],
    for compatibility purposes. Refer to this module for further info.

*)

type contents = Sorts.contents = Pos | Null

type sorts = Sorts.t =
  | Prop of contents       (** Prop and Set *)
  | Type of Univ.universe  (** Type *)

type sorts_family = Sorts.family = InProp | InSet | InType

type constr = Constr.constr
(** Alias types, for compatibility. *)

type types = Constr.types
(** Same as [constr], for documentation purposes. *)

type existential_key = Constr.existential_key

type existential = Constr.existential

type metavariable = Constr.metavariable

type case_style = Constr.case_style =
  LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle

type case_printing = Constr.case_printing =
  { ind_nargs : int; style     : case_style }

type case_info = Constr.case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array;
    ci_cstr_nargs : int array;
    ci_pp_info    : case_printing
  }

type cast_kind = Constr.cast_kind =
  VMcast | NATIVEcast | DEFAULTcast | REVERTcast

type rec_declaration = Constr.rec_declaration
type fixpoint = Constr.fixpoint
type cofixpoint = Constr.cofixpoint
type 'constr pexistential = 'constr Constr.pexistential
type ('constr, 'types) prec_declaration =
  ('constr, 'types) Constr.prec_declaration
type ('constr, 'types) pfixpoint = ('constr, 'types) Constr.pfixpoint
type ('constr, 'types) pcofixpoint = ('constr, 'types) Constr.pcofixpoint

type ('constr, 'types) kind_of_term = ('constr, 'types) Constr.kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of sorts
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint

type values = Constr.values

(** {5 Simple term case analysis. } *)

val isRel  : constr -> bool
val isRelN : int -> constr -> bool
val isVar  : constr -> bool
val isVarId : Id.t -> constr -> bool
val isInd  : constr -> bool
val isEvar : constr -> bool
val isMeta : constr -> bool
val isMetaOf : metavariable -> constr -> bool
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

val is_Prop : constr -> bool
val is_Set  : constr -> bool
val isprop : constr -> bool
val is_Type : constr -> bool
val iskind : constr -> bool
val is_small : sorts -> bool


(** {5 Term destructors } *)
(** Destructor operations are partial functions and
    @raise DestKO if the term has not the expected form. *)

exception DestKO

(** Destructs a DeBrujin index *)
val destRel : constr -> int

(** Destructs an existential variable *)
val destMeta : constr -> metavariable

(** Destructs a variable *)
val destVar : constr -> Id.t

(** Destructs a sort. [is_Prop] recognizes the sort {% \textsf{%}Prop{% }%}, whether
   [isprop] recognizes both {% \textsf{%}Prop{% }%} and {% \textsf{%}Set{% }%}. *)
val destSort : constr -> sorts

(** Destructs a casted term *)
val destCast : constr -> constr * cast_kind * constr

(** Destructs the product {% $ %}(x:t_1)t_2{% $ %} *)
val destProd : types -> Name.t * types * types

(** Destructs the abstraction {% $ %}[x:t_1]t_2{% $ %} *)
val destLambda : constr -> Name.t * types * constr

(** Destructs the let {% $ %}[x:=b:t_1]t_2{% $ %} *)
val destLetIn : constr -> Name.t * constr * types * constr

(** Destructs an application *)
val destApp : constr -> constr * constr array

(** Obsolete synonym of destApp *)
val destApplication : constr -> constr * constr array

(** Decompose any term as an applicative term; the list of args can be empty *)
val decompose_app : constr -> constr * constr list

(** Same as [decompose_app], but returns an array. *)
val decompose_appvect : constr -> constr * constr array

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


(** {5 Derived constructors} *)

(** non-dependent product [t1 -> t2], an alias for
   [forall (_:t1), t2]. Beware [t_2] is NOT lifted.
   Eg: in context [A:Prop], [A->A] is built by [(mkArrow (mkRel 0) (mkRel 1))]
*)
val mkArrow : types -> types -> constr

(** Named version of the functions from [Term]. *)
val mkNamedLambda : Id.t -> types -> constr -> constr
val mkNamedLetIn : Id.t -> constr -> types -> constr -> constr
val mkNamedProd : Id.t -> types -> types -> types

(** Constructs either [(x:t)c] or [[x=b:t]c] *)
val mkProd_or_LetIn : rel_declaration -> types -> types
val mkProd_wo_LetIn : rel_declaration -> types -> types
val mkNamedProd_or_LetIn : named_declaration -> types -> types
val mkNamedProd_wo_LetIn : named_declaration -> types -> types

(** Constructs either [[x:t]c] or [[x=b:t]c] *)
val mkLambda_or_LetIn : rel_declaration -> constr -> constr
val mkNamedLambda_or_LetIn : named_declaration -> constr -> constr

(** {5 Other term constructors. } *)

(** [applist (f,args)] and its variants work as [mkApp] *)

val applist : constr * constr list -> constr
val applistc : constr -> constr list -> constr
val appvect : constr * constr array -> constr
val appvectc : constr -> constr array -> constr

(** [prodn n l b] = [forall (x_1:T_1)...(x_n:T_n), b]
   where [l] is [(x_n,T_n)...(x_1,T_1)...]. *)
val prodn : int -> (Name.t * constr) list -> constr -> constr

(** [compose_prod l b]
   @return [forall (x_1:T_1)...(x_n:T_n), b]
   where [l] is [(x_n,T_n)...(x_1,T_1)].
   Inverse of [decompose_prod]. *)
val compose_prod : (Name.t * constr) list -> constr -> constr

(** [lamn n l b]
    @return [fun (x_1:T_1)...(x_n:T_n) => b]
   where [l] is [(x_n,T_n)...(x_1,T_1)...]. *)
val lamn : int -> (Name.t * constr) list -> constr -> constr

(** [compose_lam l b]
   @return [fun (x_1:T_1)...(x_n:T_n) => b]
   where [l] is [(x_n,T_n)...(x_1,T_1)].
   Inverse of [it_destLam] *)
val compose_lam : (Name.t * constr) list -> constr -> constr

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

(** {5 Other term destructors. } *)

(** Transforms a product term {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a product. *)
val decompose_prod : constr -> (Name.t*constr) list * constr

(** Transforms a lambda term {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a lambda. *)
val decompose_lam : constr -> (Name.t*constr) list * constr

(** Given a positive integer n, transforms a product term
   {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %}
   into the pair {% $ %}([(xn,Tn);...;(x1,T1)],T){% $ %}. *)
val decompose_prod_n : int -> constr -> (Name.t * constr) list * constr

(** Given a positive integer {% $ %}n{% $ %}, transforms a lambda term
   {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %} *)
val decompose_lam_n : int -> constr -> (Name.t * constr) list * constr

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

(** {5 ... } *)
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

(** {5 Kind of type} *)

type ('constr, 'types) kind_of_type =
  | SortType   of sorts
  | CastType   of 'types * 'types
  | ProdType   of Name.t * 'types * 'types
  | LetInType  of Name.t * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

val kind_of_type : types -> (constr, types) kind_of_type

(** {5 Redeclaration of stuff from module [Sorts]} *)

val set_sort  : sorts
(** Alias for Sorts.set *)

val prop_sort : sorts
(** Alias for Sorts.prop *)

val type1_sort  : sorts
(** Alias for Sorts.type1 *)

val sorts_ord : sorts -> sorts -> int
(** Alias for Sorts.compare *)

val is_prop_sort : sorts -> bool
(** Alias for Sorts.is_prop *)

val family_of_sort : sorts -> sorts_family
(** Alias for Sorts.family *)

(** {5 Redeclaration of stuff from module [Constr]}

    See module [Constr] for further info. *)

(** {6 Term constructors. } *)

val mkRel : int -> constr
val mkVar : Id.t -> constr
val mkMeta : metavariable -> constr
val mkEvar : existential -> constr
val mkSort : sorts -> types
val mkProp : types
val mkSet  : types
val mkType : Univ.universe -> types
val mkCast : constr * cast_kind * constr -> constr
val mkProd : Name.t * types * types -> types
val mkLambda : Name.t * types * constr -> constr
val mkLetIn : Name.t * constr * types * constr -> constr
val mkApp : constr * constr array -> constr
val mkConst : constant -> constr
val mkInd : inductive -> constr
val mkConstruct : constructor -> constr
val mkCase : case_info * constr * constr * constr array -> constr
val mkFix : fixpoint -> constr
val mkCoFix : cofixpoint -> constr

(** {6 Aliases} *)

val eq_constr : constr -> constr -> bool
(** Alias for [Constr.equal] *)

val kind_of_term : constr -> (constr, types) kind_of_term
(** Alias for [Constr.kind] *)

val constr_ord : constr -> constr -> int
(** Alias for [Constr.compare] *)

val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a
(** Alias for [Constr.fold] *)

val map_constr : (constr -> constr) -> constr -> constr
(** Alias for [Constr.map] *)

val map_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr
(** Alias for [Constr.map_with_binders] *)

val iter_constr : (constr -> unit) -> constr -> unit
(** Alias for [Constr.iter] *)

val iter_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit
(** Alias for [Constr.iter_with_binders] *)

val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool
(** Alias for [Constr.compare_head] *)

val hash_constr : constr -> int
(** Alias for [Constr.hash] *)

val hcons_sorts : sorts -> sorts
(** Alias for [Constr.hashcons_sorts] *)

val hcons_constr : constr -> constr
(** Alias for [Constr.hashcons] *)

val hcons_types : types -> types
(** Alias for [Constr.hashcons] *)
