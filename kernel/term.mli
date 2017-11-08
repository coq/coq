(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr

(** {5 Redeclaration of types from module Constr and Sorts}

    This reexports constructors of inductive types defined in module [Constr],
    for compatibility purposes. Refer to this module for further info.

*)

(** {5 Simple term case analysis. } *)
val isRel  : constr -> bool
val isRelN : int -> constr -> bool
val isVar  : constr -> bool
val isVarId : Id.t -> constr -> bool
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
val isProj : constr -> bool

val is_Prop : constr -> bool
val is_Set  : constr -> bool
val isprop : constr -> bool
val is_Type : constr -> bool
val iskind : constr -> bool
val is_small : Sorts.t -> bool


(** {5 Term destructors } *)
(** Destructor operations are partial functions and
    @raise DestKO if the term has not the expected form. *)

exception DestKO

(** Destructs a de Bruijn index *)
val destRel : constr -> int

(** Destructs an existential variable *)
val destMeta : constr -> metavariable

(** Destructs a variable *)
val destVar : constr -> Id.t

(** Destructs a sort. [is_Prop] recognizes the sort {% \textsf{%}Prop{% }%}, whether
   [isprop] recognizes both {% \textsf{%}Prop{% }%} and {% \textsf{%}Set{% }%}. *)
val destSort : constr -> Sorts.t

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
val destConst : constr -> Constant.t puniverses

(** Destructs an existential variable *)
val destEvar : constr -> existential

(** Destructs a (co)inductive type *)
val destInd : constr -> inductive puniverses

(** Destructs a constructor *)
val destConstruct : constr -> constructor puniverses

(** Destructs a [match c as x in I args return P with ... |
Ci(...yij...) => ti | ... end] (or [let (..y1i..) := c as x in I args
return P in t1], or [if c then t1 else t2])
@return [(info,c,fun args x => P,[|...|fun yij => ti| ...|])]
where [info] is pretty-printing information *)
val destCase : constr -> case_info * constr * constr * constr array

(** Destructs a projection *)
val destProj : constr -> projection * constr

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
   Eg: in context [A:Prop], [A->A] is built by [(mkArrow (mkRel 1) (mkRel 2))]
*)
val mkArrow : types -> types -> constr

(** Named version of the functions from [Term]. *)
val mkNamedLambda : Id.t -> types -> constr -> constr
val mkNamedLetIn : Id.t -> constr -> types -> constr -> constr
val mkNamedProd : Id.t -> types -> types -> types

(** Constructs either [(x:t)c] or [[x=b:t]c] *)
val mkProd_or_LetIn : Context.Rel.Declaration.t -> types -> types
val mkProd_wo_LetIn : Context.Rel.Declaration.t -> types -> types
val mkNamedProd_or_LetIn : Context.Named.Declaration.t -> types -> types
val mkNamedProd_wo_LetIn : Context.Named.Declaration.t -> types -> types

(** Constructs either [[x:t]c] or [[x=b:t]c] *)
val mkLambda_or_LetIn : Context.Rel.Declaration.t -> constr -> constr
val mkNamedLambda_or_LetIn : Context.Named.Declaration.t -> constr -> constr

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

val it_mkLambda_or_LetIn : constr -> Context.Rel.t -> constr
val it_mkProd_or_LetIn : types -> Context.Rel.t -> types

(** In [lambda_applist c args], [c] is supposed to have the form
    [λΓ.c] with [Γ] without let-in; it returns [c] with the variables
    of [Γ] instantiated by [args]. *)
val lambda_applist : constr -> constr list -> constr
val lambda_appvect : constr -> constr array -> constr

(** In [lambda_applist_assum n c args], [c] is supposed to have the
    form [λΓ.c] with [Γ] of length [m] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val lambda_applist_assum : int -> constr -> constr list -> constr
val lambda_appvect_assum : int -> constr -> constr array -> constr

(** pseudo-reduction rule *)

(** [prod_appvect] [forall (x1:B1;...;xn:Bn), B] [a1...an] @return [B[a1...an]] *)
val prod_appvect : constr -> constr array -> constr
val prod_applist : constr -> constr list -> constr

(** In [prod_appvect_assum n c args], [c] is supposed to have the
    form [∀Γ.c] with [Γ] of length [m] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val prod_appvect_assum : int -> constr -> constr array -> constr
val prod_applist_assum : int -> constr -> constr list -> constr

(** {5 Other term destructors. } *)

(** Transforms a product term {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a product. *)
val decompose_prod : constr -> (Name.t*constr) list * constr

(** Transforms a lambda term {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a lambda. *)
val decompose_lam : constr -> (Name.t*constr) list * constr

(** Given a positive integer n, decompose a product term
   {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %}
   into the pair {% $ %}([(xn,Tn);...;(x1,T1)],T){% $ %}.
   Raise a user error if not enough products. *)
val decompose_prod_n : int -> constr -> (Name.t * constr) list * constr

(** Given a positive integer {% $ %}n{% $ %}, decompose a lambda term
   {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}.
   Raise a user error if not enough lambdas. *)
val decompose_lam_n : int -> constr -> (Name.t * constr) list * constr

(** Extract the premisses and the conclusion of a term of the form
   "(xi:Ti) ... (xj:=cj:Tj) ..., T" where T is not a product nor a let *)
val decompose_prod_assum : types -> Context.Rel.t * types

(** Idem with lambda's and let's *)
val decompose_lam_assum : constr -> Context.Rel.t * constr

(** Idem but extract the first [n] premisses, counting let-ins. *)
val decompose_prod_n_assum : int -> types -> Context.Rel.t * types

(** Idem for lambdas, _not_ counting let-ins *)
val decompose_lam_n_assum : int -> constr -> Context.Rel.t * constr

(** Idem, counting let-ins *)
val decompose_lam_n_decls : int -> constr -> Context.Rel.t * constr

(** Return the premisses/parameters of a type/term (let-in included) *)
val prod_assum : types -> Context.Rel.t
val lam_assum : constr -> Context.Rel.t

(** Return the first n-th premisses/parameters of a type (let included and counted) *)
val prod_n_assum : int -> types -> Context.Rel.t

(** Return the first n-th premisses/parameters of a term (let included but not counted) *)
val lam_n_assum : int -> constr -> Context.Rel.t

(** Remove the premisses/parameters of a type/term *)
val strip_prod : types -> types
val strip_lam : constr -> constr

(** Remove the first n-th premisses/parameters of a type/term *)
val strip_prod_n : int -> types -> types
val strip_lam_n : int -> constr -> constr

(** Remove the premisses/parameters of a type/term (including let-in) *)
val strip_prod_assum : types -> types
val strip_lam_assum : constr -> constr

(** {5 ... } *)
(** An "arity" is a term of the form [[x1:T1]...[xn:Tn]s] with [s] a sort.
    Such a term can canonically be seen as the pair of a context of types
    and of a sort *)

type arity = Context.Rel.t * Sorts.t

(** Build an "arity" from its canonical form *)
val mkArity : arity -> types

(** Destruct an "arity" into its canonical form *)
val destArity : types -> arity

(** Tell if a term has the form of an arity *)
val isArity : types -> bool

(** {5 Kind of type} *)

type ('constr, 'types) kind_of_type =
  | SortType   of Sorts.t
  | CastType   of 'types * 'types
  | ProdType   of Name.t * 'types * 'types
  | LetInType  of Name.t * 'constr * 'types * 'types
  | AtomicType of 'constr * 'constr array

val kind_of_type : types -> (constr, types) kind_of_type

(** {5 Redeclaration of stuff from module [Sorts]} *)

val set_sort  : Sorts.t
[@@ocaml.deprecated "Alias for Sorts.set"]

val prop_sort : Sorts.t
[@@ocaml.deprecated "Alias for Sorts.prop"]

val type1_sort  : Sorts.t
[@@ocaml.deprecated "Alias for Sorts.type1"]

val sorts_ord : Sorts.t -> Sorts.t -> int
[@@ocaml.deprecated "Alias for Sorts.compare"]

val is_prop_sort : Sorts.t -> bool
[@@ocaml.deprecated "Alias for Sorts.is_prop"]

val family_of_sort : Sorts.t -> Sorts.family
[@@ocaml.deprecated "Alias for Sorts.family"]

(** {5 Redeclaration of stuff from module [Constr]}

    See module [Constr] for further info. *)

(** {6 Term constructors. } *)

val mkRel : int -> constr
[@@ocaml.deprecated "Alias for Constr.mkRel"]
val mkVar : Id.t -> constr
[@@ocaml.deprecated "Alias for Constr.mkVar"]
val mkMeta : metavariable -> constr
[@@ocaml.deprecated "Alias for Constr.mkMeta"]
val mkEvar : existential -> constr
[@@ocaml.deprecated "Alias for Constr.mkEvar"]
val mkSort : Sorts.t -> types
[@@ocaml.deprecated "Alias for Constr.mkSort"]
val mkProp : types
[@@ocaml.deprecated "Alias for Constr.mkProp"]
val mkSet  : types
[@@ocaml.deprecated "Alias for Constr.mkSet"]
val mkType : Univ.Universe.t -> types
[@@ocaml.deprecated "Alias for Constr.mkType"]
val mkCast : constr * cast_kind * constr -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkProd : Name.t * types * types -> types
[@@ocaml.deprecated "Alias for Constr"]
val mkLambda : Name.t * types * constr -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkLetIn : Name.t * constr * types * constr -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkApp : constr * constr array -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConst : Constant.t -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkProj : projection * constr -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkInd : inductive -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConstruct : constructor -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConstU : Constant.t puniverses -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkIndU : inductive puniverses -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConstructU : constructor puniverses -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConstructUi : (pinductive * int) -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkCase : case_info * constr * constr * constr array -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkFix : fixpoint -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkCoFix : cofixpoint -> constr
[@@ocaml.deprecated "Alias for Constr"]

(** {6 Aliases} *)

val eq_constr : constr -> constr -> bool
[@@ocaml.deprecated "Alias for Constr.equal"]

(** [eq_constr_univs u a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe constraints in [u]. *)
val eq_constr_univs : constr UGraph.check_function
[@@ocaml.deprecated "Alias for Constr.eq_constr_univs"]

(** [leq_constr_univs u a b] is [true] if [a] is convertible to [b] modulo 
    alpha, casts, application grouping and the universe constraints in [u]. *)
val leq_constr_univs : constr UGraph.check_function
[@@ocaml.deprecated "Alias for Constr.leq_constr_univs"]

(** [eq_constr_univs a b] [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping and ignoring universe instances. *)
val eq_constr_nounivs : constr -> constr -> bool
[@@ocaml.deprecated "Alias for Constr.qe_constr_nounivs"]

val kind_of_term : constr -> (constr, types, Sorts.t, Univ.Instance.t) kind_of_term
[@@ocaml.deprecated "Alias for Constr.kind"]

val compare : constr -> constr -> int
[@@ocaml.deprecated "Alias for [Constr.compare]"]

val constr_ord : constr -> constr -> int
[@@ocaml.deprecated "Alias for [Term.compare]"]

val fold_constr : ('a -> constr -> 'a) -> 'a -> constr -> 'a
[@@ocaml.deprecated "Alias for [Constr.fold]"]

val map_constr : (constr -> constr) -> constr -> constr
[@@ocaml.deprecated "Alias for [Constr.map]"]

val map_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr
[@@ocaml.deprecated "Alias for [Constr.map_with_binders]"]

val map_puniverses : ('a -> 'b) -> 'a puniverses -> 'b puniverses
val univ_of_sort : Sorts.t -> Univ.Universe.t
val sort_of_univ : Univ.Universe.t -> Sorts.t

val iter_constr : (constr -> unit) -> constr -> unit
[@@ocaml.deprecated "Alias for [Constr.iter]"]

val iter_constr_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit
[@@ocaml.deprecated "Alias for [Constr.iter_with_binders]"]

val compare_constr : (constr -> constr -> bool) -> constr -> constr -> bool
[@@ocaml.deprecated "Alias for [Constr.compare_head]"]

type constr = Constr.constr
[@@ocaml.deprecated "Alias for Constr.t"]

(** Alias types, for compatibility. *)

type types = Constr.types
[@@ocaml.deprecated "Alias for Constr.types"]

type contents = Sorts.contents = Pos | Null
[@@ocaml.deprecated "Alias for Sorts.contents"]

type sorts = Sorts.t =
  | Prop of Sorts.contents   (** Prop and Set *)
  | Type of Univ.Universe.t  (** Type *)
[@@ocaml.deprecated "Alias for Sorts.t"]

type sorts_family = Sorts.family = InProp | InSet | InType
[@@ocaml.deprecated "Alias for Sorts.family"]

type 'a puniverses = 'a Constr.puniverses
[@@ocaml.deprecated "Alias for Constr.puniverses"]

(** Simply type aliases *)
type pconstant = Constr.pconstant
[@@ocaml.deprecated "Alias for Constr.pconstant"]
type pinductive = Constr.pinductive
[@@ocaml.deprecated "Alias for Constr.pinductive"]
type pconstructor = Constr.pconstructor
[@@ocaml.deprecated "Alias for Constr.pconstructor"]
type existential_key = Constr.existential_key
[@@ocaml.deprecated "Alias for Constr.existential_key"]
type existential = Constr.existential
[@@ocaml.deprecated "Alias for Constr.existential"]
type metavariable = Constr.metavariable
[@@ocaml.deprecated "Alias for Constr.metavariable"]

type case_style = Constr.case_style =
  LetStyle | IfStyle | LetPatternStyle | MatchStyle | RegularStyle
[@@ocaml.deprecated "Alias for Constr.case_style"]

type case_printing = Constr.case_printing =
  { ind_tags : bool list; cstr_tags : bool list array; style : Constr.case_style }
[@@ocaml.deprecated "Alias for Constr.case_printing"]

type case_info = Constr.case_info =
  { ci_ind         : inductive;
    ci_npar        : int;
    ci_cstr_ndecls : int array;
    ci_cstr_nargs  : int array;
    ci_pp_info     : Constr.case_printing
  }
[@@ocaml.deprecated "Alias for Constr.case_info"]

type cast_kind = Constr.cast_kind =
  VMcast | NATIVEcast | DEFAULTcast | REVERTcast
[@@ocaml.deprecated "Alias for Constr.cast_kind"]

type rec_declaration = Constr.rec_declaration
[@@ocaml.deprecated "Alias for Constr.rec_declaration"]
type fixpoint = Constr.fixpoint
[@@ocaml.deprecated "Alias for Constr.fixpoint"]
type cofixpoint = Constr.cofixpoint
[@@ocaml.deprecated "Alias for Constr.cofixpoint"]
type 'constr pexistential = 'constr Constr.pexistential
[@@ocaml.deprecated "Alias for Constr.pexistential"]
type ('constr, 'types) prec_declaration =
  ('constr, 'types) Constr.prec_declaration
[@@ocaml.deprecated "Alias for Constr.prec_declaration"]
type ('constr, 'types) pfixpoint = ('constr, 'types) Constr.pfixpoint
[@@ocaml.deprecated "Alias for Constr.pfixpoint"]
type ('constr, 'types) pcofixpoint = ('constr, 'types) Constr.pcofixpoint
[@@ocaml.deprecated "Alias for Constr.pcofixpoint"]

type ('constr, 'types, 'sort, 'univs) kind_of_term =
  ('constr, 'types, 'sort, 'univs) Constr.kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of Constr.metavariable
  | Evar      of 'constr Constr.pexistential
  | Sort      of 'sort
  | Cast      of 'constr * Constr.cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of (Constant.t * 'univs)
  | Ind       of (inductive * 'univs)
  | Construct of (constructor * 'univs)
  | Case      of Constr.case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) Constr.pfixpoint
  | CoFix     of ('constr, 'types) Constr.pcofixpoint
  | Proj      of projection * 'constr
[@@ocaml.deprecated "Alias for Constr.kind_of_term"]

type values = Constr.values
[@@ocaml.deprecated "Alias for Constr.values"]

val hash_constr : Constr.constr -> int
[@@ocaml.deprecated "Alias for Constr.hash"]

val hcons_sorts : Sorts.t -> Sorts.t
[@@ocaml.deprecated "Alias for [Sorts.hcons]"]

val hcons_constr : Constr.constr -> Constr.constr
[@@ocaml.deprecated "Alias for [Constr.hcons]"]

val hcons_types : Constr.types -> Constr.types
[@@ocaml.deprecated "Alias for [Constr.hcons]"]
