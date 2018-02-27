(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** {5 Redeclaration of types from module Constr and Sorts}

    This reexports constructors of inductive types defined in module [Constr],
    for compatibility purposes. Refer to this module for further info.

*)

exception DestKO
[@@ocaml.deprecated "Alias for [Constr.DestKO]"]

(** {5 Simple term case analysis. } *)
val isRel  : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isRel]"]
val isRelN : int -> constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isRelN]"]
val isVar  : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isVar]"]
val isVarId : Id.t -> constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isVarId]"]
val isInd  : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isInd]"]
val isEvar : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isEvar]"]
val isMeta : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isMeta]"]
val isEvar_or_Meta : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isEvar_or_Meta]"]
val isSort : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isSort]"]
val isCast : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isCast]"]
val isApp : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isApp]"]
val isLambda : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isLambda]"]
val isLetIn : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isletIn]"]
val isProd : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isProp]"]
val isConst : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isConst]"]
val isConstruct : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isConstruct]"]
val isFix : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isFix]"]
val isCoFix : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isCoFix]"]
val isCase : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isCase]"]
val isProj : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isProj]"]

val is_Prop : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.is_Prop]"]
val is_Set  : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.is_Set]"]
val isprop : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.isprop]"]
val is_Type : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.is_Type]"]
val iskind : constr -> bool
[@@ocaml.deprecated "Alias for [Constr.is_kind]"]
val is_small : Sorts.t -> bool
[@@ocaml.deprecated "Alias for [Constr.is_small]"]


(** {5 Term destructors } *)
(** Destructor operations are partial functions and
    @raise DestKO if the term has not the expected form. *)

(** Destructs a de Bruijn index *)
val destRel : constr -> int
[@@ocaml.deprecated "Alias for [Constr.destRel]"]

(** Destructs an existential variable *)
val destMeta : constr -> metavariable
[@@ocaml.deprecated "Alias for [Constr.destMeta]"]

(** Destructs a variable *)
val destVar : constr -> Id.t
[@@ocaml.deprecated "Alias for [Constr.destVar]"]

(** Destructs a sort. [is_Prop] recognizes the sort {% \textsf{%}Prop{% }%}, whether
   [isprop] recognizes both {% \textsf{%}Prop{% }%} and {% \textsf{%}Set{% }%}. *)
val destSort : constr -> Sorts.t
[@@ocaml.deprecated "Alias for [Constr.destSort]"]

(** Destructs a casted term *)
val destCast : constr -> constr * cast_kind * constr
[@@ocaml.deprecated "Alias for [Constr.destCast]"]

(** Destructs the product {% $ %}(x:t_1)t_2{% $ %} *)
val destProd : types -> Name.t * types * types
[@@ocaml.deprecated "Alias for [Constr.destProd]"]

(** Destructs the abstraction {% $ %}[x:t_1]t_2{% $ %} *)
val destLambda : constr -> Name.t * types * constr
[@@ocaml.deprecated "Alias for [Constr.destLambda]"]

(** Destructs the let {% $ %}[x:=b:t_1]t_2{% $ %} *)
val destLetIn : constr -> Name.t * constr * types * constr
[@@ocaml.deprecated "Alias for [Constr.destLetIn]"]

(** Destructs an application *)
val destApp : constr -> constr * constr array
[@@ocaml.deprecated "Alias for [Constr.destApp]"]

(** Obsolete synonym of destApp *)
val destApplication : constr -> constr * constr array
[@@ocaml.deprecated "Alias for [Constr.destApplication]"]

(** Decompose any term as an applicative term; the list of args can be empty *)
val decompose_app : constr -> constr * constr list
[@@ocaml.deprecated "Alias for [Constr.decompose_app]"]

(** Same as [decompose_app], but returns an array. *)
val decompose_appvect : constr -> constr * constr array
[@@ocaml.deprecated "Alias for [Constr.decompose_appvect]"]

(** Destructs a constant *)
val destConst : constr -> Constant.t Univ.puniverses
[@@ocaml.deprecated "Alias for [Constr.destConst]"]

(** Destructs an existential variable *)
val destEvar : constr -> existential
[@@ocaml.deprecated "Alias for [Constr.destEvar]"]

(** Destructs a (co)inductive type *)
val destInd : constr -> inductive Univ.puniverses
[@@ocaml.deprecated "Alias for [Constr.destInd]"]

(** Destructs a constructor *)
val destConstruct : constr -> constructor Univ.puniverses
[@@ocaml.deprecated "Alias for [Constr.destConstruct]"]

(** Destructs a [match c as x in I args return P with ... |
Ci(...yij...) => ti | ... end] (or [let (..y1i..) := c as x in I args
return P in t1], or [if c then t1 else t2])
@return [(info,c,fun args x => P,[|...|fun yij => ti| ...|])]
where [info] is pretty-printing information *)
val destCase : constr -> case_info * constr * constr * constr array
[@@ocaml.deprecated "Alias for [Constr.destCase]"]

(** Destructs a projection *)
val destProj : constr -> projection * constr
[@@ocaml.deprecated "Alias for [Constr.destProj]"]

(** Destructs the {% $ %}i{% $ %}th function of the block
   [Fixpoint f{_ 1} ctx{_ 1} = b{_ 1}
    with    f{_ 2} ctx{_ 2} = b{_ 2}
    ...
    with    f{_ n} ctx{_ n} = b{_ n}],
   where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
*)
val destFix : constr -> fixpoint
[@@ocaml.deprecated "Alias for [Constr.destFix]"]

val destCoFix : constr -> cofixpoint
[@@ocaml.deprecated "Alias for [Constr.destCoFix]"]

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
    form [λΓ.c] with [Γ] of length [n] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val lambda_applist_assum : int -> constr -> constr list -> constr
val lambda_appvect_assum : int -> constr -> constr array -> constr

(** pseudo-reduction rule *)

(** [prod_appvect] [forall (x1:B1;...;xn:Bn), B] [a1...an] @return [B[a1...an]] *)
val prod_appvect : types -> constr array -> types
val prod_applist : types -> constr list -> types

(** In [prod_appvect_assum n c args], [c] is supposed to have the
    form [∀Γ.c] with [Γ] of length [n] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val prod_appvect_assum : int -> types -> constr array -> types
val prod_applist_assum : int -> types -> constr list -> types

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
val mkConstU : Constant.t Univ.puniverses -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkIndU : inductive Univ.puniverses -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConstructU : constructor Univ.puniverses -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkConstructUi : (pinductive * int) -> constr
[@@ocaml.deprecated "Alias for Constr"]
val mkCase : case_info * constr * constr * constr array -> constr
[@@ocaml.deprecated "Alias for Constr.mkCase"]
val mkFix : fixpoint -> constr
[@@ocaml.deprecated "Alias for Constr.mkFix"]
val mkCoFix : cofixpoint -> constr
[@@ocaml.deprecated "Alias for Constr.mkCoFix"]

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

val map_puniverses : ('a -> 'b) -> 'a Univ.puniverses -> 'b Univ.puniverses
[@@ocaml.deprecated "Alias for [Constr.map_puniverses]"]
val univ_of_sort : Sorts.t -> Univ.Universe.t
[@@ocaml.deprecated "Alias for [Sorts.univ_of_sort]"]
val sort_of_univ : Univ.Universe.t -> Sorts.t
[@@ocaml.deprecated "Alias for [Sorts.sort_of_univ]"]

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

type 'a puniverses = 'a Univ.puniverses
[@@ocaml.deprecated "Alias for Constr.puniverses"]

(** Simply type aliases *)
type pconstant = Constr.pconstant
[@@ocaml.deprecated "Alias for Constr.pconstant"]
type pinductive = Constr.pinductive
[@@ocaml.deprecated "Alias for Constr.pinductive"]
type pconstructor = Constr.pconstructor
[@@ocaml.deprecated "Alias for Constr.pconstructor"]
type existential_key = Evar.t
[@@ocaml.deprecated "Alias for Evar.t"]
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

type values = Vmvalues.values
[@@ocaml.deprecated "Alias for Vmvalues.values"]

val hash_constr : Constr.constr -> int
[@@ocaml.deprecated "Alias for Constr.hash"]

val hcons_sorts : Sorts.t -> Sorts.t
[@@ocaml.deprecated "Alias for [Sorts.hcons]"]

val hcons_constr : Constr.constr -> Constr.constr
[@@ocaml.deprecated "Alias for [Constr.hcons]"]

val hcons_types : Constr.types -> Constr.types
[@@ocaml.deprecated "Alias for [Constr.hcons]"]
