(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** {5 Derived constructors} *)

(** non-dependent product [t1 -> t2], an alias for
   [forall (_:t1), t2]. Beware [t_2] is NOT lifted.
   Eg: in context [A:Prop], [A->A] is built by [(mkArrow (mkRel 1) (mkRel 2))]
*)
val mkArrow : types -> Sorts.relevance -> types -> constr

val mkArrowR : types -> types -> constr
(** For an always-relevant domain *)

(** Named version of the functions from [Term]. *)
val mkNamedLambda : Id.t binder_annot -> types -> constr -> constr
val mkNamedLetIn : Id.t binder_annot -> constr -> types -> constr -> constr
val mkNamedProd : Id.t binder_annot -> types -> types -> types

(** Constructs either [(x:t)c] or [[x=b:t]c] *)
val mkProd_or_LetIn : Constr.rel_declaration -> types -> types
val mkProd_wo_LetIn : Constr.rel_declaration -> types -> types
val mkNamedProd_or_LetIn : Constr.named_declaration -> types -> types
val mkNamedProd_wo_LetIn : Constr.named_declaration -> types -> types

(** Constructs either [[x:t]c] or [[x=b:t]c] *)
val mkLambda_or_LetIn : Constr.rel_declaration -> constr -> constr
val mkNamedLambda_or_LetIn : Constr.named_declaration -> constr -> constr

(** {5 Other term constructors. } *)

(** [applist (f,args)] and its variants work as [mkApp] *)

val applist : constr * constr list -> constr
val applistc : constr -> constr list -> constr
val appvect : constr * constr array -> constr
val appvectc : constr -> constr array -> constr

(** [prodn n l b] = [forall (x_1:T_1)...(x_n:T_n), b]
   where [l] is [(x_n,T_n)...(x_1,T_1)...]. *)
val prodn : int -> (Name.t binder_annot * constr) list -> constr -> constr

(** [compose_prod l b]
   @return [forall (x_1:T_1)...(x_n:T_n), b]
   where [l] is [(x_n,T_n)...(x_1,T_1)].
   Inverse of [decompose_prod]. *)
val compose_prod : (Name.t binder_annot * constr) list -> constr -> constr

(** [lamn n l b]
    @return [fun (x_1:T_1)...(x_n:T_n) => b]
   where [l] is [(x_n,T_n)...(x_1,T_1)...]. *)
val lamn : int -> (Name.t binder_annot * constr) list -> constr -> constr

(** [compose_lam l b]
   @return [fun (x_1:T_1)...(x_n:T_n) => b]
   where [l] is [(x_n,T_n)...(x_1,T_1)].
   Inverse of [it_destLam] *)
val compose_lam : (Name.t binder_annot * constr) list -> constr -> constr

(** [to_lambda n l]
   @return [fun (x_1:T_1)...(x_n:T_n) => T]
   where [l] is [forall (x_1:T_1)...(x_n:T_n), T] *)
val to_lambda : int -> constr -> constr

(** [to_prod n l]
   @return [forall (x_1:T_1)...(x_n:T_n), T]
   where [l] is [fun (x_1:T_1)...(x_n:T_n) => T] *)
val to_prod : int -> constr -> constr

val it_mkLambda_or_LetIn : constr -> Constr.rel_context -> constr
val it_mkProd_wo_LetIn : types -> Constr.rel_context -> types
val it_mkProd_or_LetIn : types -> Constr.rel_context -> types

(** In [lambda_applist c args], [c] is supposed to have the form
    [λΓ.c] with [Γ] without let-in; it returns [c] with the variables
    of [Γ] instantiated by [args]. *)
val lambda_applist : constr -> constr list -> constr
val lambda_appvect : constr -> constr array -> constr

(** In [lambda_applist_decls n c args], [c] is supposed to have the
    form [λΓ.c] with [Γ] of length [n] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val lambda_applist_decls : int -> constr -> constr list -> constr
val lambda_appvect_decls : int -> constr -> constr array -> constr

(** pseudo-reduction rule *)

(** [prod_appvect] [forall (x1:B1;...;xn:Bn), B] [a1...an]
    @return [B[a1...an]] *)
val prod_appvect : types -> constr array -> types
val prod_applist : types -> constr list -> types

(** In [prod_appvect_decls n c args], [c] is supposed to have the
    form [∀Γ.c] with [Γ] of length [n] and possibly with let-ins; it
    returns [c] with the assumptions of [Γ] instantiated by [args] and
    the local definitions of [Γ] expanded. *)
val prod_appvect_decls : int -> types -> constr array -> types
val prod_applist_decls : int -> types -> constr list -> types

(** {5 Other term destructors. } *)

(** Transforms a product term {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a product. *)
val decompose_prod : constr -> (Name.t binder_annot * constr) list * constr

(** Transforms a lambda term {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair
   {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}, where {% $ %}T{% $ %} is not a lambda. *)
val decompose_lambda : constr -> (Name.t binder_annot * constr) list * constr

(** Given a positive integer n, decompose a product term
   {% $ %}(x_1:T_1)..(x_n:T_n)T{% $ %}
   into the pair {% $ %}([(xn,Tn);...;(x1,T1)],T){% $ %}.
   Raise a user error if not enough products. *)
val decompose_prod_n : int -> constr -> (Name.t binder_annot * constr) list * constr

(** Given a positive integer {% $ %}n{% $ %}, decompose a lambda term
   {% $ %}[x_1:T_1]..[x_n:T_n]T{% $ %} into the pair {% $ %}([(x_n,T_n);...;(x_1,T_1)],T){% $ %}.
   Raise a user error if not enough lambdas. *)
val decompose_lambda_n : int -> constr -> (Name.t binder_annot * constr) list * constr

(** Extract the premisses and the conclusion of a term of the form
   "(xi:Ti) ... (xj:=cj:Tj) ..., T" where T is not a product nor a let *)
val decompose_prod_decls : types -> Constr.rel_context * types

(** Idem with lambda's and let's *)
val decompose_lambda_decls : constr -> Constr.rel_context * constr

(** Idem but extract the first [n] premisses, counting let-ins. *)
val decompose_prod_n_decls : int -> types -> Constr.rel_context * types

(** Idem but extracting simultaneously the first [n] premisses, counting let-ins, in a term and its type. *)
val decompose_lambda_prod_n_decls : int -> constr -> types -> Constr.rel_context * constr * types

(** Idem for lambdas, including let-ins but _not_ counting them;
    This is typically the function to use to extract the context of a Fix
    up to and including the decreasing argument, counting as many lambda's
    as given by the decreasing index + 1 *)
val decompose_lambda_n_assum : int -> constr -> Constr.rel_context * constr

(** Idem, counting let-ins *)
val decompose_lambda_n_decls : int -> constr -> Constr.rel_context * constr

(** Return the premisses/parameters of a type/term (let-in included) *)
val prod_decls : types -> Constr.rel_context
val lambda_decls : constr -> Constr.rel_context

(** Return the first n-th premisses/parameters of a type (let included and counted) *)
val prod_n_decls : int -> types -> Constr.rel_context

(** Return the first n-th premisses/parameters of a term (let included but not counted) *)
val lam_n_assum : int -> constr -> Constr.rel_context

(** Remove the premisses/parameters of a type/term *)
val strip_prod : types -> types
val strip_lam : constr -> constr

(** Remove the first n-th premisses/parameters of a type/term *)
val strip_prod_n : int -> types -> types
val strip_lam_n : int -> constr -> constr

(** Remove the premisses/parameters of a type/term (including let-in) *)
val strip_prod_decls : types -> types
val strip_lambda_decls : constr -> constr

(** {5 ... } *)
(** An "arity" is a term of the form [[x1:T1]...[xn:Tn]s] with [s] a sort.
    Such a term can canonically be seen as the pair of a context of types
    and of a sort *)

type arity = Constr.rel_context * Sorts.t

(** Build an "arity" from its canonical form *)
val mkArity : arity -> types

(** Destruct an "arity" into its canonical form *)
val destArity : types -> arity

(** Tell if a term has the form of an arity *)
val isArity : types -> bool

(* Deprecated *)
type sorts_family = Sorts.family = InSProp | InProp | InSet | InType | InQSort
[@@ocaml.deprecated "(8.8) Alias for Sorts.family"]

type sorts = Sorts.t = private
  | SProp | Prop | Set
  | Type of Univ.Universe.t  (** Type *)
  | QSort of Sorts.QVar.t * Univ.Universe.t
[@@ocaml.deprecated "(8.8) Alias for Sorts.t"]

val decompose_prod_assum : types -> Constr.rel_context * types
[@@ocaml.deprecated "(8.18) Use [decompose_prod_decls] instead."]
val decompose_lam_assum : constr -> Constr.rel_context * constr
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_decls] instead."]
val decompose_prod_n_assum : int -> types -> Constr.rel_context * types
[@@ocaml.deprecated "(8.18) Use [decompose_prod_n_decls] instead."]
val prod_assum : types -> Constr.rel_context
[@@ocaml.deprecated "(8.18) Use [prod_decls] instead."]
val lam_assum : constr -> Constr.rel_context
[@@ocaml.deprecated "(8.18) Use [lambda_decls] instead."]
val prod_n_assum : int -> types -> Constr.rel_context
[@@ocaml.deprecated "(8.18) Use [prod_n_decls] instead."]
val strip_prod_assum : types -> types
[@@ocaml.deprecated "(8.18) Use [strip_prod_decls] instead."]
val strip_lam_assum : constr -> constr
[@@ocaml.deprecated "(8.18) Use [strip_lambda_decls] instead."]

val decompose_lam : t -> (Name.t binder_annot * t) list * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda] instead."]
val decompose_lam_n : int -> t -> (Name.t binder_annot * t) list * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_n] instead."]
val decompose_lam_n_assum : int -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_n_assum] instead."]
val decompose_lam_n_decls : int -> t -> rel_context * t
[@@ocaml.deprecated "(8.18) Use [decompose_lambda_n_decls] instead."]
