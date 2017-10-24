open Names
open Glob_term

(** {5 Maps of pattern variables} *)

(** Type [constr_under_binders] is for representing the term resulting
    of a matching. Matching can return terms defined in a some context
    of named binders; in the context, variable names are ordered by
    (<) and referred to by index in the term Thanks to the canonical
    ordering, a matching problem like

    [match ... with [(fun x y => ?p,fun y x => ?p)] => [forall x y => p]]

    will be accepted. Thanks to the reference by index, a matching
    problem like

    [match ... with [(fun x => ?p)] => [forall x => p]]

    will work even if [x] is also the name of an existing goal
    variable.

    Note: we do not keep types in the signature. Besides simplicity,
    the main reason is that it would force to close the signature over
    binders that occur only in the types of effective binders but not
    in the term itself (e.g. for a term [f x] with [f:A -> True] and
    [x:A]).

    On the opposite side, by not keeping the types, we loose
    opportunity to propagate type informations which otherwise would
    not be inferable, as e.g. when matching [forall x, x = 0] with
    pattern [forall x, ?h = 0] and using the solution "x|-h:=x" in
    expression [forall x, h = x] where nothing tells how the type of x
    could be inferred. We also loose the ability of typing ltac
    variables before calling the right-hand-side of ltac matching clauses. *)

type constr_under_binders = Id.t list * EConstr.constr

(** Types of substitutions with or w/o bound variables *)

type patvar_map = EConstr.constr Id.Map.t
type extended_patvar_map = constr_under_binders Id.Map.t

(** A globalised term together with a closure representing the value
    of its free variables. Intended for use when these variables are taken
    from the Ltac environment. *)
type closure = {
  idents:Id.t Id.Map.t;
  typed: constr_under_binders Id.Map.t ;
  untyped:closed_glob_constr Id.Map.t }
and closed_glob_constr = {
  closure: closure;
  term: glob_constr }

(** Ltac variable maps *)
type var_map = constr_under_binders Id.Map.t
type uconstr_var_map = closed_glob_constr Id.Map.t
type unbound_ltac_var_map = Geninterp.Val.t Id.Map.t

type ltac_var_map = {
  ltac_constrs : var_map;
  (** Ltac variables bound to constrs *)
  ltac_uconstrs : uconstr_var_map;
  (** Ltac variables bound to untyped constrs *)
  ltac_idents: Id.t Id.Map.t;
  (** Ltac variables bound to identifiers *)
  ltac_genargs : unbound_ltac_var_map;
  (** Ltac variables bound to other kinds of arguments *)
}
