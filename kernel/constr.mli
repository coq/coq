(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** {6 Value under universe substitution } *)
type 'a puniverses = 'a Univ.puniverses

(** {6 Simply type aliases } *)
type pconstant = constant puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

(** {6 Existential variables } *)
type existential_key = Evar.t

(** {6 Existential variables } *)
type metavariable = int

(** {6 Case annotation } *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle 
  | RegularStyle (** infer printing form from number of constructor *)
type case_printing =
  { ind_tags : bool list; (** tell whether letin or lambda in the arity of the inductive type *)
    cstr_tags : bool list array; (** tell whether letin or lambda in the signature of each constructor *)
    style     : case_style }

(** the integer is the number of real args, needed for reduction *)
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (* number of pattern vars of each constructor (with let's)*)
    ci_cstr_nargs : int array; (* number of pattern vars of each constructor (w/o let's) *)
    ci_pp_info    : case_printing (** not interpreted by the kernel *)
  }

(** {6 The type of constructions } *)

type t
type constr = t
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
val mkVar : Id.t -> constr

(** Constructs an patvar named "?n" *)
val mkMeta : metavariable -> constr

(** Constructs an existential variable *)
type existential = existential_key * constr array
val mkEvar : existential -> constr

(** Construct a sort *)
val mkSort : Sorts.t -> types
val mkProp : types
val mkSet  : types
val mkType : Univ.universe -> types


(** This defines the strategy to use for verifiying a Cast *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast | REVERTcast

(** Constructs the term [t1::t2], i.e. the term t{_ 1} casted with the
   type t{_ 2} (that means t2 is declared as the type of t1). *)
val mkCast : constr * cast_kind * constr -> constr

(** Constructs the product [(x:t1)t2] *)
val mkProd : Name.t * types * types -> types

(** Constructs the abstraction \[x:t{_ 1}\]t{_ 2} *)
val mkLambda : Name.t * types * constr -> constr

(** Constructs the product [let x = t1 : t2 in t3] *)
val mkLetIn : Name.t * constr * types * constr -> constr

(** [mkApp (f,[| t_1; ...; t_n |]] constructs the application
   {% $(f~t_1~\dots~t_n)$ %}. *)
val mkApp : constr * constr array -> constr

val map_puniverses : ('a -> 'b) -> 'a puniverses -> 'b puniverses

(** Constructs a constant *)
val mkConst : constant -> constr
val mkConstU : pconstant -> constr

(** Constructs a projection application *)
val mkProj : (projection * constr) -> constr

(** Inductive types *)

(** Constructs the ith (co)inductive type of the block named kn *)
val mkInd : inductive -> constr
val mkIndU : pinductive -> constr

(** Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. *)
val mkConstruct : constructor -> constr
val mkConstructU : pconstructor -> constr
val mkConstructUi : pinductive * int -> constr

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
type rec_declaration = Name.t array * types array * constr array
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


(** {6 Concrete type for making pattern-matching. } *)

(** [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type ('constr, 'types) prec_declaration =
    Name.t array * 'types array * 'constr array
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration

type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of Sorts.t
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant puniverses
  | Ind       of inductive puniverses
  | Construct of constructor puniverses
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of projection * 'constr

(** User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

val kind : constr -> (constr, types) kind_of_term

(** [equal a b] is true if [a] equals [b] modulo alpha, casts,
   and application grouping *)
val equal : constr -> constr -> bool

(** [eq_constr_univs u a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [u]. *)
val eq_constr_univs : constr Univ.check_function

(** [leq_constr_univs u a b] is [true] if [a] is convertible to [b] modulo 
    alpha, casts, application grouping and the universe inequalities in [u]. *)
val leq_constr_univs : constr Univ.check_function

(** [eq_constr_univs u a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [u]. *)
val eq_constr_univs_infer : Univ.universes -> constr -> constr -> bool Univ.constrained

(** [leq_constr_univs u a b] is [true] if [a] is convertible to [b] modulo 
    alpha, casts, application grouping and the universe inequalities in [u]. *)
val leq_constr_univs_infer : Univ.universes -> constr -> constr -> bool Univ.constrained

(** [eq_constr_univs a b] [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping and ignoring universe instances. *)
val eq_constr_nounivs : constr -> constr -> bool

(** Total ordering compatible with [equal] *)
val compare : constr -> constr -> int

(** {6 Functionals working on the immediate subterm of a construction } *)

(** [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

val fold : ('a -> constr -> 'a) -> 'a -> constr -> 'a

(** [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val map : (constr -> constr) -> constr -> constr

(** Like {!map}, but also has an additional accumulator. *)

val fold_map : ('a -> constr -> 'a * constr) -> 'a -> constr -> 'a * constr

(** [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val map_with_binders :
  ('a -> 'a) -> ('a -> constr -> constr) -> 'a -> constr -> constr

(** [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

val iter : (constr -> unit) -> constr -> unit

(** [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

val iter_with_binders :
  ('a -> 'a) -> ('a -> constr -> unit) -> 'a -> constr -> unit

(** [compare_head f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's, binders
   name and Cases annotations are not taken into account *)

val compare_head : (constr -> constr -> bool) -> constr -> constr -> bool

(** [compare_head_gen u s f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed, [u] to compare universe
   instances (the first boolean tells if they belong to a constant), [s] to 
   compare sorts; Cast's, binders name and Cases annotations are not taken 
    into account *)

val compare_head_gen : (bool -> Univ.Instance.t -> Univ.Instance.t -> bool) ->
  (Sorts.t -> Sorts.t -> bool) ->
  (constr -> constr -> bool) ->
  constr -> constr -> bool

(** [compare_head_gen_leq u s sle f fle c1 c2] compare [c1] and [c2]
    using [f] to compare the immediate subterms of [c1] of [c2] for
    conversion, [fle] for cumulativity, [u] to compare universe
    instances (the first boolean tells if they belong to a constant),
    [s] to compare sorts for equality and [sle] for subtyping; Cast's,
    binders name and Cases annotations are not taken into account *)

val compare_head_gen_leq : (bool -> Univ.Instance.t -> Univ.Instance.t -> bool) ->
  (Sorts.t -> Sorts.t -> bool) ->
  (Sorts.t -> Sorts.t -> bool) ->
  (constr -> constr -> bool) ->
  (constr -> constr -> bool) ->
  constr -> constr -> bool
  
(** {6 Hashconsing} *)

val hash : constr -> int
val case_info_hash : case_info -> int

(*********************************************************************)

val hcons : constr -> constr

(**************************************)

type values
