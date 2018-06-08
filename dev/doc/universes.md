Notes on universe polymorphism
------------------------------

The implementation of universe polymorphism introduces a few changes
to the API of Coq. First and foremost, the term language changes, as
global references now carry a universe level substitution:

~~~ocaml
type 'a puniverses = 'a * Univ.Instance.t
type pconstant = constant puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

type constr = ...
  | Const of puniverses
  | Ind of pinductive
  | Constr of pconstructor
~~~

Universes
---------

Universe instances (an array of levels) gets substituted when
unfolding definitions, are used to typecheck and are unified according
to the rules in the ITP'14 paper on universe polymorphism in Coq.

~~~ocaml
type Level.t = Set | Prop | Level of int * dirpath (* hashconsed *)
type Instance.t = Level.t array
type Universe.t = Level.t list (* hashconsed *)
~~~

The universe module defines modules and abstract types for levels,
universes etc.. Structures are hashconsed (with a hack to take care
of the fact that deserialization breaks sharing).

  Definitions (constants, inductives) now carry around not only
constraints but also the universes they introduced (a Univ.UContext.t).
There is another kind of contexts `Univ.ContextSet.t`, the latter has
a set of universes, while the former has serialized the levels in an
array, and is used for polymorphic objects. Both have "reified"
constraints depending on global and local universes.

  A polymorphic definition is abstract w.r.t. the variables in this
context, while a monomorphic one (or template polymorphic) just adds the
universes and constraints to the global universe context when it is put
in the environment. No other universes than the global ones and the
declared local ones are needed to check a declaration, hence the kernel
does not produce any constraints anymore, apart from module
subtyping.... There are hence two conversion functions now: `check_conv`
and `infer_conv`: the former just checks the definition in the current env
(in which we usually push_universe_context of the associated context),
and `infer_conv` which produces constraints that were not implied by the
ambient constraints. Ideally, that one could be put out of the kernel,
but currently module subtyping needs it.

 Inference of universes is now done during refinement, and the evar_map
carries the incrementally built universe context, starting from the
global universe constraints (see `Evd.from_env`). `Evd.conversion` is a
wrapper around `infer_conv` that will do the bookkeeping for you, it
uses `evar_conv_x`. There is a universe substitution being built
incrementally according to the constraints, so one should normalize at
the end of a proof (or during a proof) with that substitution just like
we normalize evars. There are some nf_* functions in
library/universes.ml to do that. Additionally, there is a minimization
algorithm in there that can be applied at the end of a proof to simplify
the universe constraints used in the term. It is heuristic but
validity-preserving. No user-introduced universe (i.e. coming from a
user-written anonymous Type) gets touched by this, only the fresh
universes generated for each global application. Using
~~~ocaml
val pf_constr_of_global : Globnames.global_reference -> (constr -> tactic) -> tactic
~~~
Is the way to make a constr out of a global reference in the new API.
If they constr is polymorphic, it will add the necessary constraints to
the evar_map. Even if a constr is not polymorphic, we have to take care
of keeping track of its universes. Typically, using:
~~~ocaml
  mkApp (coq_id_function, [| A; a |])
~~~
and putting it in a proof term is not enough now. One has to somehow
show that A's type is in cumululativity relation with id's type
argument, incurring a universe constraint. To do this, one can simply
call Typing.resolve_evars env evdref c which will do some infer_conv to
produce the right constraints and put them in the evar_map. Of course in
some cases you might know from an invariant that no new constraint would
be produced and get rid of it. Anyway the kernel will tell you if you
forgot some. As a temporary way out, `Universes.constr_of_global` allows
you to make a constr from any non-polymorphic constant, but it will fail
on polymorphic ones.

Other than that, unification (w_unify and evarconv) now take account of universes and
produce only well-typed evar_maps.

Some syntactic comparisons like the one used in `change` have to be
adapted to allow identification up-to-universes (when dealing with
polymorphic references), `make_eq_univs_test` is there to help.
In constr, there are actually many new comparison functions to deal with
that:
~~~ocaml
(** [equal a b] is true if [a] equals [b] modulo alpha, casts,
   and application grouping *)
val equal : constr -> constr -> bool

(** [eq_constr_univs u a b] is [true] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [u]. *)
val eq_constr_univs : constr Univ.check_function

(** [leq_constr_univs u a b] is [true] if [a] is convertible to [b] modulo
    alpha, casts, application grouping and the universe inequalities in [u]. *)
val leq_constr_univs : constr Univ.check_function

(** [eq_constr_universes a b] [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping and the universe equalities in [c]. *)
val eq_constr_universes : constr -> constr -> bool Univ.universe_constrained

(** [leq_constr_universes a b] [true, c] if [a] is convertible to [b] modulo
    alpha, casts, application grouping and the universe inequalities in [c]. *)
val leq_constr_universes : constr -> constr -> bool Univ.universe_constrained

(** [eq_constr_univs a b] [true, c] if [a] equals [b] modulo alpha, casts,
   application grouping and ignoring universe instances. *)
val eq_constr_nounivs : constr -> constr -> bool
~~~
The `_univs` versions are doing checking of universe constraints
according to a graph, while the `_universes` are producing (non-atomic)
universe constraints. The non-atomic universe constraints include the
`ULub` constructor: when comparing `f (* u1 u2 *) c` and `f (* u1' u2'
*) c` we add ULub constraints on `u1, u1'` and `u2, u2'`. These are
treated specially: as unfolding `f` might not result in these
unifications, we need to keep track of the fact that failure to satisfy
them does not mean that the term are actually equal. This is used in
unification but probably not necessary to the average programmer.

Another issue for ML programmers is that tables of constrs now usually
need to take a `constr Univ.in_universe_context_set` instead, and
properly refresh the universes context when using the constr, e.g. using
Clenv.refresh_undefined_univs clenv or:
~~~ocaml
(** Get fresh variables for the universe context.
    Useful to make tactics that manipulate constrs in universe contexts polymorphic. *)
val fresh_universe_context_set_instance : universe_context_set ->
  universe_level_subst * universe_context_set
~~~
The substitution should be applied to the constr(s) under consideration,
and the context_set merged with the current evar_map with:
~~~ocaml
val merge_context_set : rigid -> evar_map -> Univ.universe_context_set -> evar_map
~~~
The `rigid` flag here should be `Evd.univ_flexible` most of the
time. This means the universe levels of polymorphic objects in the
constr might get instantiated instead of generating equality constraints
(Evd.univ_rigid does that).

On this issue, I recommend forcing commands to take `global_reference`s
only, the user can declare his specialized terms used as hints as
constants and this is cleaner. Alas, backward-compatibility-wise,
this is the only solution I found. In the case of global_references
only, it's just a matter of using `Evd.fresh_global` /
`pf_constr_of_global` to let the system take care of universes.


The universe graph
------------------

To accomodate universe polymorphic definitions, the graph structure in
kernel/univ.ml was modified. The new API forces every universe to be
declared before it is mentionned in any constraint. This forces to
declare every universe to be >= Set or > Set. Every universe variable
introduced during elaboration is >= Set. Every _global_ universe is now
declared explicitly > Set, _after_ typechecking the definition. In
polymorphic definitions Type@{i} ranges over Set and any other universe
j. However, at instantiation time for polymorphic references, one can
try to instantiate a universe parameter with Prop as well, if the
instantiated constraints allow it. The graph invariants ensure that
no universe i can be set lower than Set, so the chain of universes
always bottoms down at Prop < Set.

Modules
-------

One has to think of universes in modules as being globally declared, so
when including a module (type) which declares a type i (e.g. through a
parameter), we get back a copy of i and not some fresh universe.

Incompatibilities
-----------------

Old-style universe polymorphic definitions were implemented by taking
advantage of the fact that elaboration (i.e., pretyping and unification)
were _not_ universe aware, so some of the constraints generated during
pretypechecking would be forgotten. In the current setting, this is not
possible, as unification ensures that the substitution is built is
entirely well-typed, even w.r.t universes. This means that some terms
that type-checked before no longer do, especially projections of the
pair:
~~~coq
@fst ?x ?y : prod ?x ?y : Type (max(Datatypes.i, Datatypes.j)).
~~~
The "template universe polymorphic" variables i and j appear during
typing without being refreshed, meaning that they can be lowered (have
upper constraints) with user-introduced universes. In most cases this
won't work, so ?x and ?y have to be instantiated earlier, either from
the type of the actual projected pair term (some t : prod A B) or the
typing constraint. Adding the correct type annotations will always fix
this.


Unification semantics
---------------------

In Ltac, matching with:

- a universe polymorphic constant `c` matches any instance of the
  constant.
- a variable ?x already bound to a term `t` (non-linear pattern) uses
  strict equality of universes (e.g., Type@{i} and Type@{j} are not
  equal).

In tactics:

- `change foo with bar`, `pattern foo` will unify all instances of `foo`
  (and convert them with `bar`). This might incur unifications of
  universes. `change` uses conversion while `pattern` only does
  syntactic matching up-to unification of universes.
- `apply`, `refine` use unification up to universes.
