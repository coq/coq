Primitive Projections
---------------------

    | Proj of Projection.t * constr

Projections are always applied to a term, which must be of a record
type (i.e. reducible to an inductive type `I params`). Type-checking,
reduction and conversion are fast (not as fast as they could be yet)
because we don't keep parameters around. As you can see, it's
currently a `constant` that is used here to refer to the projection,
that will change to an abstract `projection` type in the future.
Basically a projection constant records which inductive it is a
projection for, the number of params and the actual position in the
constructor that must be projected. For compatibility reason, we also
define an eta-expanded form (accessible from user syntax `@f`). The
constant_entry of a projection has both informations. Declaring a
record (under `Set Primitive Projections`) will generate such
definitions. The API to declare them is not stable at the moment, but
the inductive type declaration also knows about the projections, i.e.
a record inductive type decl contains an array of terms representing
the projections. This is used to implement eta-conversion for record
types (with at least one field and having all projections definable).
The canonical value being `Build_R (pn x) ... (pn x)`. Unification and
conversion work up to this eta rule. The records can also be universe
polymorphic of course, and we don't need to keep track of the universe
instance for the projections either. Projections are reduced _eagerly_
everywhere, and introduce a new `Zproj` constructor in the abstract
machines that obeys both the delta (for the constant opacity) and iota
laws (for the actual reduction). Refolding works as well (afaict), but
there is a slight hack there related to universes (not projections).

For the ML programmer, the biggest change is that pattern-matchings on
kind_of_term require an additional case, that is handled usually
exactly like an `App (Const p) arg`.

There are slight hacks related to hints is well, to use the primitive
projection form of f when one does `Hint Resolve f`. Usually hint
resolve will typecheck the term, resulting in a partially applied
projection (disallowed), so we allow it to take
`constr_or_global_reference` arguments instead and special-case on
projections. Other tactic extensions might need similar treatment.
