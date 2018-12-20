# Notes on SProp

(ml API side, see refman for user side)

## Relevance

All kernel binders (`Prod`/`Lambda`/`LetIn`/`Context` elements) are
now annotated with a value in `type Sorts.relevance = Relevant |
Irrelevant`. It should verify that the binder's type lives in `SProp`
iff the annotation is `Irrelevant`.

As a plugin you can generally just use `Relevant` everywhere, the
kernel will fix it if needed when it checks the terms you produce. The
only issue is that if you generate `Relevant` when it should have been
`Irrelevant` you won't be able to use proof irrelevance on that
variable until the kernel fixes it. See refman for examples as Coq
also uses `Relevant` incorrectly in some places.

This annotation is done by transforming the binder name `'a` into a
`'a Context.binder_annot = { binder_name : 'a; binder_relevance :
Sorts.relevance }`, eg `Prod of Name.t * types * types` becomes `Prod
of Name.t Context.binder_annot * types * types`.

If you just carry binder names around without looking at them no
change is needed, eg if you have `match foo with Lambda (x, a, b) ->
Prod (x, a, type_of (push_rel (LocalAssum (x,a)) env) b)`. Otherwise
see `context.mli` for a few combinators on the `binder_annot` type.

When making `Relevant` annotations you can use some convenience
functions from `Context` (eg `annotR x = make_annot x Relevant`), also
`mkArrowR` from `Constr`/`EConstr` which has the signature of the old
`mkArrow`.

You can enable the debug warning `bad-relevance` to help find places
where you generate incorrect annotations.

Relevance can be inferred from a well-typed term using functions in
`Retypeops` (for `Constr`) and `Retyping` (for `EConstr`). For `x` a
term, note the difference between its relevance as a term (is `x :
(_ : SProp)`) and as a type (is `x : SProp`), there are functions for
both kinds.
