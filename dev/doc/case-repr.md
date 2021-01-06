## Case representation

Starting from Coq 8.14, the term representation of pattern-matching uses a
so-called *compact form*. Compared to the previous representation, the major
difference is that all type and term annotations on lambda and let abstractions
that were present in branches and return clause of pattern-matchings were
removed. In order to keep the ability to construct the old expanded form out of
the new compact form, the case node also makes explicit data that was stealthily
present in the expanded return clause, namely universe instances and parameters
of the inductive type being eliminated.

### ML Representation

The case node now looks like
```
Case of
  case_info *
  Instance.t * (* universe instances of the inductive *)
  constr array * (* parameters of the inductive *)
  case_return * (* erased return clause *)
  case_invert * (* SProp inversion data *)
  constr * (* scrutinee *)
  case_branch array (* erased branches *)
```
where
```
type case_branch = Name.t binder_annot array * constr
type case_return = Name.t binder_annot array * types
```

For comparison, pre-8.14 case nodes were defined as follows.
```
Case of
  case_info *
  constr * (* annotated return clause *)
  case_invert * (* SProp inversion data *)
  constr * (* scrutinee *)
  constr array (* annotated branches *)
```

### Typing Rules and Invariants

Disregarding the `case_info` cache and the SProp inversion, the typing rules for
the case node can be given as follows.

Provided
- Γ ⊢ c : Ind@{u} pms Indices
- Inductive Ind@{i} Δ : forall Θ, Type := cᵢ : forall Ξᵢ, Ind Δ Aᵢ
- Γ, Θ@{i := u}{Δ := pms} ⊢ p : Type
- Γ, Ξᵢ@{i := u}{Δ := pms} ⊢ snd brᵢ : p{Θ := Aᵢ{Δ := pms}}

Then Γ ⊢ Case (_, u, pms, ( _, p), _, c, br) : p{Θ := Indices}

In particular, this implies that Γ ⊢ pms : Δ@{i := u}. Parameters are stored in
the same order as in the application node.

The u universe instance must be a valid instance for the corresponding
inductive type, in particular their length must coincide.

The `Name.t binder_annot array` appearing both in the return clause and
in the branches must satisfy these invariants:
- For branches, it must have the same length as the corresponding Ξᵢ context
(including let-ins)
- For the return clause, it must have the same length as the context
Θ, self : Ind@{u} pms Θ (including let-ins). The last variable appears as
the term being destructed and corresponds to the variable introduced by the
"as" clause of the user-facing syntax.
- The relevance annotations must match with the corresponding sort of the
variable from the context.

Note that the annotated variable array is reversed w.r.t. the context,
i.e. variables appear left to right as in standard practice.

Let-bindings can appear in Δ, Θ or Ξᵢ, since they are arbitrary
contexts. As a general rule, let bindings appear as binders but not as
instances. That is, they MUST appear in the variable array, but they MUST NOT
appear in the parameter array.

Example:
```
Inductive foo (X := tt) : forall (Y := X), Type := Foo : forall (Z := X), foo.

Definition case (x : foo) : unit := match x as x₀ in foo with Foo _ z => z end
```
The case node of the `case` function is represented as
```
Case (
  _,
  Instance.empty,
  [||],
  ([|(Y, Relevant); (x₀, Relevant)|], unit), (* let (Y := tt) in fun (x₀ : foo) => unit *)
  NoInvert,
  #1,
  [|
    ([|(z, Relevant)|], #1) (* let z := tt in z *)
  |]
)
```

This choice of representation for let-bindings requires access to the
environment in some cases, e.g. to compute branch reduction. There is a
fast-path for non-let-containing inductive types though, which are the vast
majority.

### Porting plugins

The conversion functions from and to the expanded form are:
- `[Inductive, EConstr].expand_case` which goes from the compact to the expanded
form and cannot fail (assuming the term was well-typed)
- `[Inductive, EConstr].contract_case` which goes the other way and will
raise anomalies if the expanded forms are not fully eta-expanded.

As such, it is always painless to convert to the old representation. Converting
the other way, you must ensure that all the terms you provide the
compatibility function with are fully eta-expanded, **including let-bindings**.
This works as expected for the common case with eta-expanded branches but will
fail for plugins that generate non-eta-expanded branches.

Some other useful variants of these functions are:
- `Inductive.expand_case_specif`
- `EConstr.annotate_case`
- `EConstr.expand_branch`
