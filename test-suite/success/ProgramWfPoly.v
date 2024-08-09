(* An example extracted by the minimizer from category-theory *)

Require Coq.FSets.FMaps.
Require Coq.Program.Program.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Declare Scope category_theory_scope.
Open Scope category_theory_scope.

Module Export Category_DOT_Lib_WRAPPED.
Module Export Lib.
#[export] Set Universe Polymorphism.
#[export] Set Uniform Inductive Parameters.
#[export] Unset Universe Minimization ToSet.

End Lib.

End Category_DOT_Lib_WRAPPED.
Module Export Category_DOT_Lib_DOT_FMapExt_WRAPPED.
Module Export FMapExt.
Import Coq.FSets.FMapFacts.

Module FMapExt (E : DecidableType) (M : WSfun E).

Module P := WProperties_fun E M.
Module F := P.F.

#[export] Hint Extern 5 =>
  match goal with
    [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
      apply F.empty_mapsto_iff in H; contradiction
  end : core.

End FMapExt.

End FMapExt.

End Category_DOT_Lib_DOT_FMapExt_WRAPPED.
Module Export Lib.
Module Export FMapExt.
Include Category_DOT_Lib_DOT_FMapExt_WRAPPED.FMapExt.
End FMapExt.

End Lib.
Import Coq.NArith.NArith.
Import Coq.FSets.FMaps.

Module PO := PairOrderedType N_as_OT N_as_OT.
Module M  := FMapList.Make(PO).
Module Import FMapExt := FMapExt PO M.

Inductive partial (P : Prop) : Set :=
| Proved : P -> partial
| Uncertain : partial.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

#[local] Open Scope partial_scope.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

Record environment : Set := {
  vars : positive -> N
}.

Inductive term : Set :=
  | Var   : positive -> term
  | Value : N -> term.

Program Definition term_eq_dec (x y : term) : {x = y} + {x <> y} :=
  match x, y with
  | Var x,   Var y   => if Pos.eq_dec x y then left _ else right _
  | Value x, Value y => if N.eq_dec   x y then left _ else right _
  | _, _ => right _
  end.
Definition subst_all {A} (f : A -> term -> term -> A) :
  A -> list (term * term) -> A.
exact (fold_right (fun '(v, v') rest => f rest v v')).
Defined.

Definition term_denote env (x : term) : N :=
  match x with
  | Var n => vars env n
  | Value n => n
  end.

Inductive map_expr : Set :=
  | Empty : map_expr
  | Add   : term -> term -> term -> map_expr -> map_expr.

Fixpoint map_expr_denote env (m : map_expr) : M.t N :=
  match m with
  | Empty => M.empty N
  | Add x y f m' => M.add (term_denote env x, term_denote env y)
                          (term_denote env  f) (map_expr_denote env m')
  end.

Inductive formula : Set :=
  | Top    : formula
  | Bottom : formula
  | Maps   : term -> term -> term -> map_expr -> formula
  | Impl   : formula -> formula -> formula.
Fixpoint subst_formula (t : formula) (v v' : term) : formula.
Admitted.

Fixpoint formula_denote env (t : formula) : Prop :=
  match t with
  | Top => True
  | Bottom => False
  | Maps x y f m =>
    M.MapsTo (term_denote env x, term_denote env y)
             (term_denote env f) (map_expr_denote env m)
  | Impl p q => formula_denote env p -> formula_denote env q
  end.
Fixpoint formula_size (t : formula) : nat.
Admitted.
Fixpoint substitutions (xs : list (term * term)) : list (term * term).
Admitted.
Fixpoint remove_conflicts (x y f : term) (m : map_expr) : map_expr.
Admitted.

Import ListNotations.

Program Definition formula_forward (t : formula) env (hyp : formula)
        (cont : forall env' defs,
            [formula_denote env' (subst_all subst_formula t defs)]) :
  [formula_denote env hyp -> formula_denote env t] :=
  match hyp with
  | Top => Reduce (cont env [])
  | Bottom => Yes
  | Maps x y f m =>
    let fix go n : [formula_denote env (Maps x y f n)
                    -> formula_denote env t] :=
        match n with
        | Empty => Yes
        | Add x' y' f' m' =>
          cont env (substitutions [(x, x'); (y, y'); (f, f')]) && go m'
        end in Reduce (go (remove_conflicts x y f m))
  | Impl _ _ => Reduce (cont env [])
  end.
Next Obligation.
Admitted.
Next Obligation.
admit.
Defined.
Admit Obligations.

Fixpoint map_contains env (x y : N) (m : map_expr) : option term :=
  match m with
  | Empty => None
  | Add x' y' f' m' =>
    if (N.eqb x (term_denote env x') &&
        N.eqb y (term_denote env y'))%bool
    then Some f'
    else map_contains env x y m'
  end.

Program Fixpoint formula_backward (t : formula) env {measure (formula_size t)} :
  [formula_denote env t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Maps x y f m =>
    match map_contains env (term_denote env x) (term_denote env y) m with
    | Some f' => Reduce (term_eq_dec f' f)
    | None => No
    end
  | Impl p q =>
    formula_forward q env p
      (fun env' defs' => formula_backward (subst_all subst_formula q defs') env')
  end.
Admit Obligations. (* used to raise a universe instance length mismatch *)
