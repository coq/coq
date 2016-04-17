Unset Elimination Schemes.

(** System F *)

(** Term variable contexts *)
Inductive TmCtx :=
(** Empty term context *)
| tc_nil : TmCtx
(** Extended term context *)
| tc_cons (Delta : TyCtx) (Gamma : TmCtx) : Ty Delta -> TmCtx

(** Type variable contexts, essentially just nat *)
with TyCtx :=
(** Empty type context *)
| tyc_nil : TyCtx
(** Extended type context *)
| tyc_cons : TyCtx -> TyCtx

(** Well-typed polymorphic types *)
with Ty : TyCtx -> Type :=
(** Type variables *)
| ty_var (Delta : TyCtx) : Ty (tyc_cons Delta)
(** Arrow type *)
| ty_arr (Delta : TyCtx) : Ty Delta -> Ty Delta -> Ty Delta
(** Polymorphic type (forall) *)
| ty_all (Delta : TyCtx)
  : Ty (tyc_cons Delta) -> Ty Delta

(** Well-typed terms *)
with Tm : forall (Delta : TyCtx), TmCtx -> Ty Delta -> Type :=
(** Term variable *)
| tm_var (Delta : TyCtx) (Gamma : TmCtx) (T : Ty Delta)
  : Tm Delta (tc_cons Delta Gamma T) T
(** Lambda abstraction for terms *)
| tm_lam (Delta : TyCtx) (Gamma : TmCtx) (T1 T2 : Ty Delta)
    (e : Tm Delta (tc_cons Delta Gamma T1) T2)
  : Tm Delta Gamma (ty_arr Delta T1 T2)
(** Application of term of arrow type *)
| tm_app (Delta : TyCtx) (Gamma : TmCtx) (T1 T2 : Ty Delta)
    (e1 : Tm Delta Gamma (ty_arr Delta T1 T2)) (e2 : Tm Delta Gamma T1)
  : Tm Delta Gamma T2
(** Lambda abstraction for types *)
| tm_Lam (Delta : TyCtx) (Gamma : TmCtx) (T : Ty (tyc_cons Delta))
    (e : Tm (tyc_cons Delta) Gamma T)
  : Tm Delta Gamma (ty_all Delta T)
(** There is one more rule for application of polymorphic functions, however this requires subsitutiting free type variables. Defining a subsitution for free type variables however would make this definition inductive-inductive-recursive which we currently cannot do. *)
.

Scheme tmctx_elim := Induction for TmCtx Sort Type
with tyctx_elim := Induction for TyCtx Sort Type
with ty_elim := Induction for Ty Sort Type
with tm_elim := Induction for Tm Sort Type.
