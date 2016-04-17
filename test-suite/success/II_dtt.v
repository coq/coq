Module WithElim.

Inductive Ctx : Type :=
| emp_ctx : Ctx
| ctx_ext : forall Γ,  Ty Γ -> Ctx

with Ty : Ctx -> Type :=
| subst_ty : forall {Γ Δ}, Ty Δ -> Sub Γ Δ -> Ty Γ
| U : forall {Γ}, Ty Γ
| El : forall {Γ : Ctx}, Tm Γ U -> Ty Γ
| Pi : forall {Γ} (A : Ty Γ) (B : Ty (ctx_ext Γ A)), Ty Γ

with Sub : Ctx -> Ctx -> Type :=
| emp_sub : forall {Γ}, Sub Γ emp_ctx
| sub_ext : forall {Γ Δ} (δ : Sub Γ Δ) {A : Ty Δ} (t: Tm Γ (subst_ty A δ)),
    Sub Γ (ctx_ext Δ A)
| id : forall {Γ}, Sub Γ Γ
| comp : forall {Γ Δ Σ}, Sub Δ Σ -> Sub Γ Δ -> Sub Γ Σ
| π1 : forall {Γ Δ} {A : Ty Δ}, Sub Γ (ctx_ext Δ A) ->  Sub Γ Δ

with Tm : forall Γ, Ty Γ -> Type :=
| subst_tm : forall {Γ Δ} {A : Ty Δ} (t : Tm Δ A) (δ : Sub Γ Δ), Tm Γ (subst_ty A δ)
| π2 : forall {Γ Δ} {A : Ty Δ} (δ : Sub Γ (ctx_ext Δ A)), Tm Γ (subst_ty A (π1 δ))
| app : forall {Γ} {A : Ty Γ} {B : Ty (ctx_ext Γ A)}, Tm Γ (Pi A B) -> Tm (ctx_ext Γ A) B
| lam : forall {Γ} {A : Ty Γ} {B : Ty (ctx_ext Γ A)}, Tm (ctx_ext Γ A) B -> Tm Γ (Pi A B)
.

(* Scheme Ctxelim := Induction for Ctx Sort Type *)
(*   with Tyelim := Induction for Ty Sort Type *)
(*   with Selim := Induction for Sub Sort Type *)
(*   with Tmelim := Induction for Tm Sort Type. *)

Section elim.
  Variables
    (CtxM : Ctx -> Type)
    (TyM : forall Γ, CtxM Γ -> Ty Γ -> Type)
    (SubM : forall Γ, CtxM Γ -> forall Δ, CtxM Δ -> Sub Γ Δ -> Type)
    (TmM : forall Γ (pΓ : CtxM Γ) (t : Ty Γ), TyM Γ pΓ t -> Tm Γ t -> Type).

  Variables
    (femp : CtxM emp_ctx)
    (fext : forall (x : Ctx) (x0 : CtxM x) (x1 : Ty x) (x2 : TyM x x0 x1),
        CtxM (ctx_ext x x1))

    (fsubst : forall Γ pΓ Δ pΔ (t : Ty Δ),
        TyM _ pΔ t -> forall s : Sub Γ Δ, SubM Γ pΓ Δ pΔ s -> TyM _ pΓ (subst_ty t s))
    (fU : forall x (x0 : CtxM x), TyM x x0 U)
    (fEl : forall Γ pΓ t, TmM Γ pΓ U (fU _ pΓ) t -> TyM Γ pΓ (El t))
    (fPi : forall Γ A B pΓ pa, TyM _ (fext _ pΓ _ pa) B -> TyM Γ pΓ (Pi A B))

    (fempsub : forall Γ pΓ, SubM Γ pΓ emp_ctx femp emp_sub)
    (fsubext : forall Γ (pΓ : CtxM Γ) (Δ : Ctx) (pΔ: CtxM Δ)
                 (δ : Sub Γ Δ) (pδ : SubM Γ pΓ Δ pΔ δ)
                 (A : Ty Δ) (pA : TyM Δ pΔ A)
                 (t : Tm Γ (subst_ty A δ))
                 (pt : TmM Γ pΓ _ (fsubst _ _ _ _ A pA δ pδ) t),
        SubM Γ pΓ (ctx_ext Δ A) (fext _ pΔ _ pA) (sub_ext δ t))
    (fsubid : forall Γ pΓ, SubM Γ pΓ Γ pΓ id)
    (fsubcomp : forall Γ pΓ Δ pΔ Σ pΣ (s : Sub Δ Σ) (ps : SubM Δ pΔ Σ pΣ s)
                  (s0 : Sub Γ Δ) (ps0 : SubM Γ pΓ Δ pΔ s0),
        SubM Γ pΓ Σ pΣ (comp s s0))
    (fsubwk : forall Γ pΓ Δ pΔ A pA (s : Sub Γ (ctx_ext Δ A))
                (ps : SubM Γ pΓ (ctx_ext Δ A) (fext _ pΔ _ pA) s),
        SubM Γ pΓ Δ pΔ (π1 s))

    (fsubtm : forall Γ pΓ Δ pΔ A pA t (pt : TmM _ pΔ _ pA t)
                (δ : Sub Γ Δ) (pδ : SubM Γ pΓ Δ pΔ δ),
        TmM Γ pΓ _ (fsubst _ _ _ _ A pA δ pδ) (subst_tm t δ))
    (fpi2 : forall Γ pΓ Δ (pΔ : CtxM Δ) A pA δ pδ,
        TmM Γ pΓ _ (fsubst _ _ _ pΔ A pA _ (fsubwk _ _ _ _ A pA δ pδ)) (π2 δ))
    (fapp : forall Γ (pΓ : CtxM Γ) (A : Ty Γ) pA B (pB : TyM _ (fext _ pΓ A pA) B)
              t (pT : TmM _ pΓ _ (fPi _ _ _ _ _ pB) t),
        TmM _ (fext _ pΓ _ pA) _ pB (app t))
    (flam : forall Γ pΓ A (pA : TyM Γ pΓ A) (B : Ty (ctx_ext Γ A)) pB
              (t : Tm (ctx_ext Γ A) B) (pt : TmM _ (fext _ pΓ _ pA) B pB t),
        TmM Γ pΓ (Pi A B) (fPi Γ A B pΓ pA pB) (lam t)).

  Definition Ctx_elim :=
    fix FCtx (c : Ctx) { struct c } : CtxM c :=
      match c return (CtxM c) with
      | emp_ctx => femp
      | ctx_ext g t => fext g (FCtx g) t (FTy t)
      end
    with FTy {Γ : Ctx} (ty : Ty Γ) {struct ty} : TyM Γ (FCtx Γ) ty :=
      match ty in Ty g return TyM g (FCtx g) ty with
      | @U g => fU g (FCtx g)
      | @El g t => fEl g (FCtx g) t (FTm g (@U g) t)
      | @Pi g a b => fPi g a b (FCtx g) (FTy a)
                       (FTy b : TyM (ctx_ext g a) (FCtx (ctx_ext g a)) b)
      | @subst_ty Γ Δ t s => fsubst _ _ _ _ t (FTy t) s (FSub _ _ s)
      end
    with FSub (Γ : Ctx) (Δ : Ctx) (s : Sub Γ Δ) {struct s} : SubM Γ (FCtx Γ) Δ (FCtx Δ) s :=
      match s as s' in Sub Γ Δ return SubM Γ (FCtx Γ) Δ (FCtx Δ) s' with
      | @emp_sub Γ => fempsub Γ (FCtx Γ)
      | @sub_ext Γ Δ δ A t =>
        fsubext _ (FCtx Γ) _ (FCtx Δ) δ (FSub _ _ δ) _ (FTy A) t (FTm _ _ t)
      | @id Γ => fsubid Γ (FCtx Γ)
      | @comp Γ Δ Σ s s0 => fsubcomp _ _ _ _ _ _ _ (FSub _ _ s) _ (FSub _ _ s0)
      | @π1 Γ Δ A s => fsubwk _ (FCtx Γ) _ (FCtx Δ) _ (FTy A) _ (FSub _ _ s)
      end
    with FTm (Γ : Ctx) (ty : Ty Γ) (t : Tm Γ ty) {struct t} :
           TmM Γ (FCtx Γ) ty (FTy ty) t :=
      match t as t in Tm Γ ty return TmM Γ (FCtx Γ) ty (FTy ty) t with
      | @subst_tm Γ Δ A t δ =>
        fsubtm _ _ _ _ _ _ t (FTm _ _ t) δ (FSub _ _ δ)
      | @π2 Γ Δ A δ => fpi2 _ (FCtx Γ) _ (FCtx Δ) _ (FTy A) _ (FSub _ _ δ)
      | @app Γ A B t => fapp _ (FCtx Γ) _ (FTy A) _ (FTy B) _ (FTm _ _ t)
      | @lam Γ A B t => flam _ (FCtx Γ) _ (FTy A) _ (FTy B) _ (FTm _ _ t)
      end
  for FCtx.

  Definition Ty_elim : forall Γ ty, TyM Γ (Ctx_elim Γ) ty :=
    fix FCtx (c : Ctx) : CtxM c :=
      match c return (CtxM c) with
      | emp_ctx => femp
      | ctx_ext g t => fext g (FCtx g) t (FTy g t)
      end
    with FTy (Γ : Ctx) (ty : Ty Γ) {struct ty} : TyM Γ (FCtx Γ) ty :=
      match ty in Ty g return TyM g (FCtx g) ty with
      | @U g => fU g (FCtx g)
      | @El g t => fEl g (FCtx g) t (FTm g (@U g) t)
      | @Pi g a b => fPi g a b (FCtx g) (FTy g a)
                       (FTy (ctx_ext g a) b : TyM (ctx_ext g a) (FCtx (ctx_ext g a)) b)
      | @subst_ty Γ Δ t s => fsubst _ _ _ _ t (FTy _ t) s (FSub _ _ s)
      end
    with FSub (Γ : Ctx) (Δ : Ctx) (s : Sub Γ Δ) : SubM Γ (FCtx Γ) Δ (FCtx Δ) s :=
      match s with
      | @emp_sub Γ => fempsub Γ (FCtx Γ)
      | @sub_ext Γ Δ δ A t =>
        fsubext _ (FCtx Γ) _ (FCtx Δ) δ (FSub _ _ δ) _ (FTy _ A) t (FTm _ _ t)
      | @id Γ => fsubid Γ (FCtx Γ)
      | @comp Γ Δ Σ s s0 => fsubcomp _ _ _ _ _ _ _ (FSub _ _ s) _ (FSub _ _ s0)
      | @π1 Γ Δ A s => fsubwk _ (FCtx Γ) _ (FCtx Δ) _ (FTy _ A) _ (FSub _ _ s)
      end
    with FTm (Γ : Ctx) (ty : Ty Γ) (t : Tm Γ ty) {struct t} :
           TmM Γ (FCtx Γ) ty (FTy Γ ty) t :=
      match t as t in Tm Γ ty return TmM Γ (FCtx Γ) ty (FTy Γ ty) t with
      | @subst_tm Γ Δ A t δ =>
        fsubtm _ _ _ _ _ _ t (FTm _ _ t) δ (FSub _ _ δ)
      | @π2 Γ Δ A δ => fpi2 _ (FCtx Γ) _ (FCtx Δ) _ (FTy _ A) _ (FSub _ _ δ)
      | @app Γ A B t => fapp _ (FCtx Γ) _ (FTy _ A) _ (FTy _ B) _ (FTm _ _ t)
      | @lam Γ A B t => flam _ (FCtx Γ) _ (FTy _ A) _ (FTy _ B) _ (FTm _ _ t)
      end
   for FTy.

  Definition Tm_elim : forall Γ ty (t : Tm Γ ty), TmM Γ (Ctx_elim Γ) ty (Ty_elim Γ ty) t :=
    fix FCtx (c : Ctx) : CtxM c :=
      match c return (CtxM c) with
      | emp_ctx => femp
      | ctx_ext g t => fext g (FCtx g) t (FTy g t)
      end
    with FTy (Γ : Ctx) (ty : Ty Γ) {struct ty} : TyM Γ (FCtx Γ) ty :=
      match ty in Ty g return TyM g (FCtx g) ty with
      | @U g => fU g (FCtx g)
      | @El g t => fEl g (FCtx g) t (FTm g (@U g) t)
      | @Pi g a b => fPi g a b (FCtx g) (FTy g a)
                       (FTy (ctx_ext g a) b : TyM (ctx_ext g a) (FCtx (ctx_ext g a)) b)
      | @subst_ty Γ Δ t s => fsubst _ _ _ _ t (FTy _ t) s (FSub _ _ s)
      end
    with FSub (Γ : Ctx) (Δ : Ctx) (s : Sub Γ Δ) : SubM Γ (FCtx Γ) Δ (FCtx Δ) s :=
      match s with
      | @emp_sub Γ => fempsub Γ (FCtx Γ)
      | @sub_ext Γ Δ δ A t =>
        fsubext _ (FCtx Γ) _ (FCtx Δ) δ (FSub _ _ δ) _ (FTy _ A) t (FTm _ _ t)
      | @id Γ => fsubid Γ (FCtx Γ)
      | @comp Γ Δ Σ s s0 => fsubcomp _ _ _ _ _ _ _ (FSub _ _ s) _ (FSub _ _ s0)
      | @π1 Γ Δ A s => fsubwk _ (FCtx Γ) _ (FCtx Δ) _ (FTy _ A) _ (FSub _ _ s)
      end
    with FTm (Γ : Ctx) (ty : Ty Γ) (t : Tm Γ ty) {struct t} :
           TmM Γ (FCtx Γ) ty (FTy Γ ty) t :=
      match t as t in Tm Γ ty return TmM Γ (FCtx Γ) ty (FTy Γ ty) t with
      | @subst_tm Γ Δ A t δ =>
        fsubtm _ _ _ _ _ _ t (FTm _ _ t) δ (FSub _ _ δ)
      | @π2 Γ Δ A δ => fpi2 _ (FCtx Γ) _ (FCtx Δ) _ (FTy _ A) _ (FSub _ _ δ)
      | @app Γ A B t => fapp _ (FCtx Γ) _ (FTy _ A) _ (FTy _ B) _ (FTm _ _ t)
      | @lam Γ A B t => flam _ (FCtx Γ) _ (FTy _ A) _ (FTy _ B) _ (FTm _ _ t)
      end
   for FTm.

End elim.


(** Basic interpretation *)

Definition interp_ctx : Ctx -> Type :=
 Ctx_elim
    (fun _ => Type)
    (fun cΓ Γ tyg => Γ -> Type)
    (fun cΓ Γ cΔ Δ s => Γ -> Δ)
    (fun cΓ Γ cty τ t => forall g : Γ, τ g)

    (* Ctx *)
    unit (fun _ X _ P => { A : X & P A})

    (* Ty *)
    (fun cΓ Γ cΔ Δ ct τΔ s f x => τΔ (f x))
    (fun cΓ Γ => fun _ => Set)
    (fun cΓ Γ ct t v => t v)
    (fun Γ A B pΓ pa pb subs =>
       (forall (A : pa subs), pb (existT _ subs A)))

    (* Sub *)
    (fun _ _ _ => tt)
    (fun  Γ pΓ Δ pΔ δ pδ A pA t pt X => (existT _ (pδ X) (pt _)))
    (fun Γ pΓ X => X)
    (fun Γ pΓ Δ pΔ Σ pΣ s ps s0 ps0 X => (ps (ps0 X)))
    (fun Γ pΓ Δ pΔ A pA s ps X => projT1 (ps X))

    (* Tm *)
    (fun Γ pΓ Δ pΔ A pA t pt δ pδ g => pt _)
    (fun Γ pΓ Δ pΔ A pA δ pδ g => projT2 (pδ g))
    (fun Γ pΓ A pA B pB t pT g => match g with existT _ g A => pT g A end)
    (fun Γ pΓ A pA B pB t pt g A0 => pt _).

Definition interp_Ty : forall Γ, Ty Γ -> interp_ctx Γ -> Type :=
  Ty_elim
    (fun _ => Type)
    (fun cΓ Γ tyg => Γ -> Type)
    (fun cΓ Γ cΔ Δ s => Γ -> Δ)
    (fun cΓ Γ cty τ t => forall g : Γ, τ g)

    (* Ctx *)
    unit (fun _ X _ P => { A : X & P A})

    (* Ty *)
    (fun cΓ Γ cΔ Δ ct τΔ s f x => τΔ (f x))
    (fun cΓ Γ => fun _ => Set)
    (fun cΓ Γ ct t v => t v)
    (fun Γ A B pΓ pa pb subs =>
       (forall (A : pa subs), pb (existT _ subs A)))

    (* Sub *)
    (fun _ _ _ => tt)
    (fun  Γ pΓ Δ pΔ δ pδ A pA t pt X => (existT _ (pδ X) (pt _)))
    (fun Γ pΓ X => X)
    (fun Γ pΓ Δ pΔ Σ pΣ s ps s0 ps0 X => (ps (ps0 X)))
    (fun Γ pΓ Δ pΔ A pA s ps X => projT1 (ps X))

    (* Tm *)
    (fun Γ pΓ Δ pΔ A pA t pt δ pδ g => pt _)
    (fun Γ pΓ Δ pΔ A pA δ pδ g => projT2 (pδ g))
    (fun Γ pΓ A pA B pB t pT g => match g with existT _ g A => pT g A end)
    (fun Γ pΓ A pA B pB t pt g A0 => pt _).

Definition interp_Tm :
  forall Γ (τ : Ty Γ), Tm Γ τ -> forall v : interp_ctx Γ, interp_Ty Γ τ v :=
  Tm_elim
    (fun _ => Type)
    (fun cΓ Γ tyg => Γ -> Type)
    (fun cΓ Γ cΔ Δ s => Γ -> Δ)
    (fun cΓ Γ cty τ t => forall g : Γ, τ g)

    (* Ctx *)
    unit (fun _ X _ P => { A : X & P A})

    (* Ty *)
    (fun cΓ Γ cΔ Δ ct τΔ s f x => τΔ (f x))
    (fun cΓ Γ => fun _ => Set)
    (fun cΓ Γ ct t v => t v)
    (fun Γ A B pΓ pa pb subs =>
       (forall (A : pa subs), pb (existT _ subs A)))

    (* Sub *)
    (fun _ _ _ => tt)
    (fun  Γ pΓ Δ pΔ δ pδ A pA t pt X => (existT _ (pδ X) (pt _)))
    (fun Γ pΓ X => X)
    (fun Γ pΓ Δ pΔ Σ pΣ s ps s0 ps0 X => (ps (ps0 X)))
    (fun Γ pΓ Δ pΔ A pA s ps X => projT1 (ps X))

    (* Tm *)
    (fun Γ pΓ Δ pΔ A pA t pt δ pδ g => pt _)
    (fun Γ pΓ Δ pΔ A pA δ pδ g => projT2 (pδ g))
    (fun Γ pΓ A pA B pB t pT g => match g with existT _ g A => pT g A end)
    (fun Γ pΓ A pA B pB t pt g A0 => pt _).

(** Examples *)
Definition tyUU : Ty emp_ctx := Pi U U.
Eval compute in interp_Ty _ tyUU tt.

Definition Uctx : Ctx := ctx_ext emp_ctx U.

Definition TyUU' : Ty Uctx := Pi U U.
Eval compute in interp_Ty _ TyUU'.

Definition wk {Γ} {A : Ty Γ} : Sub (ctx_ext Γ A) Γ :=
  π1 id.

Definition vz {Γ} {A : Ty Γ} : Tm (ctx_ext Γ A) (subst_ty A wk) :=
  π2 id.

Definition vs {Γ} {A : Ty Γ} {B} : Tm Γ A -> Tm (ctx_ext Γ B) (subst_ty A wk) :=
  fun x => subst_tm x wk.

Definition idU := lam vz : Tm emp_ctx (Pi U (subst_ty U wk)).
Eval compute in interp_Tm _ _ idU tt.

(* Having the substitution calculus equations would be nicer *)
Axiom subst_ty_U : forall {Γ}, subst_ty U (@wk Γ U) = U.

Definition coetm {Γ A A'} : A = A' -> Tm Γ A -> Tm Γ A'.
Proof. intros H. destruct H. trivial. Defined.

Definition polyidty : Ty emp_ctx :=
  Pi U (El (coetm subst_ty_U vz)).

Eval compute in interp_Ty _  polyidty tt.

End WithElim.
