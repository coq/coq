Inductive type : Set :=
    Tptr : type -> type
  | Tref : type -> type
  | Trv_ref : type -> type
  | Tint : type -> type -> type
  | Tvoid : type
  | Tarray : type -> type -> type
  | Tnamed : type -> type
  | Tfunction : type -> type -> type -> type
  | Tbool : type
  | Tmember_pointer : type -> type -> type
  | Tfloat : type -> type
  | Tqualified : type -> type -> type
  | Tnullptr : type
  | Tarch : type -> type -> type
.
Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }.
Proof. fix IHty1 1.  decide equality. Defined.

Goal (if type_eq_dec (Tptr Tvoid) (Tptr Tvoid) then True else False).
Proof.
timeout 1 cbn.
constructor.
Qed.
