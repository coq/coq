Require Import BinPos.

Inductive expr : Type :=
  Var : nat -> expr
| App : expr -> expr -> expr
| Abs : unit -> expr -> expr.

Inductive expr_acc
: expr -> expr -> Prop :=
  acc_App_l : forall f a : expr,
                expr_acc f (App f a)
| acc_App_r : forall f a : expr,
                expr_acc a (App f a)
| acc_Abs : forall (t : unit) (e : expr),
              expr_acc e (Abs t e).

Theorem wf_expr_acc : well_founded expr_acc.
Proof.
  red.
  refine (fix rec a : Acc expr_acc a :=
            match a as a return Acc expr_acc a with
              | Var v => Acc_intro _ (fun y (_H : expr_acc y (Var v)) =>
                                        match _H in expr_acc z Z
                                              return match Z return Prop with
                                                         | Var _ => Acc _ y
                                                         | _ => True
                                                       end
                                        with
                                          | acc_App_l _ _ => I
                                          | _ => I
                                        end)
              | App f x => Acc_intro _ (fun y (pf : expr_acc y (App f x)) =>
                                          match pf in expr_acc z Z
                                                return match Z return Prop with
                                                         | App a b => f = a -> x = b -> Acc expr_acc z
                                                         | _ => True
                                                       end
                                          with
                                            | acc_App_l f' x' => fun pf _ => match pf in _ = z return
                                                                                   Acc expr_acc z
                                                                             with
                                                                               | eq_refl => rec f
                                                                             end
                                            | acc_App_r f' x' => fun _ pf => match pf in _ = z return
                                                                                   Acc expr_acc z
                                                                             with
                                                                               | eq_refl => rec x
                                                                             end
                                            | _ => I
                                          end eq_refl eq_refl)
              | Abs t e => Acc_intro _ (fun y (pf : expr_acc y (Abs t e)) =>
                                          match pf in expr_acc z Z
                                                return match Z return Prop with
                                                         | Abs a b => e = b -> Acc expr_acc z
                                                         | _ => True
                                                       end
                                          with
                                            | acc_Abs f x => fun pf => match pf in _ = z return
                                                                             Acc expr_acc z
                                                                       with
                                                                         | eq_refl => rec e
                                                                       end
                                            | _ => I
                                          end eq_refl)
            end).
Defined.

Theorem wf_expr_acc_delay : well_founded expr_acc.
Proof.
  red.
  refine (fix rec a : Acc expr_acc a :=
            match a as a return Acc expr_acc a with
              | Var v => Acc_intro _ (fun y (_H : expr_acc y (Var v)) =>
                                        match _H in expr_acc z Z
                                              return match Z return Prop with
                                                         | Var _ => Acc _ y
                                                         | _ => True
                                                       end
                                        with
                                          | acc_App_l _ _ => I
                                          | _ => I
                                        end)
              | App f x => Acc_intro _ (fun y (pf : expr_acc y (App f x)) =>
                                          match pf in expr_acc z Z
                                                return match Z return Prop with
                                                         | App a b => (unit -> Acc expr_acc a) -> (unit -> Acc expr_acc b) -> Acc expr_acc z
                                                         | _ => True
                                                       end
                                          with
                                            | acc_App_l f' x' => fun pf _ => pf tt
                                            | acc_App_r f' x' => fun _ pf => pf tt
                                            | _ => I
                                          end (fun _ => rec f) (fun _ => rec x))
              | Abs t e => Acc_intro _ (fun y (pf : expr_acc y (Abs t e)) =>
                                          match pf in expr_acc z Z
                                                return match Z return Prop with
                                                         | Abs a b => (unit -> Acc expr_acc b) -> Acc expr_acc z
                                                         | _ => True
                                                       end
                                          with
                                            | acc_Abs f x => fun pf => pf tt
                                            | _ => I
                                          end (fun _ => rec e))
            end); 
    try solve [ inversion _H ].
Defined.

Fixpoint build_large (n : nat) : expr :=
  match n with
    | 0 => Var 0
    | S n =>
      let e := build_large n in
      App e e
  end.

Section guard.
  Context {A : Type} {R : A -> A -> Prop}.

  Fixpoint guard  (n : nat) (wfR : well_founded R) : well_founded R :=
    match n with
      | 0 => wfR
      | S n0 =>
        fun x : A =>
          Acc_intro x
                    (fun (y : A) (_ : R y x) => guard n0 (guard n0 wfR) y)
    end.
End guard.


Definition sizeF_delay : expr -> positive.
refine
  (@Fix expr (expr_acc)
       (wf_expr_acc_delay)
       (fun _ => positive)
       (fun e =>
          match e as e return (forall l, expr_acc l e -> positive) -> positive with
            | Var _ => fun _ => 1
            | App l r => fun rec => @rec l _ + @rec r _
            | Abs _ e => fun rec => 1 + @rec e _
          end%positive)).
eapply acc_App_l.
eapply acc_App_r.
eapply acc_Abs.
Defined.

Definition sizeF_guard : expr -> positive.
refine
  (@Fix expr (expr_acc)
       (guard 5 wf_expr_acc)
       (fun _ => positive)
       (fun e =>
          match e as e return (forall l, expr_acc l e -> positive) -> positive with
            | Var _ => fun _ => 1
            | App l r => fun rec => @rec l _ + @rec r _
            | Abs _ e => fun rec => 1 + @rec e _
          end%positive)).
eapply acc_App_l.
eapply acc_App_r.
eapply acc_Abs.
Defined.

Time Eval native_compute in sizeF_delay (build_large 2).
Time Eval native_compute in sizeF_guard (build_large 2).
