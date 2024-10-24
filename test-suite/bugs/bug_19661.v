Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X -> tele) : tele.

Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => forall x, tele_fun (b x) T
  end.

Notation "TT -t> A" := (tele_fun TT A) (at level 99, A at level 200, right associativity).

Record tele_arg_cons {X : Type} (f : X -> Type) : Type := TeleArgCons
  { tele_arg_head : X;
    tele_arg_tail : f tele_arg_head }.
Global Arguments TeleArgCons {_ _} _ _.

Fixpoint tele_arg (t : tele) : Type :=
  match t with
  | TeleO => unit
  | TeleS f => tele_arg_cons (fun x => tele_arg (f x))
  end.

Fixpoint tele_app {TT : tele} {U} : (TT -t> U) -> tele_arg TT -> U :=
  match TT as TT return (TT -t> U) -> tele_arg TT -> U with
  | TeleO => fun F _ => F
  | TeleS r => fun (F : TeleS r -t> U) '(TeleArgCons x b) =>
      tele_app (F x) b
  end.
Global Arguments tele_app {!_ _} & _ !_ /.

Axiom PROP: Type.
Axiom T : PROP.
Axiom atomic_commit :
  forall {TB : tele}
         (_ : forall (_ : tele_arg TB), PROP)
         (_ : forall (_ : tele_arg TB), PROP),
    PROP.

Fixpoint do_after_shatter  (next : nat) (d : nat) : PROP :=
  match d with
  | 0 => T
  | S d =>
  (@atomic_commit
      (@TeleS _ (fun l' => TeleO))
      ((@tele_app (@TeleS _ (fun l' => TeleO))
          _ (fun l' => T)))
      ((@tele_app (@TeleS _ (fun l' =>  TeleO))
          _ (fun l' =>
                      do_after_shatter (l'-1) d
                    ))))
  end.
