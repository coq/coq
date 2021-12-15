Require Import Program.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.
Set Printing Universes.

Local Open Scope positive.

Definition field : Type := positive.

Section poly.
  Universe U.

  Inductive fields : Type :=
  | pm_Leaf : fields
  | pm_Branch : fields -> option Type@{U} -> fields -> fields.

  Definition fields_left (f : fields) : fields :=
    match f with
    | pm_Leaf => pm_Leaf
    | pm_Branch l _ _ => l
    end.

  Definition fields_right (f : fields) : fields :=
    match f with
    | pm_Leaf => pm_Leaf
    | pm_Branch _ _ r => r
    end.

  Definition fields_here (f : fields) : option Type@{U} :=
    match f with
    | pm_Leaf => None
    | pm_Branch _ s _ => s
    end.

  Fixpoint fields_get (p : field) (m : fields) {struct p} : option Type@{U} :=
    match p with
      | xH => match m with
                | pm_Leaf => None
                | pm_Branch _ x _ => x
              end
      | xO p' => fields_get p' match m with
                               | pm_Leaf => pm_Leaf
                               | pm_Branch L _ _ => L
                             end
      | xI p' => fields_get p' match m with
                               | pm_Leaf => pm_Leaf
                               | pm_Branch _ _ R => R
                             end
    end.

  Definition fields_leaf : fields := pm_Leaf.

  Inductive member (val : Type@{U}) : fields -> Type :=
  | pmm_H : forall L R, member val (pm_Branch L (Some val) R)
  | pmm_L : forall (V : option Type@{U}) L R, member val L -> member val (pm_Branch L V R)
  | pmm_R : forall (V : option Type@{U}) L R, member val R -> member val (pm_Branch L V R).
  Arguments pmm_H {_ _ _}.
  Arguments pmm_L {_ _ _ _} _.
  Arguments pmm_R {_ _ _ _} _.

  Fixpoint get_member (val : Type@{U}) p {struct p}
  : forall m, fields_get p m = @Some Type@{U} val -> member val m :=
    match p as p return forall m, fields_get p m = @Some Type@{U} val -> member@{U} val m with
      | xH => fun m =>
        match m as m return fields_get xH m = @Some Type@{U} val -> member@{U} val m with
        | pm_Leaf => fun pf : None = @Some Type@{U} _ =>
                       match pf in _ = Z return match Z with
                                                | Some _ => _
                                                | None => unit
                                                end
                       with
                       | eq_refl => tt
                       end
        | pm_Branch _ None _ => fun pf : None = @Some Type@{U} _ =>
                                  match pf in _ = Z return match Z with
                                                           | Some _ => _
                                                           | None => unit
                                                           end
                                  with
                                  | eq_refl => tt
                                  end
        | pm_Branch _ (Some x) _ => fun pf : @Some Type@{U} x = @Some Type@{U} val =>
                                      match eq_sym pf in _ = Z return member@{U} val (pm_Branch _ Z _) with
                                      | eq_refl => pmm_H
                                      end
        end
      | xO p' => fun m =>
        match m as m return fields_get (xO p') m = @Some Type@{U} val -> member@{U} val m with
        | pm_Leaf => fun pf : fields_get p' pm_Leaf = @Some Type@{U} val =>
                       @get_member _ p' pm_Leaf pf
        | pm_Branch l _ _ => fun pf : fields_get p' l = @Some Type@{U} val =>
                       @pmm_L _ _ _ _ (@get_member _ p' l pf)
        end
      | xI p' => fun m =>
        match m as m return fields_get (xI p') m = @Some Type@{U} val -> member@{U} val m with
        | pm_Leaf => fun pf : fields_get p' pm_Leaf = @Some Type@{U} val =>
                       @get_member _ p' pm_Leaf pf
        | pm_Branch l _ r => fun pf : fields_get p' r = @Some Type@{U} val =>
                               @pmm_R _ _ _ _ (@get_member _ p' r pf)
        end
    end.

  Inductive record : fields -> Type :=
  | pr_Leaf : record pm_Leaf
  | pr_Branch : forall L R (V : option Type@{U}),
      record L ->
      match V return Type@{U} with
        | None => unit
        | Some t => t
      end ->
      record R ->
      record (pm_Branch L V R).


  Definition record_left {L} {V : option Type@{U}} {R}
             (r : record (pm_Branch L V R)) : record L :=
    match r in record z
          return match z with
                 | pm_Branch L _ _ => record L
                 | _ => unit
                 end
    with
      | pr_Branch _ l _ _ => l
      | pr_Leaf => tt
    end.
Set Printing All.
  Definition record_at {L} {V : option Type@{U}} {R} (r : record (pm_Branch L V R))
  : match V return Type@{U} with
    | None => unit
    | Some t => t
    end :=
    match r in record z
          return match z (* return ?X *) with
                 | pm_Branch _ V _ => match V return Type@{U} with
                                     | None => unit
                                     | Some t => t
                                     end
                 | _ => unit
                 end
    with
      | pr_Branch _ _ v _ => v
      | pr_Leaf => tt
    end.

  Definition record_here {L : fields} (v : Type@{U}) {R : fields}
             (r : record (pm_Branch L (@Some Type@{U} v) R)) : v :=
    match r in record z
          return match z return Type@{U} with
                 | pm_Branch _ (Some v) _ => v
                 | _ => unit
                 end
    with
      | pr_Branch _ _ v _ => v
      | pr_Leaf => tt
    end.

  Definition record_right {L V R} (r : record (pm_Branch L V R)) : record R :=
    match r in record z return match z with
                                  | pm_Branch _ _ R => record R
                                  | _ => unit
                                end
    with
      | pr_Branch _ _ _ r => r
      | pr_Leaf => tt
    end.

  Fixpoint record_get {val : Type@{U}} {pm : fields} (m : member val pm) : record pm -> val :=
    match m in member _ pm return record pm -> val with
      | pmm_H => fun r => record_here r
      | pmm_L m' => fun r => record_get m' (record_left r)
      | pmm_R m' => fun r => record_get m' (record_right r)
    end.

  Fixpoint record_set {val : Type@{U}} {pm : fields} (m : member val pm) (x : val) {struct m}
  : record pm -> record pm :=
    match m in member _ pm return record pm -> record pm with
    | pmm_H => fun r =>
      pr_Branch (Some _)
                (record_left r)
                x
                (record_right r)
    | pmm_L m' => fun r =>
      pr_Branch _
                (record_set m' x (record_left r))
                (record_at r)
                (record_right r)
    | pmm_R m' => fun r =>
      pr_Branch _ (record_left r)
                (record_at r)
                (record_set m' x (record_right r))
    end.
End poly.
Axiom cheat : forall {A}, A.
Lemma record_get_record_set_different:
  forall (T: Type) (vars: fields)
    (pmr pmw: member T vars)
    (diff: pmr <> pmw)
    (r: record vars) (val: T),
    record_get pmr (record_set pmw val r) = record_get pmr r.
Proof.
  intros.
  revert pmr diff r val.
  induction pmw; simpl; intros.
  - dependent destruction pmr.
    + congruence.
    + auto.
    + auto.
  - dependent destruction pmr.
    + auto.
    + simpl. apply IHpmw. congruence.
    + auto.
  - dependent destruction pmr.
    + auto.
    + auto.
    + simpl. apply IHpmw. congruence.
Qed.
