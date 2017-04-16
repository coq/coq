Definition proj1_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : proj1_sig u = proj1_sig v
  := f_equal (@proj1_sig _ _) p.

Definition proj2_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : eq_rect _ _ (proj2_sig u) _ (proj1_sig_path p) = proj2_sig v
  := match p with eq_refl => eq_refl end.

Goal forall sz : nat,
    let sz' := sz in
    forall pf : sz = sz',
      let feq_refl := exist (fun x : nat => sz = x) sz' eq_refl in
      let fpf := exist (fun x : nat => sz = x) sz' pf in feq_refl = fpf -> 
proj2_sig feq_refl = proj2_sig fpf.
Proof.
  intros.
  etransitivity; [ | exact (proj2_sig_path H) ].
  Fail clearbody fpf.
