Require Import NArith ZArith ZModOffset Lia.
Require Import Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.

Module Zmod.

Record Zmod (m : positive) := Private_of_N_value {
  Private_to_N : N ; _ : Bool.Is_true (Private_to_N <? N.pos m)%N }.
Arguments Private_to_N {m}.

Definition to_Z {m} (x : Zmod m) := Z.of_N (Private_to_N x).
Notation unsigned := to_Z (only parsing).
Local Coercion to_Z : Zmod >-> Z.

Local Lemma to_Z_range {m} (x : Zmod m) : 0 <= to_Z x < Z.pos m.
Proof.
  case x as [x H]; cbv [to_Z Private_to_N].
  apply Is_true_eq_true, N.ltb_lt, N2Z.inj_lt in H; auto using N2Z.is_nonneg.
Qed.

Definition of_small_Z (m : positive) (z : Z) (H : True -> 0 <= z < Z.pos m) : Zmod m.
  refine (Private_of_N_value m (Z.to_N z) (transparent_true _ (fun _ => _))).
  abstract (apply Is_true_eq_left, N.ltb_lt; lia).
Defined.

Definition of_Z (m : positive) (z : Z) : Zmod m.
  refine (of_small_Z m (z mod (Z.pos m)) (fun _ => _)).
  abstract (apply Z.mod_pos_bound, Pos2Z.is_pos).
Defined.

Definition signed {m} (x : Zmod m) : Z :=
  if Z.ltb (Z.double x) m then x else x-m.

Notation zero := (Private_of_N_value _ 0 I).

Notation one := (of_Z _ 1).

(** Ring operations *)

Definition eqb {m} (x y : Zmod m) := Z.eqb (to_Z x) (to_Z y).

Definition add {m} (x y : Zmod m) : Zmod m.
  refine (let n := x + y in of_small_Z m (if Z.ltb n m then n else n-m) (fun _ => _)).
  abstract (pose proof to_Z_range x; pose proof to_Z_range y; case (Z.ltb_spec n m); lia).
Defined.

Definition sub {m} (x y : Zmod m) : Zmod m.
  refine (let z := x - y in of_small_Z m (if Z.leb 0 z then z else z+m) (fun _ => _)).
  abstract (pose proof to_Z_range x; pose proof to_Z_range y; case (Z.leb_spec 0 z); lia).
Defined.

Definition opp {m} (x : Zmod m) : Zmod m := sub zero x.

Definition mul {m} (x y : Zmod m) : Zmod m := of_Z m (to_Z x * to_Z y).

(** Three notions of division *)

Definition udiv {m} (x y : Zmod m) : Zmod m.
  refine (of_small_Z m (Z.div x y) (fun _ => _)).
  abstract (pose proof to_Z_range x; pose proof to_Z_range y;
    zify; Z.to_euclidean_division_equations; nia).
Defined.

Definition sdiv {m} (x y : Zmod m) := of_Z m (Z.div (signed x) (signed y)).

Definition inv {m} (x : Zmod m) : Zmod m := of_Z m (Znumtheory.invmod (to_Z x) m).

Definition mdiv {m} (x y : Zmod m) : Zmod m := mul x (inv y).

(**  Powers  *)

Definition pow_N {m} (a : Zmod m) n := N.iter_op mul one a n.

Definition pow_Z {m} (a : Zmod m) z :=
  if Z.ltb z 0 then inv (pow_N a (Z.abs_N z)) else pow_N a (Z.abs_N z).

(** Bitwise operations *)
Import Nbitwise.

Definition and {m} (x y : Zmod m) : Zmod m.
  refine (of_small_Z m (N.land (Z.to_N x) (Z.to_N y)) (fun _ => _)).
  abstract (pose (to_Z_range x); pose (N.land_mono (Z.to_N x) (Z.to_N y)); lia).
Defined.

Definition ndn {m} (x y : Zmod m) : Zmod m.
  refine (of_small_Z m (N.ldiff (Z.to_N x) (Z.to_N y)) (fun _ => _)).
  abstract (pose (to_Z_range x); pose (N.ldiff_mono (Z.to_N x) (Z.to_N y)); lia).
Defined.

Definition or {m} (x y : Zmod m) := of_Z m (Z.lor x y).

Definition xor {m} (x y : Zmod m) := of_Z m (Z.lxor x y).

Definition not {m} (x : Zmod m) := of_Z m (Z.lnot (to_Z x)).

Definition abs {m} (x : Zmod m) : Zmod m := if signed x <? 0 then opp x else x.

(** Shifts *)

Definition slu_N {m} (x : Zmod m) (n : N) := of_Z m (Z.shiftl x n).

Definition sru_N {m} (x : Zmod m) (n : N) : Zmod m.
  refine (of_small_Z m (N.shiftr (Z.to_N x) n) (fun _ => _)).
  abstract (pose (to_Z_range x); pose (N.shiftr_mono (Z.to_N x) n); lia).
Defined.

Definition srs_N {m} x (n : N) := of_Z m (Z.shiftr (@signed m x) n).

(** Shifts by [Zmod] are defined without truncation. This is appropriate for
 * some use cases and not for others. Truncating wrappers can be defined
 * similarly when sufficient; undefined behavior is out of scope here. *)

Definition slu {m} (x y : Zmod m) := @slu_N m x (Z.to_N y).
Notation shiftl := slu.
Definition sru {m} (x y : Zmod m) := @sru_N m x (Z.to_N y).
Definition srs {m} (x y : Zmod m) := @srs_N m x (Z.to_N y).

(** Enumerating elements *)

Definition elements m : list (Zmod m) :=
  map (fun i => of_Z m (Z.of_nat i)) (seq 0 (Pos.to_nat m)).

Definition positives (m : positive) :=
  let h := Z.to_nat ((m-1)/2) in
  map (fun i => of_Z m (Z.of_nat i)) (seq 1 h).

Definition negatives (m : positive) :=
  let h1 := Z.to_nat ((m-1)/2) in
  let h2 := Z.to_nat (m/2) in
  map (fun i => of_Z m (Z.of_nat i)) (seq (S h1) h2).

Definition invertibles m : list (Zmod m) :=
  filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (elements m).

Example elements_1 : elements 1 = [zero]. Proof. trivial. Qed.
Example positives_1 : positives 1 = []. Proof. trivial. Qed.
Example negatives_1 : negatives 1 = []. Proof. trivial. Qed.
Example invertibles_1 : invertibles 1 = [zero]. Proof. trivial. Qed.

Example elements_2 : elements 2 = [zero; one]. Proof. trivial. Qed.
Example positives_2 : positives 2 = []. Proof. trivial. Qed.
Example negatives_2 : negatives 2 = [one]. Proof. trivial. Qed.
Example invertibles_2 : invertibles 2 = [one]. Proof. trivial. Qed.

Example elements_3 : elements 3 = [zero; one; of_Z _ 2]. Proof. trivial. Qed.
Example positives_3 : positives 3 = [one]. Proof. trivial. Qed.
Example negatives_3 : negatives 3 = [opp one]. Proof. trivial. Qed.
Example invertibles_3 : invertibles 3 = [one; opp one]. Proof. trivial. Qed.

End Zmod.

Notation Zmod := Zmod.Zmod.


Local Coercion Zmod.to_Z : Zmod >-> Z.

Module Zstar.

Record Zstar (m : positive) := Private_of_N_value {
  Private_to_N : N ;
  _ : Is_true ((Private_to_N <? m)%N && (Z.gcd Private_to_N m =? 1)) }.
Arguments Private_to_N {m}.

Definition to_Zmod {m : positive} (a : Zstar m) : Zmod m.
  refine (Zmod.of_small_Z m (Private_to_N a) (fun _ => _)).
  abstract (case a as [a H]; cbv [Private_to_N];
    apply andb_prop_elim, proj1, Is_true_eq_true, N.ltb_lt in H; lia).
Defined.

Local Coercion to_Zmod : Zstar >-> Zmod.

Definition of_coprime_Zmod {m} (a : Zmod m) (H : True -> Z.gcd a m = 1) : Zstar m.
  refine (Private_of_N_value m (Z.to_N (Zmod.to_Z a)) (transparent_true _ (fun _ => _))).
  abstract (case a as [a Ha]; cbv [Zmod.to_Z Zmod.Private_to_N] in *; rewrite ?N2Z.id;
    apply andb_prop_intro, conj, Is_true_eq_left, Z.eqb_eq, H, I; trivial).
Defined.

Definition of_Zmod {m} (x : Zmod m) : Zstar m.
  refine (of_coprime_Zmod (if Z.eqb (Z.gcd x m) 1 then x else Zmod.one) (fun _ => _)).
  abstract (destruct (Z.eqb_spec (Z.gcd x m) 1); trivial; 
    cbv [Zmod.to_Z Zmod.Private_to_N Zmod.of_Z Zmod.of_small_Z];
    rewrite Z2N.id, Z.gcd_mod, Z.gcd_1_r; Z.div_mod_to_equations; lia).
Defined.

Definition one {m} : Zstar m := of_Zmod Zmod.one.

Definition opp {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.opp x).

Definition abs {m} (x : Zmod m) : Zmod m := of_Zmod (Zmod.abs x).

Definition mul {m} (a b : Zstar m) : Zstar m.
  refine (of_coprime_Zmod (Zmod.mul a b) _)%positive.
  abstract (cbv [Zmod.to_Z Zmod.mul Zmod.of_Z Zmod.of_small_Z]; cbn;
    rewrite !Z2N.id; try (Z.div_mod_to_equations; lia);
    rewrite Z.gcd_mod, Z.gcd_comm, Z.coprime_mul; trivial;
    case a as [a Ha]; cbn; apply Is_true_eq_true in Ha;
    case b as [b Hb]; cbn; apply Is_true_eq_true in Hb; lia).
Defined.

(**  Inverses and division have a canonical definition  *)

Definition inv {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.inv x).

Definition div {m} (x y : Zstar m) : Zstar m := mul x (inv y).

(**  Powers  *)

Definition pow_N {m} (a : Zstar m) n := N.iter_op mul one a n.

Definition pow_Z {m} (a : Zstar m) z :=
  if Z.ltb z 0 then inv (pow_N a (Z.abs_N z)) else pow_N a (Z.abs_N z).

(** Enumerating elements *)

Definition elements m : list (Zstar m) :=
  map of_Zmod (filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (Zmod.elements m)).

Definition positives m :=
  map of_Zmod (filter (fun x : Zmod m => Z.gcd x m =? 1) (Zmod.positives m)).

Definition negatives m :=
  map of_Zmod (filter (fun x : Zmod m => Z.gcd x m =? 1) (Zmod.negatives m)).
End Zstar.

Notation Zstar := Zstar.Zstar.
