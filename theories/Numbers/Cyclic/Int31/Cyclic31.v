(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Int31 numbers defines indeed a cyclic structure : Z/(2^31)Z *)

(**
Author: Arnaud Spiwack (+ Pierre Letouzey)
*)
Require Import CyclicAxioms.
Require Export ZArith.
Require Export Int31Properties.

Local Open Scope int31_scope.
(** {2 Operators } **)

Definition Pdigits := Eval compute in P_of_succ_nat (size - 1).

Fixpoint positive_to_int_rec (n:nat) (p:positive) :=
  match n, p with 
  | O, _ => (Npos p, 0)
  | S n, xH => (0%N, 1)
  | S n, xO p => 
    let (N,i) := positive_to_int_rec n p in
    (N, i << 1)
  | S n, xI p =>
    let (N,i) := positive_to_int_rec n p in
    (N, (i << 1) + 1) 
  end.

Definition positive_to_int := positive_to_int_rec size.

Definition mulc_WW x y :=
  let (h, l) := mulc x y in
  if is_zero h then 
    if is_zero l then W0
    else WW h l
  else WW h l.
Notation "n '*c' m" := (mulc_WW n m) (at level 40, no associativity) : int31_scope.

Definition pos_mod p x := 
  if p <= digits then
    let p := digits - p in
    (x << p) >> p
  else x.

Instance int_ops : ZnZ.Ops int :=
{
 digits      := Pdigits; (* number of digits *)
 zdigits     := digits; (* number of digits *)
 to_Z        := to_Z; (* conversion to Z *)
 of_pos      := positive_to_int; (* positive -> N*int31 :  p => N,i
                                      where p = N*2^31+phi i *)
 head0       := head0;  (* number of head 0 *)
 tail0       := tail0;  (* number of tail 0 *)
 zero        := 0;
 one         := 1;
 minus_one   := max_int;
 compare     := compare;
 eq0         := is_zero;
 opp_c       := oppc;
 opp         := opp;
 opp_carry   := oppcarry;
 succ_c      := succc;
 add_c       := addc;
 add_carry_c := addcarryc;
 succ        := succ;
 add         := add;
 add_carry   := addcarry;
 pred_c      := predc;
 sub_c       := subc;
 sub_carry_c := subcarryc;
 pred        := pred;
 sub         := sub;
 sub_carry   := subcarry;
 mul_c       := mulc_WW;
 mul         := mul;
 square_c    := fun x => mulc_WW x x;
 div21       := diveucl_21;
 div_gt      := diveucl; (* this is supposed to be the special case of
                         division a/b where a > b *)
 div         := diveucl;
 modulo_gt   := Int31Native.mod;
 modulo      := Int31Native.mod;
 gcd_gt      := gcd;
 gcd         := gcd;
 add_mul_div := addmuldiv;
 pos_mod     := pos_mod;
 is_even     := is_even;
 sqrt2       := sqrt2;
 sqrt        := sqrt
}.

Local Open Scope Z_scope.

Lemma is_zero_spec_aux : forall x : int, is_zero x = true -> [|x|] = 0%Z.
Proof.
 intros x;rewrite is_zero_spec;intros H;rewrite H;trivial.
Qed.

Lemma positive_to_int_spec :
  forall p : positive,
    Zpos p =
      Z_of_N (fst (positive_to_int p)) * wB + to_Z (snd (positive_to_int p)).
Proof.
 (*** WARNING : TODO **)
Admitted.

Lemma mulc_WW_spec :
   forall x y,[|| x *c y ||] = [|x|] * [|y|].
Proof.
 intros x y;unfold mulc_WW.
 generalize (mulc_spec x y);destruct (mulc x y);simpl;intros Heq;rewrite Heq.
 case_eq (is_zero i);intros;trivial.
 apply is_zero_spec in H;rewrite H, to_Z_0.
 case_eq (is_zero i0);intros;trivial.
 apply is_zero_spec in H0;rewrite H0, to_Z_0, Zmult_comm;trivial.
Qed.

Lemma squarec_spec : 
  forall x,
    [||x *c x||] = [|x|] * [|x|].
Proof (fun x => mulc_WW_spec x x).

Lemma diveucl_spec_aux : forall a b, 0 < [|b|] ->
  let (q,r) := diveucl a b in
  [|a|] = [|q|] * [|b|] + [|r|] /\
  0 <= [|r|] < [|b|].
Proof.
 intros a b H;assert (W:= diveucl_spec a b).
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod [|a|] [|b|] H0).
 destruct (diveucl a b);destruct (Zdiv_eucl [|a|] [|b|]).
 inversion W;rewrite Zmult_comm;trivial.
Qed.

Lemma diveucl_21_spec_aux : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := diveucl_21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
Proof.
 intros a1 a2 b H1 H2;assert (W:= diveucl_21_spec a1 a2 b).
 assert (W1:= to_Z_bounded a1).
 assert ([|b|]>0) by (auto with zarith).
 generalize (Z_div_mod ([|a1|]*wB+[|a2|]) [|b|] H).
 destruct (diveucl_21 a1 a2 b);destruct (Zdiv_eucl ([|a1|]*wB+[|a2|]) [|b|]).
 inversion W;rewrite (Zmult_comm [|b|]);trivial.
Qed.

Lemma shift_unshift_mod_3:
  forall n p a : Z,
  0 <= p <= n ->
  (a * 2 ^ (n - p)) mod 2 ^ n / 2 ^ (n - p) = a mod 2 ^ p.
Proof.
 intros;rewrite <- (shift_unshift_mod_2 n p a);[ | auto with zarith].
 symmetry;apply Zmod_small.
 generalize (a * 2 ^ (n - p));intros w.
 assert (2 ^ n > 0) by (auto with zarith).
 assert (H1 := Z_mod_lt w _ H0).
 split;[apply div_le_0| apply div_lt];auto with zarith.
Qed.

Lemma pos_mod_spec : forall w p,
       [|pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
Proof.
 unfold pos_mod;intros.
 assert (W:=to_Z_bounded p);assert (W':=to_Z_bounded digits);assert (W'' := to_Z_bounded w).
 case_eq (p <= digits)%int31;intros Heq.
 rewrite leb_spec in Heq.
 rewrite lsr_spec, lsl_spec.
 assert (0 <= [|p|] <= [|digits|]) by (auto with zarith).
 rewrite <- (shift_unshift_mod_3 [|digits|] [|p|] [|w|] H).
 replace ([|digits|] - [|p|]) with [|digits - p|];trivial.
 rewrite sub_spec, Zmod_small;auto with zarith.
 symmetry;apply Zmod_small.
 rewrite <- Bool.not_true_iff_false, leb_spec in Heq.
 assert (2 ^ [|digits|] < 2 ^ [|p|]);[ apply Zpower_lt_monotone | ];auto with zarith.
 change wB with (2 ^ [|digits|]) in *;auto with zarith.
Qed.

Axiom sqrt2_spec : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt2 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].

(** {2 Specification and proof} **)
Global Instance int_specs : ZnZ.Specs int_ops := {
    spec_to_Z   := to_Z_bounded;
    spec_of_pos := positive_to_int_spec;
    spec_zdigits := refl_equal _;
    spec_more_than_1_digit:= refl_equal _;
    spec_0 := to_Z_0;
    spec_1 := to_Z_1;
    spec_m1 := refl_equal _;
    spec_compare := compare_spec;
    spec_eq0 := is_zero_spec_aux;
    spec_opp_c := oppc_spec;
    spec_opp := opp_spec;
    spec_opp_carry := oppcarry_spec;
    spec_succ_c := succc_spec;
    spec_add_c := addc_spec;
    spec_add_carry_c := addcarryc_spec;
    spec_succ := succ_spec;
    spec_add := add_spec;
    spec_add_carry := addcarry_spec;
    spec_pred_c := predc_spec;
    spec_sub_c := subc_spec;
    spec_sub_carry_c := subcarryc_spec;
    spec_pred := pred_spec;
    spec_sub := sub_spec;
    spec_sub_carry := subcarry_spec;
    spec_mul_c := mulc_WW_spec;
    spec_mul := mul_spec;
    spec_square_c := squarec_spec;
    spec_div21 := diveucl_21_spec_aux;
    spec_div_gt := fun a b _ => diveucl_spec_aux a b;
    spec_div := diveucl_spec_aux;
    spec_modulo_gt := fun a b _ _ => mod_spec a b;
    spec_modulo := fun a b _ => mod_spec a b;
    spec_gcd_gt := fun a b _ => gcd_spec a b;
    spec_gcd := gcd_spec;
    spec_head00 := head00_spec;
    spec_head0 := head0_spec;
    spec_tail00 := tail00_spec;
    spec_tail0 := tail0_spec;
    spec_add_mul_div := addmuldiv_spec;
    spec_pos_mod := pos_mod_spec;
    spec_is_even := is_even_spec;
    spec_sqrt2 := sqrt2_spec;
    spec_sqrt := sqrt_spec }.



Module Int31Cyclic <: CyclicType.
  Definition t := int.
  Definition ops := int_ops.
  Definition specs := int_specs.
End Int31Cyclic.

(*
(*
Lemma to_Z_rec_bounded :
  forall n i, (0 <= to_Z_rec n i < 2 ^ (Z_of_nat n))%Z.
Proof.
 induction n;simpl to_Z_rec.
 simpl;auto with zarith.
 intros;rewrite inj_S, Zpower_Zsucc;auto using Zle_0_nat.
 assert (W:= IHn (i>>1));clear IHn.
 destruct (is_even i);[rewrite Zdouble_mult | rewrite Zdouble_plus_one_mult];
  auto using Zle_0_nat with zarith.
Qed.

Lemma to_Z_bounded : forall i, (0 <= to_Z i < base digits31)%Z.
Proof (to_Z_rec_bounded size).

Lemma spec_0 : to_Z 0 = 0%Z.
Proof (refl_equal _).

Lemma spec_1 : to_Z 1 = 1%Z.
Proof (refl_equal _).

Lemma spec_max_int31 : to_Z max_int31 = (base digits31 - 1)%Z.
Proof (refl_equal _).

(** {3 Comparison} *)
Axiom spec_compare :
  forall x y, compare31 x y = (to_Z x ?= to_Z y)%Z.

Axiom spec_eq31 :forall x y, (x == y) = true <-> x = y.

Axiom spec_lt31 : 
  forall x y, (x < y) = Zlt_bool (to_Z x) (to_Z y).

Axiom spec_le31 : 
  forall x y, (x <= y) = Zle_bool (to_Z x) (to_Z y).

Lemma spec_is_zero_iff : 
  forall x, is_zero x = true <-> x = 0.
Proof (fun x => spec_eq31 x 0).

Lemma spec_is_zero : 
  forall x, is_zero x = true -> x = 0.
Proof.
 intros x H;rewrite spec_is_zero_iff in H;trivial.
Qed.

(** {3 arithmetic operations} *)

Axiom spec_add : 
  forall x y,
   to_Z (x + y) = (to_Z x + to_Z y) mod base digits31.

Lemma spec_add_carry : 
  forall x y,
   to_Z (add31carry x y) = (to_Z x + to_Z y + 1) mod base digits31.
Proof.
 unfold add31carry;intros.
 rewrite spec_add,spec_add,Zplus_mod_idemp_l;trivial.
Qed.

Axiom spec_add_c : 
  forall x y,
   interp_carry 1 (base digits31) to_Z (x +c y) = (to_Z x + to_Z y)%Z.

Axiom spec_add_carry_c : 
  forall x y,
   interp_carry 1 (base digits31) to_Z (add31carryc x y) = (to_Z x + to_Z y + 1)%Z.

Lemma spec_succ : 
  forall x,
   to_Z (succ31 x) = (to_Z x + 1) mod base digits31.
Proof (fun x => spec_add x 1).

Lemma spec_succ_c : 
  forall x,
   interp_carry 1 (base digits31) to_Z (succ31c x) =(to_Z x + 1)%Z.
Proof (fun x => spec_add_c x 1).

Axiom spec_sub : 
  forall x y,
   to_Z (x - y) = (to_Z x - to_Z y) mod base digits31.

Axiom spec_sub_c : 
  forall x y,
   interp_carry (-1)%Z (base digits31) to_Z (x -c y) = (to_Z x - to_Z y)%Z.

Lemma spec_sub_carry : 
  forall x y,
   to_Z (sub31carry x y) = (to_Z x - to_Z y - 1) mod base digits31.
Proof.
 unfold sub31carry;intros.
 rewrite spec_sub,spec_sub,Zminus_mod_idemp_l;trivial.
Qed.

Axiom spec_sub_carry_c : 
  forall x y,
   interp_carry (-1) (base digits31) to_Z (sub31carryc x y) = (to_Z x - to_Z y - 1)%Z.

Lemma spec_pred : 
  forall x,
   to_Z (pred31 x) = (to_Z x - 1) mod base digits31.
Proof (fun x => spec_sub x 1).

Lemma spec_pred_c : 
  forall x,
    interp_carry (-1) (base digits31) to_Z (pred31c x) = (to_Z x - 1)%Z.
Proof (fun x => spec_sub_c x 1).
 
Lemma spec_opp : 
  forall x,
   to_Z (- x) = (- to_Z x mod base digits31)%Z.
Proof (fun x => spec_sub 0 x).

Lemma spec_opp_carry : 
  forall x,
   to_Z (opp31carry x) = (base digits31 - to_Z x - 1)%Z.
Proof.
 intros;unfold opp31carry, max_int31.
 rewrite spec_sub.
 rewrite Zmod_small.
 (* change (to_Z 2147483647) with (2147483647)%Z.  (* marche pas *) *)
 change (2147483647 - to_Z x = 2147483648 - to_Z x - 1)%Z;ring.
 generalize (to_Z_bounded x).
 change (0 <= to_Z x < 2147483648 -> 0 <= 2147483647 - to_Z x < 2147483648).
 auto with zarith.
Qed.

Lemma spec_opp_c : 
  forall x,
   interp_carry (-1) (base digits31) to_Z (opp31c x) = (- to_Z x)%Z.
Proof (fun x => spec_sub_c 0 x).

Axiom spec_mul : 
  forall x y,
   to_Z (x * y) = (to_Z x * to_Z y) mod base digits31.

Axiom spec_mul31_c : 
  forall x y,
   (to_Z (fst(mul31c x y)) * base digits31 + to_Z (snd(mul31c x y)) = ZnZ.to_Z x * ZnZ.to_Z y)%Z.

Lemma spec_mul_c :
  forall x y,
   zn2z_to_Z (base digits31) to_Z (x *c y) = (to_Z x * to_Z y)%Z.
Proof.
 intros x y;unfold mul31c_WW.
 case_eq (is_zero x);intros.
 apply spec_is_zero in H;rewrite H, spec_0;trivial.
 case_eq (is_zero y);intros.
 apply spec_is_zero in H0;rewrite H0, spec_0, Zmult_comm;trivial.
 rewrite <- spec_mul31_c;destruct (mul31c x y);trivial.
Qed.

Lemma spec_square_c : 
  forall x,
    zn2z_to_Z (base digits31) to_Z (x *c x) = (to_Z x * to_Z x)%Z.
Proof (fun x => spec_mul_c x x).
 *)

(*
(*
Check foldi_cont31.
Print foldi_cont31.
Eval lazy beta delta iota in (fun A B f cont => foldi_cont31 A B f 0 2 cont).
Eval lazy in (fun A B f cont => foldi_cont31 A B f 0 2 cont).
Eval compute in (fun A B f cont => foldi_cont31 A B f 0 2 cont).
Eval vm_compute in (fun A B f cont => foldi_cont31 A B f 0 2 cont).
*)
Definition foldi A (f:int31 -> A -> A) from to :=
  foldi_cont31 A A (fun i cont a => cont (f i a)) from to (fun a => a).
Register foldi as Inline.

(*
Eval lazy in (fun A f => foldi A f 0 2).
Eval compute in (fun A f => foldi A f 0 2).
Eval vm_compute in (fun A f => foldi A f 0 2).

Eval lazy in (fun A B f cont => foldi_down_cont31 A B f 2 0 cont).
Eval compute in (fun A B f cont => foldi_down_cont31 A B f 2 0 cont).
Eval vm_compute in (fun A B f cont => foldi_down_cont31 A B f 2 0 cont).
*)
Definition foldi_down A (f:int31 -> A -> A) from downto :=
  foldi_down_cont31 A A (fun i cont a => cont (f i a)) from downto (fun a => a).
Register foldi as Inline.
(*
Eval lazy in (fun A f cont => foldi_down A f 2 0 cont).
Eval compute in (fun A f cont => foldi_down A f 2 0 cont).
Eval vm_compute in  (fun A f cont => foldi_down A f 2 0 cont).
*)


(*
Eval cbv in (fun A B f cont => foldi31_ntr A B f 0 2 cont).

Eval compute in (fun A B f cont => foldi31_ntr A B f 0 2 cont).
Set Draw Opt.
Definition toto := (fun A B f cont => foldi31_ntr A B f 0 2 cont).
Eval vm_compute in toto.

Set Vm Optimize.
Definition foldi A (f:int31 -> A -> A) min max :=
  foldi31_ntr A A (fun i cont a => cont (f i a)) min max (fun a => a).
Register foldi as Inline.
Definition tuuu min max := foldi int31 add31 min max 0.
Eval vm_compute in tuuu 1 3.
Eval vm_compute in fun A f => foldi A f 0 2.
Unset Draw Opt.
Unset Draw Instr.
Eval compute in fun A f => foldi A f 0 2.
(* fun (A : Type) (f : int31 -> A -> A) (a : A) => f 2 (f 1 (f 0 a)) *)
Eval vm_compute in fun A f => foldi A f 0 2.
(*fun (A : Type) (f : int31 -> A -> A) (x : A) => f 2 (f 1 (f 0 x)) *)
Set Draw Opt.

Definition fib k :=   
  if le31 k 1 then k 
  else
    let f (_ : int31) (cont : int31 -> int31 -> int31) (fip1 fi : int31) := cont (fip1 + fi) fip1 in
    foldi31_ntr _ _ f 2 k (fun fip1 fi => fip1) 1 0.

Definition aux := 0%nat.


Definition Ffib (_ : int31) (cont : int31 -> int31 -> int31) (fip1 fi : int31) := cont (fip1 + fi) fip1.
Register Ffib as Inline.
Definition fib2 k :=
if le31 k 1 then k 
else foldi31_ntr _ _ Ffib 2 k (fun fip1 fi => fip1) 1 0.


Print fib.
(_ : int31) (cont : int31 -> int31 -> int31) (fip1 fi : int31)
Time Eval cbv in fib 25.
Time Eval vm_compute in fib 25.

Definition tutu A B C f min max cont := foldi31_ntr A (B -> C) f min max cont.



Definition titi := (fun A B f cont a=> foldi31_ntr A B f 0 2 cont a).
(fun A B f cont a => foldi31_ntr A B f 0 2 cont a).

Check (refl_equal (fun A B f cont => foldi31_ntr A B f 0 2 cont) :
           (fun A B f cont => foldi31_ntr A B f 0 2 cont) = 
           (fun (A B : Type) (f : int31 -> (A -> B) -> A -> B) (cont : A -> B)
             (a : A) => f 0 (fun a0 : A => f 1 (fun a1 : A => f 2 cont a1) a0) a)).
 
Definition foldi A (f:int31 -> A -> A) min max :=
  foldi31_ntr A A (fun i cont a => cont (f i a)) min max (fun a => a).

Eval lazy in (fun A f => foldi A f 0 2).

Eval cbv in (fun A f => foldi A f 0 2).

Eval lazy in (foldi31_ntr int31 int31 (f 
Eval cbv in (fun A f a => foldi31_ntr A f a 0 2).
Eval cbv in (fun A f a => foldi_down31_ntr A f a 0 2).
Eval compute in (fun A f a => foldi31_ntr A f a 0 2).
Eval cbv delta [add31] in 1 + 1.
Eval cbv in (fun A f a => foldi_down31_ntr A f a 0 2).
Eval compute in (fun A f a => foldi_down31_ntr A f a 0 2).
Definition max_int := 0 - 1.
Eval vm_compute in (fun A f a => foldi_down31_ntr A f a (max_int-1) max_int).
Eval vm_compute in (fun A f a => foldi_down31_ntr A f a max_int max_int).
Eval compute in (fun A f a => foldi_down31_ntr A f a max_int max_int).
Eval lazy in (fun A f a => foldi_down31_ntr A f a max_int max_int).


Register array : Type -> Type as array_type.
Register make : forall A:Type, int31 -> A -> array A as array_make.
Register get : forall A:Type, array A -> int31 -> A as array_get.
Register set : forall A:Type, array A -> int31 -> A -> array A as array_set.

Eval compute in make int31 4 7.

Eval lazy in make int31 4 7.

Eval vm_compute in make int31 4 7.

Definition p1 := make int31 4 7.
Eval compute in get _ (set _ p1 2 3) 2.
Eval compute in get _ (set _ p1 2 3) 1.
Eval compute in get _ p1 10.
Eval compute in (set _ p1 2 3).
Eval compute in let p2 := set _ p1 2 3 in (p1, p2).

Eval lazy in get _ (set _ p1 2 3) 2.
Eval lazy in get _ (set _ p1 2 3) 1.
Eval lazy in get _ p1 10.
Eval lazy in (set _ p1 2 3).
Eval lazy in let p2 := set _ p1 2 3 in (p1, p2).

Eval vm_compute in get _ (set _ p1 2 3) 2.
Eval vm_compute in get _ (set _ p1 2 3) 1.
Eval vm_compute in get _ p1 10.
Eval vm_compute in (set _ p1 2 3).
Eval vm_compute in let p2 := set _ p1 2 3 in (p1, p2).


Eval lazy in (fun A f a => foldi_down31_ntr A f a 0 2).
Eval lazy in 1 + 2.
Check (refl_equal (fun A f a => foldi_down31_ntr A f a 0 2) : 
           (fun A f a => foldi_down31_ntr A f a 0 2) = 
            fun (A : Type) (f : int31 -> A -> A) (a : A) => f 2 (f 1 (f 0 a))).
Check (fun A => array (array A)).
Eval simpl in 0 + 1.
(* TODO : Simpl ne marche pas *)
Set Draw Opt.
Set Draw Instr.
Definition toto := 1 + 1.
Check foldi31_ntr.
Set Vm Optimize.
Definition toto1 := foldi31_ntr int31 (fun i acc => i + acc) 0 1 2.
Definition toto2 A F a := foldi31_ntr A F a 1 2.
Eval vm_compute in toto2.
Definition foldi (A:Type) (F:int31 -> A -> A) (a_start:A) (n_start n_end:int31) :=
  foldi31_ntr (A -> A) (fun i cont a => cont (F i a)) (fun a => a) n_start n_end a_start.
Eval lazy in fun A F a => foldi A F a 1 2.
Eval compute in fun A F a => foldi A F a 1 2.
Eval vm_compute in fun A F a => foldi A F a 1 2.

Set Vm Optimize.
Definition foldi_test1 (a_start:int31) (n_start n_end:int31) :=
  let x := 1 + 1 in
  let A := int31 in
  foldi31_ntr A (fun i a => a + a) 1 n_end a_start.


Definition foldi_test (a_start:int31) (n_start n_end:int31) :=
  let x := 1 + 1 in
  let A := int31 in
  foldi31_ntr (A -> A) (fun i cont a => cont (x + i + a + a)) (fun a => a) n_start n_end a_start.


Definition test z1 z := 
  let plus := plus in
  let w := z in
  let w1 := z in
  let x := 1 + w + z1 in
  fun y ww:int31 => (x + y + z + w + w1 + z1, plus 0%nat 0%nat).
Unset Vm Optimize.
Definition toto1' := foldi_down31_ntr int31 (fun i acc => i + acc) 0 1 2.
Definition foldi_down (A:Type) (F:int31 -> A -> A) (a_start:A) (n_start n_end:int31) :=
  foldi_down31_ntr (A -> A) (fun i cont a => cont (F i a)) (fun a => a) n_start n_end a_start.
Set Vm Optimize.
Definition foldi_down' (A:Type) (F:int31 -> A -> A) (a_start:A) (n_start n_end:int31) :=
  foldi_down31_ntr (A -> A) (fun i cont a => cont (F i a)) (fun a => a) n_start n_end a_start.
Register foldi_down as Inline.
Definition foldi_test' (a_start:int31) (n_start n_end:int31) :=
  foldi_down int31 (fun i acc => i + acc) n_end n_end n_start.
  let A := int31 in
  foldi31_ntr (A -> A) (fun i cont a => cont (i + a)) (fun a => a) n_start n_end a_start.



Unset Draw Opt.
Unset Draw Instr.
Eval vm_compute in (fun A f a => foldi31_ntr A f a 0 2).
*)
*)

Section Int31_Specs.

 Local Open Scope Z_scope.

 Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99).

 Local Notation wB := (2 ^ [|digits|]).

 Lemma wB_pos : wB > 0.
 Proof.
  compute;auto with zarith.
 Qed.

 Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, x at level 99).

 Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, x at level 99).

 Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99).

 Lemma to_Z_rec_bounded :
  forall n i, 0 <= to_Z_rec n i < 2 ^ (Z_of_nat n).
 Proof.
  induction n;simpl to_Z_rec.
  simpl;auto with zarith.
  intros;rewrite inj_S, Zpower_Zsucc;auto using Zle_0_nat.
  assert (W:= IHn (i>>1));clear IHn.
  destruct (is_even i);[rewrite Zdouble_mult | rewrite Zdouble_plus_one_mult];
   auto using Zle_0_nat with zarith.
 Qed.

 Lemma to_Z_bounded : forall i, 0 <= [|i|] < wB.
 Proof (to_Z_rec_bounded size).

 Lemma spec_zdigits : [| 31 |] = 31.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_more_than_1_digit: 1 < 31.
 Proof.
  auto with zarith.
 Qed.

 Lemma spec_0   : [| 0 |] = 0.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_1   : [| 1 |] = 1.
 Proof.
  reflexivity.
 Qed.

 Lemma spec_max_int31 : [| max_int31 |] = wB - 1.
 Proof.
  reflexivity.
 Qed.

 Axiom spec_compare : forall x y,
   (x ?= y)%int31 = ([|x|] ?= [|y|]).

 Axiom spec_eq :forall x y, (x == y) = true <-> x = y.

 Axiom spec_lt : 
  forall x y, (x < y)%bool = Zlt_bool [|x|] [|y|].

 Axiom spec_le : 
  forall x y, (x <= y)%bool = Zle_bool [|x|] [|y|].

 Lemma spec_is_zero_iff : 
  forall x, is_zero x = true <-> x = 0%int31.
 Proof (fun x => spec_eq x 0).

 Lemma spec_is_zero : 
  forall x, is_zero x = true -> x = 0%int31.
 Proof.
  intros x H;rewrite spec_is_zero_iff in H;trivial.
 Qed.

 (** Addition *)

 Axiom spec_add_c  : forall x y, [+|x +c y|] = [|x|] + [|y|].

 Lemma spec_succ_c : forall x, [+|succ31c x|] = [|x|] + 1.
 Proof. intros; apply spec_add_c. Qed.

 Axiom spec_add_carry_c : forall x y, [+|add31carryc x y|] = [|x|] + [|y|] + 1.

 Axiom spec_add : forall x y, [|x+y|] = ([|x|] + [|y|]) mod wB.

 Lemma spec_add_carry :
	 forall x y, [|add31carry x y|] = ([|x|] + [|y|] + 1) mod wB.
 Proof.
  unfold add31carry;intros.
  rewrite spec_add,spec_add,Zplus_mod_idemp_l;trivial.
 Qed.

 Lemma spec_succ : forall x, [|succ31 x|] = ([|x|] + 1) mod wB.
 Proof. intros; apply spec_add. Qed.

 (** Substraction *)

 Axiom spec_sub_c : forall x y, [-|x -c y|] = [|x|] - [|y|].

 Axiom spec_sub_carry_c : forall x y, [-|sub31carryc x y|] = [|x|] - [|y|] - 1.

 Axiom spec_sub : forall x y, [|x-y|] = ([|x|] - [|y|]) mod wB.

 Lemma spec_sub_carry :
   forall x y, [|sub31carry x y|] = ([|x|] - [|y|] - 1) mod wB.
 Proof. 
  unfold sub31carry; intros.
  rewrite spec_sub,spec_sub,Zminus_mod_idemp_l;trivial.
 Qed.

 Lemma spec_opp_c : forall x, [-|opp31c x|] = -[|x|].
 Proof. intros; apply spec_sub_c. Qed.

 Lemma spec_opp : forall x, [|- x|] = (-[|x|]) mod wB.
 Proof. intros; apply spec_sub. Qed.

 Lemma spec_opp_carry : forall x, [|opp31carry x|] = wB - [|x|] - 1.
 Proof.
  unfold opp31carry;intros.
  rewrite spec_sub, spec_max_int31.
  rewrite <- Zminus_plus_distr, Zplus_comm, Zminus_plus_distr.
  apply Zmod_small.
  generalize (to_Z_bounded x);auto with zarith.
 Qed.

 Lemma spec_pred_c : forall x, [-|pred31c x|] = [|x|] - 1.
 Proof. intros; apply spec_sub_c. Qed.

 Lemma spec_pred : forall x, [|pred31 x|] = ([|x|] - 1) mod wB.
 Proof.
  intros; apply spec_sub.
 Qed.

 (** Multiplication *)

 Axiom spec_mul : 
  forall x y,
   [| x * y |] = ([|x|] * [|y|]) mod wB.
 
 Axiom spec_mul31_c : 
  forall x y,
   [| fst(mul31c x y)|] * wB + [|snd(mul31c x y)|] = [|x|] * [|y|].

 Lemma spec_mul_c :
   forall x y,[|| x *c y ||] = [|x|] * [|y|].
 Proof.
  intros x y;unfold mul31c_WW.
  case_eq (is_zero x);intros.
  apply spec_is_zero in H;rewrite H, spec_0;trivial.
  case_eq (is_zero y);intros.
  apply spec_is_zero in H0;rewrite H0, spec_0, Zmult_comm;trivial.
  rewrite <- spec_mul31_c;destruct (mul31c x y);trivial.
 Qed.

 Lemma spec_square_c : 
  forall x,
    [||x *c x||] = [|x|] * [|x|].
 Proof (fun x => spec_mul_c x x).

 (** Division *)

 Axiom spec_diveucl_def : forall a b, 
   let (q,r) := diveucl31 a b in
   ([|q|],[|r|]) = Zdiv_eucl [|a|] [|b|].

 Lemma spec_diveucl : forall a b, 0 < [|b|] ->
      let (q,r) := diveucl31 a b in
      [|a|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
  intros a b H;assert (W:= spec_diveucl_def a b).
  assert ([|b|]>0) by (auto with zarith).
  generalize (Z_div_mod [|a|] [|b|] H0).
  destruct (diveucl31 a b);destruct (Zdiv_eucl [|a|] [|b|]).
  inversion W;rewrite Zmult_comm;trivial.
 Qed.

 Axiom spec_diveucl_divmod : forall a b,
  diveucl31 a b = (a/b, a\%b)%int31.
   
 Lemma spec_mod :  forall a b, 
   [| a \% b|] = [|a|] mod [|b|].
 Proof.
  intros a b;assert (W := spec_diveucl_def a b).
  rewrite spec_diveucl_divmod in W.
  unfold Zmod;rewrite <- W;trivial.
 Qed.

 Lemma spec_div : forall a b,
   [| a / b|] = [|a|] / [|b|].
 Proof.
  intros a b;assert (W := spec_diveucl_def a b).
  rewrite spec_diveucl_divmod in W.
  unfold Zdiv;rewrite <- W;trivial.
 Qed.

 Axiom spec_diveucl21_def : forall a1 a2 b,
   let (q,r) := diveucl31_21 a1 a2 b in
   ([|q|],[|r|]) = Zdiv_eucl ([|a1|] * wB + [|a2|]) [|b|].

 Lemma spec_div21 : forall a1 a2 b,
      wB/2 <= [|b|] ->
      [|a1|] < [|b|] ->
      let (q,r) := diveucl31_21 a1 a2 b in
      [|a1|] *wB+ [|a2|] = [|q|] * [|b|] + [|r|] /\
      0 <= [|r|] < [|b|].
 Proof.
  intros a1 a2 b H1 H2;assert (W:= spec_diveucl21_def a1 a2 b).
  assert (W1:= to_Z_bounded a1).
  assert ([|b|]>0) by (auto with zarith).
  generalize (Z_div_mod ([|a1|]*wB+[|a2|]) [|b|] H).
  destruct (diveucl31_21 a1 a2 b);destruct (Zdiv_eucl ([|a1|]*wB+[|a2|]) [|b|]).
  inversion W;rewrite (Zmult_comm [|b|]);trivial.
 Qed.

 (* Logical operations *)

 Axiom spec_lsl : forall x i, [|x << i|] = [|x|] * 2^[|i|] mod wB.
 Axiom spec_lsr : forall x i, [|x >> i|] = [|x|] / 2^[|i|].

 Axiom spec_land : forall x y i, digit (x land y) i = digit x i && digit y i.
 Axiom spec_lor : forall x y i, digit (x lor y) i = digit x i || digit y i.
 Axiom spec_lxor : forall x y i, digit (x lxor y) i = xorb (digit x i) (digit y i).

 (* gcd *)
 (* TODO: remove this axiom *)
 Axiom spec_gcd : forall a b, Zis_gcd [|a|] [|b|] [|gcd31 a b|].

 (* add_mul_div *)
 Axiom spec_add_mul_div : forall x y p, [|p|] <= Zpos Pdigits ->
   [| addmuldiv31 p x y |] =
   ([|x|] * (2 ^ [|p|]) + [|y|] / (2 ^ ((Zpos Pdigits) - [|p|]))) mod wB.

 Lemma shift_unshift_mod_3:
  forall n p a : Z,
  0 <= p <= n ->
  (a * 2 ^ (n - p)) mod 2 ^ n / 2 ^ (n - p) = a mod 2 ^ p.
 Proof.
  intros;rewrite <- (shift_unshift_mod_2 n p a);[ | auto with zarith].
  symmetry;apply Zmod_small.
  generalize (a * 2 ^ (n - p));intros w.
  assert (2 ^ n > 0) by (auto with zarith).
  assert (H1 := Z_mod_lt w _ H0).
  split;[apply div_le_0| apply div_lt];auto with zarith.
 Qed.

 Lemma spec_pos_mod : forall w p,
       [|pos_mod p w|] = [|w|] mod (2 ^ [|p|]).
 Proof.
  unfold pos_mod;intros.
  assert (W:=to_Z_bounded p);assert (W':=to_Z_bounded digits);assert (W'' := to_Z_bounded w).
  case_eq (p <= digits)%bool;intros Heq.
  rewrite spec_le, <- Zle_is_le_bool  in Heq.
  rewrite spec_lsr, spec_lsl.
  assert (0 <= [|p|] <= [|digits|]) by (auto with zarith).
  rewrite <- (shift_unshift_mod_3 [|digits|] [|p|] [|w|] H).
  replace ([|digits|] - [|p|]) with [|digits - p|];trivial.
  rewrite spec_sub, Zmod_small;auto with zarith.
  symmetry;apply Zmod_small.
  rewrite <- Bool.not_true_iff_false, spec_le, <- Zle_is_le_bool in Heq.
  assert (2 ^ [|digits|] < 2 ^ [|p|]);[ apply Zpower_lt_monotone | ];auto with zarith.
 Qed.

 (* TODO : remove this axiom *)
 Axiom spec_is_even : forall x,
      if is_even x then [|x|] mod 2 = 0 else [|x|] mod 2 = 1.

 (* TODO : remove this axiom *)
 Axiom spec_of_pos_rec : forall n p, 
   to_Z_rec n (of_pos_rec n p) = Zpos p mod 2^(Z_of_nat n).

 (* TODO : remove this axiom *)
 Axiom spec_of_pos : forall p, 
   to_Z (of_pos p) = Zpos p mod wB.

 (* TODO: Il est peut-etre faux *)
 Lemma spec_of_Z : forall z,
   to_Z (of_Z z) =  z mod wB.
 Proof.
  destruct z.
  reflexivity.
  apply spec_of_pos.
  assert (wB > 0) by (assert (W1:=to_Z_bounded 0);omega).
  unfold of_Z;rewrite spec_opp, spec_of_pos.
  change (Zneg p) with (- (Zpos p)).
  case (Z_eq_dec (Zpos p mod wB) 0);intros Heq.
  rewrite Heq.
  change (-0) with 0;rewrite Zmod_0_l.
  rewrite Z_mod_zero_opp_full;trivial.
  apply Zmod_unique with (-(Zpos p/wB + 1)).
  apply Z_mod_lt;trivial.
  assert (W:= Zmod_unique (- (Zpos p mod wB)) wB (-1) (wB - (Zpos p mod wB))).
  rewrite <- W.
  apply Zopp_inj;ring_simplify.
  apply Z_div_mod_eq;trivial.
  assert (W1:= Z_mod_lt (Zpos p) wB H);auto with zarith.
  ring.
 Qed.

 (* TODO: Remove this axiom *)
 Axiom of_to_Z : forall x, of_Z (to_Z x) = x.

 Lemma to_Z_inj : forall x y,
   to_Z x = to_Z y -> x = y.
 Proof.
  intros x y H.
  rewrite <- (of_to_Z x), <- (of_to_Z y), H;trivial.
 Qed.

 (** Head and Tail operations *)

 Lemma spec_head00:  forall x, [|x|] = 0 -> [|head031 x|] = Zpos Pdigits.
 Proof. 
  change 0 with [|0|];intros x Heq.
  apply to_Z_inj in Heq;rewrite Heq;trivial.
 Qed.

 Axiom spec_head0  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|head031 x|]) * [|x|] < wB.

 Lemma spec_tail00:  forall x, [|x|] = 0 -> [|tail031 x|] = Zpos Pdigits.
 Proof.
  change 0 with [|0|];intros x Heq.
  apply to_Z_inj in Heq;rewrite Heq;trivial.
 Qed.

 Axiom spec_tail0  : forall x, 0 < [|x|] ->
         exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail031 x|]).

 (* Sqrt *)

 (* Direct transcription of an old proof
     of a fortran program in boyer-moore *)

 Lemma quotient_by_2 a: a - 1 <= (a/2) + (a/2).
 Proof.
 case (Z_mod_lt a 2); auto with zarith.
 intros H1; rewrite Zmod_eq_full; auto with zarith.
 Qed.

 Lemma sqrt_main_trick j k: 0 <= j -> 0 <= k ->
   (j * k) + j <= ((j + k)/2 + 1)  ^ 2.
 Proof.
 intros Hj; generalize Hj k; pattern j; apply natlike_ind;
   auto; clear k j Hj.
 intros _ k Hk; repeat rewrite Zplus_0_l.
 apply  Zmult_le_0_compat; generalize (Z_div_pos k 2); auto with zarith.
 intros j Hj Hrec _ k Hk; pattern k; apply natlike_ind; auto; clear k Hk.
 rewrite Zmult_0_r, Zplus_0_r, Zplus_0_l.
 generalize (sqr_pos (Zsucc j / 2)) (quotient_by_2 (Zsucc j));
   unfold Zsucc.
 rewrite Zpower_2, Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 auto with zarith.
 intros k Hk _.
 replace ((Zsucc j + Zsucc k) / 2) with ((j + k)/2 + 1).
 generalize (Hrec Hj k Hk) (quotient_by_2 (j + k)).
 unfold Zsucc; repeat rewrite Zpower_2;
   repeat rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
 repeat rewrite Zmult_1_l; repeat rewrite Zmult_1_r.
 auto with zarith.
 rewrite Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
 apply f_equal2 with (f := Zdiv); auto with zarith.
 Qed.

 Lemma sqrt_main i j: 0 <= i -> 0 < j -> i < ((j + (i/j))/2 + 1) ^ 2.
 Proof.
 intros Hi Hj.
 assert (Hij: 0 <= i/j) by (apply Z_div_pos; auto with zarith).
 apply Zlt_le_trans with (2 := sqrt_main_trick _ _ (Zlt_le_weak _ _ Hj) Hij).
 pattern i at 1; rewrite (Z_div_mod_eq i j); case (Z_mod_lt i j); auto with zarith.
 Qed.

 Lemma sqrt_init i: 1 < i -> i < (i/2 + 1) ^ 2.
 Proof.
 intros Hi.
 assert (H1: 0 <= i - 2) by auto with zarith.
 assert (H2: 1 <= (i / 2) ^ 2); auto with zarith.
   replace i with (1* 2 + (i - 2)); auto with zarith.
   rewrite Zpower_2, Z_div_plus_full_l; auto with zarith.
   generalize (sqr_pos ((i - 2)/ 2)) (Z_div_pos (i - 2) 2).
   rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
   auto with zarith.
 generalize (quotient_by_2 i).
 rewrite Zpower_2 in H2 |- *;
   repeat (rewrite Zmult_plus_distr_l ||
           rewrite Zmult_plus_distr_r ||
           rewrite Zmult_1_l || rewrite Zmult_1_r).
   auto with zarith.
 Qed.

 Lemma sqrt_test_true i j: 0 <= i -> 0 < j -> i/j >= j -> j ^ 2 <= i.
 Proof.
 intros Hi Hj Hd; rewrite Zpower_2.
 apply Zle_trans with (j * (i/j)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
 Qed.

 Lemma sqrt_test_false i j: 0 <= i -> 0 < j -> i/j < j ->  (j + (i/j))/2 < j.
 Proof.
 intros Hi Hj H; case (Zle_or_lt j ((j + (i/j))/2)); auto.
 intros H1; contradict H; apply Zle_not_lt.
 assert (2 * j <= j + (i/j)); auto with zarith.
 apply Zle_trans with (2 * ((j + (i/j))/2)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
 Qed.

 Lemma sqrt31_step_correct rec i j:
  0 < [|i|] -> 0 < [|j|] -> [|i|] < ([|j|] + 1) ^ 2 ->
   2 * [|j|] < wB ->
  (forall j1 : int31,
    0 < [|j1|] < [|j|] -> [|i|] < ([|j1|] + 1) ^ 2 ->
    [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|sqrt31_step rec i j|] ^ 2 <= [|i|] < ([|sqrt31_step rec i j|] + 1) ^ 2.
 Proof.
 assert (Hp2: 0 < [|2|]) by exact (refl_equal Lt).
 intros Hi Hj Hij H31 Hrec.
 unfold sqrt31_step.
 case_eq ((i / j < j)%bool);[ | rewrite <- Bool.not_true_iff_false];
  rewrite spec_lt, <- Zlt_is_lt_bool, spec_div;intros.
 assert ([| j + i / j|] = [|j|] + [|i|]/[|j|]).
   rewrite spec_add, Zmod_small;rewrite spec_div;auto with zarith.
 apply Hrec;rewrite spec_lsr, H0, spec_1;change (2^1) with 2.
 split; [ | apply sqrt_test_false;auto with zarith].
 replace ([|j|] + [|i|]/[|j|]) with
        (1 * 2 + (([|j|] - 2) + [|i|] / [|j|]));[ | ring].
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= [|i|]/ [|j|]) by (apply Z_div_pos; auto with zarith).
 assert (0 <= ([|j|] - 2 + [|i|] / [|j|]) / 2) ; auto with zarith.
 case (Zle_lt_or_eq 1 [|j|]); auto with zarith; intros Hj1.
 rewrite <- Hj1, Zdiv_1_r.
 assert (0 <= ([|i|] - 1) /2)%Z;[ |apply Z_div_pos]; auto with zarith.
 apply sqrt_main;auto with zarith.
 split;[apply sqrt_test_true | ];auto with zarith.
 Qed.
 
 Lemma iter31_sqrt_correct n rec i j: 0 < [|i|] -> 0 < [|j|] ->
  [|i|] < ([|j|] + 1) ^ 2 -> 2 * [|j|] < wB ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      [|i|] < ([|j1|] + 1) ^ 2 -> 2 * [|j1|] < wB ->
       [|rec i j1|] ^ 2 <= [|i|] < ([|rec i j1|] + 1) ^ 2) ->
  [|iter31_sqrt n rec i j|] ^ 2 <= [|i|] < ([|iter31_sqrt n rec i j|] + 1) ^ 2.
 Proof.
 revert rec i j; elim n; unfold iter31_sqrt; fold iter31_sqrt; clear n.
 intros rec i j Hi Hj Hij H31 Hrec; apply sqrt31_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec i j Hi Hj Hij H31 HHrec.
 apply sqrt31_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2 Hj31; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|]); auto with zarith.
 apply Zle_0_nat.
 Qed.

 Lemma spec_sqrt : forall x,
       [|sqrt31 x|] ^ 2 <= [|x|] < ([|sqrt31 x|] + 1) ^ 2.
 Proof.
 intros i; unfold sqrt31.
 rewrite spec_compare. case Zcompare_spec; rewrite spec_1;
   intros Hi; auto with zarith.
 repeat rewrite Zpower_2; auto with zarith.
 apply iter31_sqrt_correct; auto with zarith;
  rewrite spec_lsr, spec_1; change (2^1) with 2;  auto with zarith.
  replace ([|i|]) with (1 * 2 + ([|i|] - 2))%Z; try ring.
  assert (0 <= ([|i|] - 2)/2)%Z by (apply Z_div_pos; auto with zarith).
  rewrite Z_div_plus_full_l; auto with zarith.
  apply sqrt_init; auto.
  assert (W:= Z_mult_div_ge [|i|] 2);assert (W':= to_Z_bounded i);auto with zarith.
 intros j2 H1 H2; contradict H2; apply Zlt_not_le.
  change (2 ^ Z_of_nat 31) with wB;assert (W:=to_Z_bounded i).
  apply Zle_lt_trans with ([|i|]); auto with zarith.
  assert (0 <= [|i|]/2)%Z by (apply Z_div_pos; auto with zarith).
  apply Zle_trans with (2 * ([|i|]/2)); auto with zarith.
  apply Z_mult_div_ge; auto with zarith.
 case (to_Z_bounded i); repeat rewrite Zpower_2; auto with zarith.
 Qed.
(*
 Lemma sqrt312_step_def rec ih il j:
   sqrt312_step rec ih il j =
   match (ih ?= j)%int31 with
      Eq => j
    | Gt => j
    | _ =>
       match (fst (div3121 ih il j) ?= j)%int31 with
         Lt => let m := match j +c fst (div3121 ih il j) with
                       C0 m1 => fst (m1/2)%int31
                     | C1 m1 => (fst (m1/2) + v30)%int31
                     end in rec ih il m
       | _ =>  j
       end
   end.
 Proof.
 unfold sqrt312_step; case div3121; intros.
 simpl; case compare31; auto.
 Qed.

 Lemma sqrt312_lower_bound ih il j:
   phi2 ih  il  < ([|j|] + 1) ^ 2 -> [|ih|] <= [|j|].
 Proof.
 intros H1.
 case (phi_bounded j); intros Hbj _.
 case (phi_bounded il); intros Hbil _.
 case (phi_bounded ih); intros Hbih Hbih1.
 assert (([|ih|] < [|j|] + 1)%Z); auto with zarith.
 apply Zlt_square_simpl; auto with zarith.
 repeat rewrite <-Zpower_2; apply Zle_lt_trans with (2 := H1).
 apply Zle_trans with ([|ih|] * base)%Z; unfold phi2, base;
  try rewrite Zpower_2; auto with zarith.
 Qed.

 Lemma div312_phi ih il j: (2^30 <= [|j|] -> [|ih|] < [|j|] ->
  [|fst (div3121 ih il j)|] = phi2 ih il/[|j|])%Z.
 Proof.
 intros Hj Hj1.
 generalize (spec_div21 ih il j Hj Hj1).
 case div3121; intros q r (Hq, Hr).
 apply Zdiv_unique with (phi r); auto with zarith.
 simpl fst; apply trans_equal with (1 := Hq); ring.
 Qed.

 Lemma sqrt312_step_correct rec ih il j:
  2 ^ 29 <= [|ih|] -> 0 < [|j|] -> phi2 ih il < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] < [|j|] ->  phi2 ih il < ([|j1|] + 1) ^ 2 ->
     [|rec ih il j1|] ^ 2 <= phi2 ih il < ([|rec ih il j1|] + 1) ^ 2) ->
  [|sqrt312_step rec ih il  j|] ^ 2 <= phi2 ih il
      < ([|sqrt312_step rec ih il j|] + 1) ^  2.
 Proof.
 assert (Hp2: (0 < [|2|])%Z) by exact (refl_equal Lt).
 intros Hih Hj Hij Hrec; rewrite sqrt312_step_def.
 assert (H1: ([|ih|] <= [|j|])%Z) by (apply sqrt312_lower_bound with il; auto).
 case (phi_bounded ih); intros Hih1 _.
 case (phi_bounded il); intros Hil1 _.
 case (phi_bounded j); intros _ Hj1.
 assert (Hp3: (0 < phi2 ih il)).
 unfold phi2; apply Zlt_le_trans with ([|ih|] * base)%Z; auto with zarith.
 apply Zmult_lt_0_compat; auto with zarith.
 apply Zlt_le_trans with (2:= Hih); auto with zarith.
 rewrite spec_compare. case Zcompare_spec; intros Hc1.
 split; auto.
 apply sqrt_test_true; auto.
 unfold phi2, base; auto with zarith.
 unfold phi2; rewrite Hc1.
 assert (0 <= [|il|]/[|j|]) by (apply Z_div_pos; auto with zarith).
 rewrite Zmult_comm, Z_div_plus_full_l; unfold base; auto with zarith.
 unfold Zpower, Zpower_pos in Hj1; simpl in Hj1; auto with zarith.
 case (Zle_or_lt (2 ^ 30) [|j|]); intros Hjj.
 rewrite spec_compare; case Zcompare_spec;
  rewrite div312_phi; auto; intros Hc;
  try (split; auto; apply sqrt_test_true; auto with zarith; fail).
 apply Hrec.
 assert (Hf1: 0 <= phi2 ih il/ [|j|]) by (apply Z_div_pos; auto with zarith).
 case (Zle_lt_or_eq 1 ([|j|])); auto with zarith; intros Hf2.
 2: contradict Hc; apply Zle_not_lt; rewrite <- Hf2, Zdiv_1_r; auto with zarith.
 assert (Hf3: 0 < ([|j|] + phi2 ih il / [|j|]) / 2).
 replace ([|j|] + phi2 ih il/ [|j|])%Z with
        (1 * 2 + (([|j|] - 2) + phi2 ih il / [|j|])); try ring.
 rewrite Z_div_plus_full_l; auto with zarith.
 assert (0 <= ([|j|] - 2 + phi2 ih il / [|j|]) / 2) ; auto with zarith.
 assert (Hf4: ([|j|] + phi2 ih il / [|j|]) / 2 < [|j|]).
 apply sqrt_test_false; auto with zarith.
 generalize (spec_add_c j (fst (div3121 ih il j))).
 unfold interp_carry;  case add31c; intros r;
  rewrite div312_phi; auto with zarith.
 rewrite div31_phi; change [|2|] with 2%Z; auto with zarith.
 intros HH; rewrite HH; clear HH; auto with zarith.
 rewrite spec_add, div31_phi; change [|2|] with 2%Z; auto.
 rewrite Zmult_1_l; intros HH.
 rewrite Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
 change (phi v30 * 2) with (2 ^ Z_of_nat size).
 rewrite HH, Zmod_small; auto with zarith.
 replace (phi
    match j +c fst (div3121 ih il j) with
    | C0 m1 => fst (m1 / 2)%int31
    | C1 m1 => fst (m1 / 2)%int31 + v30
    end) with ((([|j|] + (phi2 ih il)/([|j|]))/2)).
 apply sqrt_main; auto with zarith.
 generalize (spec_add_c j (fst (div3121 ih il j))).
 unfold interp_carry;  case add31c; intros r;
  rewrite div312_phi; auto with zarith.
 rewrite div31_phi; auto with zarith.
 intros HH; rewrite HH; auto with zarith.
 intros HH; rewrite <- HH.
 change (1 * 2 ^ Z_of_nat size) with (phi (v30) * 2).
 rewrite Z_div_plus_full_l; auto with zarith.
 rewrite Zplus_comm.
 rewrite spec_add, Zmod_small.
 rewrite div31_phi; auto.
 split; auto with zarith.
 case (phi_bounded (fst (r/2)%int31));
   case (phi_bounded v30); auto with zarith.
 rewrite div31_phi; change (phi 2) with 2%Z; auto.
 change (2 ^Z_of_nat size) with (base/2 + phi v30).
 assert (phi r / 2 < base/2); auto with zarith.
 apply Zmult_gt_0_lt_reg_r with 2; auto with zarith.
 change (base/2 * 2) with base.
 apply Zle_lt_trans with (phi r).
 rewrite Zmult_comm; apply Z_mult_div_ge; auto with zarith.
 case (phi_bounded r); auto with zarith.
 contradict Hij; apply Zle_not_lt.
 assert ((1 + [|j|]) <= 2 ^ 30); auto with zarith.
 apply Zle_trans with ((2 ^ 30) * (2 ^ 30)); auto with zarith.
 assert (0 <= 1 + [|j|]); auto with zarith.
 apply Zmult_le_compat; auto with zarith.
 change ((2 ^ 30) * (2 ^ 30)) with ((2 ^ 29) * base).
 apply Zle_trans with ([|ih|] * base); auto with zarith.
 unfold phi2, base; auto with zarith.
 split; auto.
 apply sqrt_test_true; auto.
 unfold phi2, base; auto with zarith.
 apply Zle_ge; apply Zle_trans with (([|j|] * base)/[|j|]).
 rewrite Zmult_comm, Z_div_mult; auto with zarith.
 apply Zge_le; apply Z_div_ge; auto with zarith.
 Qed.

 Lemma iter312_sqrt_correct n rec ih il j:
  2^29 <= [|ih|] ->  0 < [|j|] -> phi2 ih il < ([|j|] + 1) ^ 2 ->
  (forall j1, 0 < [|j1|] -> 2^(Z_of_nat n) + [|j1|] <= [|j|] ->
      phi2 ih il < ([|j1|] + 1) ^ 2 ->
       [|rec ih il j1|] ^ 2 <= phi2 ih il < ([|rec ih il j1|] + 1) ^ 2)  ->
  [|iter312_sqrt n rec ih il j|] ^ 2 <= phi2 ih il
      < ([|iter312_sqrt n rec ih il j|] + 1) ^ 2.
 Proof.
 revert rec ih il j; elim n; unfold iter312_sqrt; fold iter312_sqrt; clear n.
 intros rec ih il j Hi Hj Hij Hrec; apply sqrt312_step_correct; auto with zarith.
 intros; apply Hrec; auto with zarith.
 rewrite Zpower_0_r; auto with zarith.
 intros n Hrec rec ih il j Hi Hj Hij HHrec.
 apply sqrt312_step_correct; auto.
 intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
 intros j2 Hj2 H2j2 Hjp2; apply Hrec; auto with zarith.
 intros j3 Hj3 Hpj3.
 apply HHrec; auto.
 rewrite inj_S, Zpower_Zsucc.
 apply Zle_trans with (2 ^Z_of_nat n + [|j2|])%Z; auto with zarith.
 apply Zle_0_nat.
 Qed.
*)
 (* TODO remove this axiom *)
 Axiom spec_sqrt2 : forall x y,
       wB/ 4 <= [|x|] ->
       let (s,r) := sqrt312 x y in
          [||WW x y||] = [|s|] ^ 2 + [+|r|] /\
          [+|r|] <= 2 * [|s|].
(*
 Proof.
 intros ih il Hih; unfold sqrt312.
 change [||WW ih il||] with (phi2 ih il).
 assert (Hbin: forall s, s * s + 2* s + 1 = (s + 1) ^ 2) by
  (intros s; ring).
 assert (Hb: 0 <= base) by (red; intros HH; discriminate).
 assert (Hi2: phi2 ih il < (phi Tn + 1) ^ 2).
   change ((phi Tn + 1) ^ 2) with (2^62).
  apply Zle_lt_trans with ((2^31 -1) * base + (2^31 - 1)); auto with zarith.
  2: simpl; unfold Zpower_pos; simpl; auto with zarith.
  case (phi_bounded ih); case (phi_bounded il); intros H1 H2 H3 H4.
  unfold base, Zpower, Zpower_pos in H2,H4; simpl in H2,H4.
  unfold phi2,Zpower, Zpower_pos; simpl iter_pos; auto with zarith.
 case (iter312_sqrt_correct 31 (fun _ _ j => j) ih il Tn); auto with zarith.
 change [|Tn|] with 2147483647; auto with zarith.
 intros j1 _ HH; contradict HH.
 apply Zlt_not_le.
 change [|Tn|] with 2147483647; auto with zarith.
 change (2 ^ Z_of_nat 31) with 2147483648; auto with zarith.
 case (phi_bounded j1); auto with zarith.
 set (s := iter312_sqrt 31 (fun _ _ j : int31 => j) ih il Tn).
 intros Hs1 Hs2.
 generalize (spec_mul_c s s); case mul31c.
 simpl zn2z_to_Z; intros HH.
 assert ([|s|] = 0).
 case (Zmult_integral _ _ (sym_equal HH)); auto.
 contradict Hs2; apply Zle_not_lt; rewrite H.
 change ((0 + 1) ^ 2) with 1.
 apply Zle_trans with (2 ^ Z_of_nat size / 4 * base).
 simpl; auto with zarith.
 apply Zle_trans with ([|ih|] * base); auto with zarith.
 unfold phi2; case (phi_bounded il); auto with zarith.
 intros ih1 il1.
 change [||WW ih1 il1||] with (phi2 ih1 il1).
 intros Hihl1.
 generalize (spec_sub_c il il1).
 case sub31c; intros il2 Hil2.
 simpl interp_carry in Hil2.
 rewrite spec_compare; case Zcompare_spec.
 unfold interp_carry.
 intros H1; split.
 rewrite Zpower_2, <- Hihl1.
 unfold phi2; ring[Hil2 H1].
 replace [|il2|] with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2; rewrite H1, Hil2; ring.
 unfold interp_carry.
 intros H1; contradict Hs1.
 apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
 unfold phi2.
 case (phi_bounded il); intros _ H2.
 apply Zlt_le_trans with (([|ih|] + 1) * base + 0).
 rewrite Zmult_plus_distr_l, Zplus_0_r; auto with zarith.
 case (phi_bounded il1); intros H3 _.
 apply Zplus_le_compat; auto with zarith.
 unfold interp_carry; change (1 * 2 ^ Z_of_nat size) with base.
 rewrite Zpower_2, <- Hihl1, Hil2.
 intros H1.
 case (Zle_lt_or_eq ([|ih1|] + 1) ([|ih|])); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with (phi2 ih1 il1 + 2 * [|s|] + 1).
 unfold phi2.
 case (phi_bounded il); intros Hpil _.
 assert (Hl1l: [|il1|] <= [|il|]).
  case (phi_bounded il2); rewrite Hil2; auto with zarith.
 assert ([|ih1|] * base + 2 * [|s|] + 1 <= [|ih|] * base); auto with zarith.
 case (phi_bounded s);  change (2 ^ Z_of_nat size) with base; intros _ Hps.
 case (phi_bounded ih1); intros Hpih1 _; auto with zarith.
 apply Zle_trans with (([|ih1|] + 2) * base); auto with zarith.
 rewrite Zmult_plus_distr_l.
 assert (2 * [|s|] + 1 <= 2 * base); auto with zarith.
 rewrite Hihl1, Hbin; auto.
 intros H2; split.
 unfold phi2; rewrite <- H2; ring.
 replace (base + ([|il|] - [|il1|])) with (phi2 ih il - ([|s|] * [|s|])).
 rewrite <-Hbin in Hs2; auto with zarith.
 rewrite <- Hihl1; unfold phi2; rewrite <- H2; ring.
 unfold interp_carry in Hil2 |- *.
 unfold interp_carry; change (1 * 2 ^ Z_of_nat size) with base.
 assert (Hsih: [|ih - 1|] = [|ih|] - 1).
  rewrite spec_sub, Zmod_small; auto; change [|1|] with 1.
  case (phi_bounded ih); intros H1 H2.
  generalize Hih; change (2 ^ Z_of_nat size / 4) with 536870912.
  split; auto with zarith.
 rewrite spec_compare; case Zcompare_spec.
 rewrite Hsih.
 intros H1; split.
 rewrite Zpower_2, <- Hihl1.
 unfold phi2; rewrite <-H1.
 apply trans_equal with ([|ih|] * base + [|il1|] + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2.
 change (2 ^ Z_of_nat size) with base; ring.
 replace [|il2|] with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2.
 rewrite <-H1.
 ring_simplify.
 apply trans_equal with (base + ([|il|] - [|il1|])).
 ring.
 rewrite <-Hil2.
 change (2 ^ Z_of_nat size) with base; ring.
 rewrite Hsih; intros H1.
 assert (He: [|ih|] = [|ih1|]).
   apply Zle_antisym; auto with zarith.
   case (Zle_or_lt [|ih1|] [|ih|]); auto; intros H2.
   contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
  unfold phi2.
  case (phi_bounded il); change (2 ^ Z_of_nat size) with base;
    intros _ Hpil1.
  apply Zlt_le_trans with (([|ih|] + 1) * base).
  rewrite Zmult_plus_distr_l, Zmult_1_l; auto with zarith.
  case (phi_bounded il1); intros Hpil2 _.
  apply Zle_trans with (([|ih1|]) * base); auto with zarith.
 rewrite Zpower_2, <-Hihl1; unfold phi2; rewrite <-He.
 contradict Hs1; apply Zlt_not_le; rewrite Zpower_2, <-Hihl1.
 unfold phi2; rewrite He.
 assert (phi il - phi il1 < 0); auto with zarith.
 rewrite <-Hil2.
 case (phi_bounded il2); auto with zarith.
 intros H1.
 rewrite Zpower_2, <-Hihl1.
 case (Zle_lt_or_eq ([|ih1|] + 2) [|ih|]); auto with zarith.
 intros H2; contradict Hs2; apply Zle_not_lt.
 replace (([|s|] + 1) ^ 2) with (phi2 ih1 il1 + 2 * [|s|] + 1).
 unfold phi2.
 assert ([|ih1|] * base + 2 * phi s + 1 <= [|ih|] * base + ([|il|] - [|il1|]));
  auto with zarith.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base).
 case (phi_bounded il2); intros Hpil2 _.
 apply Zle_trans with ([|ih|] * base + - base); auto with zarith.
 case (phi_bounded s);  change (2 ^ Z_of_nat size) with base; intros _ Hps.
 assert (2 * [|s|] + 1 <= 2 * base); auto with zarith.
 apply Zle_trans with ([|ih1|] * base + 2 * base); auto with zarith.
 assert (Hi: ([|ih1|] + 3) * base <= [|ih|] * base); auto with zarith.
 rewrite Zmult_plus_distr_l in Hi; auto with zarith.
 rewrite Hihl1, Hbin; auto.
 intros H2; unfold phi2; rewrite <-H2.
 split.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base); ring.
 replace (base + [|il2|]) with (phi2 ih il - phi2 ih1 il1).
 rewrite Hihl1.
 rewrite <-Hbin in Hs2; auto with zarith.
 unfold phi2; rewrite <-H2.
 replace [|il|] with (([|il|] - [|il1|]) + [|il1|]); try ring.
 rewrite <-Hil2.
 change (-1 * 2 ^ Z_of_nat size) with (-base); ring.
Qed.
*)

Lemma spec_eq0 x : is_zero x = true -> [|x|] = 0.
Proof.
 intros H;rewrite (spec_is_zero _ H);trivial.
Qed.

(* TODO remove this axiom *)
Axiom positive_to_int31_spec :
  forall p : positive,
    Zpos p =
      Z_of_N (fst (positive_to_int31 p)) * wB + to_Z (snd (positive_to_int31 p)).

 Global Instance int31_specs : ZnZ.Specs int31_ops := {
    spec_to_Z   := to_Z_bounded;
    spec_of_pos := positive_to_int31_spec; 
    spec_zdigits := spec_zdigits;
    spec_more_than_1_digit := spec_more_than_1_digit;
    spec_0   := spec_0;
    spec_1   := spec_1;
    spec_m1  := spec_max_int31;
    spec_compare := spec_compare;
    spec_eq0 := spec_eq0;
    spec_opp_c := spec_opp_c;
    spec_opp := spec_opp;
    spec_opp_carry := spec_opp_carry;
    spec_succ_c := spec_succ_c;
    spec_add_c := spec_add_c;
    spec_add_carry_c := spec_add_carry_c;
    spec_succ := spec_succ;
    spec_add := spec_add;
    spec_add_carry := spec_add_carry;
    spec_pred_c := spec_pred_c;
    spec_sub_c := spec_sub_c;
    spec_sub_carry_c := spec_sub_carry_c;
    spec_pred := spec_pred;
    spec_sub := spec_sub;
    spec_sub_carry := spec_sub_carry;
    spec_mul_c := spec_mul_c;
    spec_mul := spec_mul;
    spec_square_c := spec_square_c;
    spec_div21 := spec_div21;
    spec_div_gt := fun a b _ => spec_diveucl a b;
    spec_div := spec_diveucl;
    spec_modulo_gt := fun a b _ _ => spec_mod a b;
    spec_modulo := fun a b _ => spec_mod a b;
    spec_gcd_gt := fun a b _ => spec_gcd a b;
    spec_gcd := spec_gcd;
    spec_head00 := spec_head00;
    spec_head0 := spec_head0;
    spec_tail00 := spec_tail00;
    spec_tail0 := spec_tail0;
    spec_add_mul_div := spec_add_mul_div;
    spec_pos_mod := spec_pos_mod;
    spec_is_even := spec_is_even;
    spec_sqrt2 := spec_sqrt2;
    spec_sqrt := spec_sqrt }.

End Int31_Specs.


Module Int31Cyclic <: CyclicType.
  Definition t := int31.
  Definition ops := int31_ops.
  Definition specs := int31_specs.
End Int31Cyclic.


*)