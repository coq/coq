(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Arith_base.

(** [fin n] is a convinient way to represent \[1 .. n\]

[fin n] can be seen as a n-uplet of unit where [F1] is the first element of
the n-uplet and [FS] set (n-1)-uplet of all the element but the first.

   Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

Inductive t : nat -> Set :=
|F1 : forall {n}, t (S n)
|FS : forall {n}, t n -> t (S n).

Section SCHEMES.
Definition case0 {P} (p: t 0): P p :=
  match p as p' in t n return
    match n as n' return t n' -> Type
  with |0 => fun f0 => P f0 |S _ => fun _ => @ID end p'
  with |F1 _ => @id |FS _ _ => @id end.

Definition caseS (P: forall n, t (S n) -> Type)
  (P1: forall n, P n F1) (PS : forall n (p: t n), P n (FS p))
  n (p: t (S n)): P n p :=
  match p as p0 in t n0
  return match n0 as nn return t nn -> Type with
    |0 => fun _ => @ID |S n' => fun p' => P n' p'
  end p0 with
  |F1 k => P1 k
  |FS k pp => PS k pp
  end.

Definition rectS (P: forall n, t (S n) -> Type)
  (P1: forall n, P n F1) (PS : forall n (p: t (S n)), P n p -> P (S n) (FS p)):
  forall n (p: t (S n)), P n p :=
fix rectS_fix n (p: t (S n)): P n p:=
  match p as p0 in t n0
  return match n0 as nn return t nn -> Type with
    |0 => fun _ => @ID |S n' => fun p' => P n' p'
  end p0 with
  |F1 k => P1 k
  |FS 0 pp => @case0 (fun f => P 0 (FS f)) pp
  |FS (S k) pp => PS k pp (rectS_fix k pp)
  end.

Definition rect2 (P: forall {n} (a b: t n), Type)
  (H0: forall n, P F1 F1)
  (H1: forall n (f: t n), P F1 (FS f))
  (H2: forall n (f: t n), P (FS f) F1)
  (HS: forall n (f g : t n), P f g -> P (FS f) (FS g)):
    forall n (a b: t n), P a b :=
fix rect2_fix n (a: t n): forall (b: t n), P a b :=
match a with
  |F1 m => fun (b: t (S m)) => match b as b' in t n'
                   return match n' as n0
                          return t n0 -> Type with
                            |0 => fun _ => @ID
                            |S n0 => fun b0 => P F1 b0
                          end b' with
                     |F1 m' => H0 m'
                     |FS m' b' => H1 m' b'
                   end
  |FS m a' => fun (b: t (S m)) => match b as b' in t n'
                      return match n' as n0
                             return t n0 -> Type with
                               |0 => fun _ => @ID
                               |S n0 => fun b0 =>
                                 forall (a0: t n0), P (FS a0) b0
                             end b' with
                         |F1 m' => fun aa => H2 m' aa
                         |FS m' b' => fun aa => HS m' aa b' (rect2_fix m' aa b')
                       end a'
end.
End SCHEMES.

(** [to_nat f] = p iff [f] is the p{^ th} element of [fin m]. *)
Fixpoint to_nat {m} (n : t m) : {i | i < m} :=
  match n in t k return {i | i< k} with
    |F1 j => exist (fun i => i< S j) 0 (Lt.lt_0_Sn j)
    |FS _ p => match to_nat p with |exist i P => exist _ (S i) (Lt.lt_n_S _ _ P) end
  end.

(** [of_nat p n] answers the p{^ th} element of [fin n] if p < n or a proof of
p >= n else *)
Fixpoint of_nat (p n : nat) : (t n) + { exists m, p = n + m } :=
  match n with
   |0 => inright _ (ex_intro (fun x => p = 0 + x) p (@eq_refl _ p))
   |S n' => match p with
      |0 => inleft _ (F1)
      |S p' => match of_nat p' n' with
        |inleft f => inleft _ (FS f)
        |inright arg => inright _ (match arg with |ex_intro m e =>
          ex_intro (fun x => S p' = S n' + x) m (f_equal S e) end)
      end
    end
  end.

(** [of_nat_lt p n H] answers the p{^ th} element of [fin n]
it behaves much better than [of_nat p n] on open term *)
Fixpoint of_nat_lt {p n : nat} : p < n -> t n :=
  match n with
    |0 => fun H : p < 0 => False_rect _ (Lt.lt_n_O p H)
    |S n' => match p with
      |0 => fun _ => @F1 n'
      |S p' => fun H => FS (of_nat_lt (Lt.lt_S_n _ _ H))
    end
  end.

Lemma of_nat_to_nat_inv {m} (p : t m) : of_nat_lt (proj2_sig (to_nat p)) = p.
Proof.
induction p.
 reflexivity.
 simpl; destruct (to_nat p). simpl. subst p; repeat f_equal. apply Peano_dec.le_unique.
Qed.

(** [weak p f] answers a function witch is the identity for the p{^  th} first
element of [fin (p + m)] and [FS (FS .. (FS (f k)))] for [FS (FS .. (FS k))]
with p FSs *)
Fixpoint weak {m}{n} p (f : t m -> t n) :
  t (p + m) -> t (p + n) :=
match p as p' return t (p' + m) -> t (p' + n) with
  |0 => f
  |S p' => fun x => match x in t n0 return
     match n0 with |0 => @ID |S n0' => n0' = p' + m -> t (S p' + n) end with
     |F1 n' => fun eq : n' = p' + m => F1
     |FS n' y => fun eq : n' = p' + m => FS (weak p' f (eq_rect _ t y _ eq))
  end (eq_refl _)
end.

(** The p{^ th} element of [fin m] viewed as the p{^ th} element of
[fin (m + n)] *)
Fixpoint L {m} n (p : t m) : t (m + n) :=
  match p with |F1 _ => F1 |FS _ p' => FS (L n p') end.

Lemma L_sanity {m} n (p : t m) : proj1_sig (to_nat (L n p)) = proj1_sig (to_nat p).
Proof.
induction p.
  reflexivity.
  simpl; destruct (to_nat (L n p)); simpl in *; rewrite IHp. now destruct (to_nat p).
Qed.

(** The p{^ th} element of [fin m] viewed as the p{^ th} element of
[fin (n + m)]
Really really ineficient !!! *)
Definition L_R {m} n (p : t m) : t (n + m).
induction n.
  exact p.
  exact ((fix LS k (p: t k) :=
    match p in t n0 return t (S n0) with
      |F1 _ => F1
      |FS _ p' => FS (LS _ p')
    end) _ IHn).
Defined.

(** The p{^ th} element of [fin m] viewed as the (n + p){^ th} element of
[fin (n + m)] *)
Fixpoint R {m} n (p : t m) : t (n + m) :=
  match n with |0 => p |S n' => FS (R n' p) end.

Lemma R_sanity {m} n (p : t m) : proj1_sig (to_nat (R n p)) = n + proj1_sig (to_nat p).
Proof.
induction n.
  reflexivity.
  simpl; destruct (to_nat (R n p)); simpl in *; rewrite IHn. now destruct (to_nat p).
Qed.

Fixpoint depair {m n} (o : t m) (p : t n) : t (m * n) :=
match o with
  |F1 m' => L (m' * n) p
  |FS m' o' => R n (depair o' p)
end.

Lemma depair_sanity {m n} (o : t m) (p : t n) :
  proj1_sig (to_nat (depair o p)) = n * (proj1_sig (to_nat o)) + (proj1_sig (to_nat p)).
induction o ; simpl.
  rewrite L_sanity. now rewrite Mult.mult_0_r.

  rewrite R_sanity. rewrite IHo.
  rewrite Plus.plus_assoc. destruct (to_nat o); simpl; rewrite Mult.mult_succ_r.
    now rewrite (Plus.plus_comm n).
Qed.