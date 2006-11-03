(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Bit vectors. Contribution by Jean Duprat (ENS Lyon). *)

Require Export Bool.
Require Export Sumbool.
Require Import Arith.

Open Local Scope nat_scope.

(** 
On s'inspire de List.v pour fabriquer les vecteurs de bits.
La dimension du vecteur est un paramètre trop important pour
se contenter de la fonction "length".
La première idée est de faire un record avec la liste et la longueur.
Malheureusement, cette verification a posteriori amene a faire
de nombreux lemmes pour gerer les longueurs.
La seconde idée est de faire un type dépendant dans lequel la
longueur est un paramètre de construction. Cela complique un
peu les inductions structurelles, la solution qui a ma préférence
est alors d'utiliser un terme de preuve comme définition, car le
mécanisme d'inférence du type du filtrage n'est pas aussi puissant que
celui implanté par les tactiques d'élimination.
*)

Section VECTORS.

(** 
Un vecteur est une liste de taille n d'éléments d'un ensemble A.
Si la taille est non nulle, on peut extraire la première composante et 
le reste du vecteur, la dernière composante ou rajouter ou enlever 
une composante (carry) ou repeter la dernière composante en fin de vecteur.
On peut aussi tronquer le vecteur de ses p dernières composantes ou
au contraire l'étendre (concaténer) d'un vecteur de longueur p.
Une fonction unaire sur A génère une fonction des vecteurs de taille n
dans les vecteurs de taille n en appliquant f terme à terme.
Une fonction binaire sur A génère une fonction des couples de vecteurs 
de taille n dans les vecteurs de taille n en appliquant f terme à terme.
*)

Variable A : Type.

Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall (a:A) (n:nat), vector n -> vector (S n).

Definition Vhead : forall n:nat, vector (S n) -> A.
Proof.
  intros n v; inversion v; exact a.
Defined.

Definition Vtail : forall n:nat, vector (S n) -> vector n.
Proof.
  intros n v; inversion v as [|_ n0 H0 H1]; exact H0.
Defined.

Definition Vlast : forall n:nat, vector (S n) -> A.
Proof.
  induction n as [| n f]; intro v.
  inversion v.
  exact a.
  
  inversion v as [| n0 a H0 H1].
  exact (f H0).
Defined.

Definition Vconst : forall (a:A) (n:nat), vector n.
Proof.
  induction n as [| n v].
  exact Vnil.

  exact (Vcons a n v).
Defined.

Lemma Vshiftout : forall n:nat, vector (S n) -> vector n.
Proof.
  induction n as [| n f]; intro v.
  exact Vnil.
  
  inversion v as [| a n0 H0 H1].
  exact (Vcons a n (f H0)).
Defined.

Lemma Vshiftin : forall n:nat, A -> vector n -> vector (S n).
Proof.
  induction n as [| n f]; intros a v.
  exact (Vcons a 0 v).
  
  inversion v as [| a0 n0 H0 H1 ].
  exact (Vcons a (S n) (f a H0)).
Defined.

Lemma Vshiftrepeat : forall n:nat, vector (S n) -> vector (S (S n)).
Proof.
  induction n as [| n f]; intro v.
  inversion v.
  exact (Vcons a 1 v).
  
  inversion v as [| a n0 H0 H1 ].
  exact (Vcons a (S (S n)) (f H0)).
Defined.

Lemma Vtrunc : forall n p:nat, n > p -> vector n -> vector (n - p).
Proof.
  induction p as [| p f]; intros H v.
  rewrite <- minus_n_O.
  exact v.
  
  apply (Vshiftout (n - S p)).
  
  rewrite minus_Sn_m.
  apply f.
  auto with *.
  exact v.
  auto with *.
Defined.

Lemma Vextend : forall n p:nat, vector n -> vector p -> vector (n + p).
Proof.
  induction n as [| n f]; intros p v v0.
  simpl in |- *; exact v0.
  
  inversion v as [| a n0 H0 H1].
  simpl in |- *; exact (Vcons a (n + p) (f p H0 v0)).
Defined.

Variable f : A -> A.

Lemma Vunary : forall n:nat, vector n -> vector n.
Proof.
  induction n as [| n g]; intro v.
  exact Vnil.
  
  inversion v as [| a n0 H0 H1].
  exact (Vcons (f a) n (g H0)).
Defined.

Variable g : A -> A -> A.

Lemma Vbinary : forall n:nat, vector n -> vector n -> vector n.
Proof.
  induction n as [| n h]; intros v v0.
  exact Vnil.
  
  inversion v as [| a n0 H0 H1]; inversion v0 as [| a0 n1 H2 H3].
  exact (Vcons (g a a0) n (h H0 H2)).
Defined.

Definition Vid : forall n:nat, vector n -> vector n.
Proof.
  destruct n; intro X.
  exact Vnil.
  exact (Vcons (Vhead _ X) _ (Vtail _ X)).
Defined.

Lemma Vid_eq : forall (n:nat) (v:vector n), v=(Vid n v).
Proof.
  destruct v; auto.
Qed.

Lemma VSn_eq :
  forall (n : nat) (v : vector (S n)), v = Vcons (Vhead _ v) _ (Vtail _ v).
Proof.
  intros.
  exact (Vid_eq _ v).
Qed.

Lemma V0_eq : forall (v : vector 0), v = Vnil.
Proof.
  intros.
  exact (Vid_eq _ v).
Qed.

End VECTORS.

(* suppressed: incompatible with Coq-Art book 
Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].
*)

Section BOOLEAN_VECTORS.

(**
Un vecteur de bits est un vecteur sur l'ensemble des booléens de longueur fixe. 
ATTENTION : le stockage s'effectue poids FAIBLE en tête.
On en extrait le bit  de poids faible (head) et la fin du vecteur (tail).
On calcule la négation d'un vecteur, le et, le ou et le xor bit à bit de 2 vecteurs.
On calcule les décalages d'une position vers la gauche (vers les poids forts, on
utilise donc Vshiftout, vers la droite (vers les poids faibles, on utilise Vshiftin) en 
insérant un bit 'carry' (logique) ou en répétant le bit de poids fort (arithmétique).
ATTENTION : Tous les décalages prennent la taille moins un comme paramètre
(ils ne travaillent que sur des vecteurs au moins de longueur un).
*)

Definition Bvector := vector bool.

Definition Bnil := @Vnil bool.

Definition Bcons := @Vcons bool.

Definition Bvect_true := Vconst bool true.

Definition Bvect_false := Vconst bool false.

Definition Blow := Vhead bool.

Definition Bhigh := Vtail bool.

Definition Bsign := Vlast bool.

Definition Bneg := Vunary bool negb.

Definition BVand := Vbinary bool andb.

Definition BVor := Vbinary bool orb.

Definition BVxor := Vbinary bool xorb.

Definition BshiftL (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bcons carry n (Vshiftout bool n bv).

Definition BshiftRl (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bhigh (S n) (Vshiftin bool (S n) carry bv).

Definition BshiftRa (n:nat) (bv:Bvector (S n)) :=
  Bhigh (S n) (Vshiftrepeat bool n bv).

Fixpoint BshiftL_iter (n:nat) (bv:Bvector (S n)) (p:nat) {struct p} :
  Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftL n (BshiftL_iter n bv p') false
  end.

Fixpoint BshiftRl_iter (n:nat) (bv:Bvector (S n)) (p:nat) {struct p} :
  Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftRl n (BshiftRl_iter n bv p') false
  end.

Fixpoint BshiftRa_iter (n:nat) (bv:Bvector (S n)) (p:nat) {struct p} :
  Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftRa n (BshiftRa_iter n bv p')
  end.

End BOOLEAN_VECTORS.
