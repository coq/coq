(* -*- coding: utf-8 -*- *)
(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence du projet : LGPL version 2.1

 *************************************************************************)

Require Arith.
Require PolyList.
Require Bool.
Require ZArith_base.
Require Import OmegaLemmas.

Open Scope Z_scope.

(* \subsection{Definition of basic types} *)

(* \subsubsection{Environment of propositions (lists) *)
Inductive PropList : Type := 
  Pnil : PropList | Pcons : Prop -> PropList -> PropList.

(* Access function for the environment with a default *)
Fixpoint nthProp [n:nat; l:PropList] : Prop -> Prop :=
  [default]Cases n l of
    O (Pcons x l') => x
  | O other => default
  | (S m) Pnil => default
  | (S m) (Pcons x t) => (nthProp m t default)
  end.
   
(* \subsubsection{Définition of reified integer expressions}
   Terms are either:
   \begin{itemize}
   \item integers [Tint]
   \item variables [Tvar]
   \item operation over integers (addition, product, opposite, subtraction)
   The last two are translated in additions and products. *)

Inductive term : Set :=
   Tint : Z -> term
 | Tplus : term -> term -> term
 | Tmult : term -> term -> term
 | Tminus : term -> term -> term
 | Topp : term -> term
 | Tvar : nat -> term
.

Delimits Scope romega_scope with term.
Infix 4 "+" Tplus : romega_scope V8only.
Infix 4 "*" Tmult : romega_scope V8only.
Infix 4 "-" Tminus : romega_scope V8only.
Notation "- x" := (Topp x) (at level 0) : romega_scope V8only.
V8Notation "[ x ]" := (Tvar x) (at level 1) : romega_scope.

(* \subsubsection{Definition of reified goals} *)
(* Very restricted definition of handled predicates that should be extended
   to cover a wider set of operations.
   Taking care of negations and disequations require solving more than a
   goal in parallel. This is a major improvement over previous versions. *)

Inductive proposition : Set :=
  EqTerm : term -> term -> proposition (* egalité entre termes *)
| LeqTerm : term -> term -> proposition (* plus petit ou egal *)
| TrueTerm : proposition (* vrai *)
| FalseTerm : proposition (* faux *)
| Tnot : proposition -> proposition (* négation *)
| GeqTerm : term -> term -> proposition
| GtTerm : term -> term -> proposition
| LtTerm : term -> term -> proposition
| NeqTerm: term -> term -> proposition
| Tor : proposition -> proposition -> proposition
| Tand : proposition -> proposition -> proposition
| Timp : proposition -> proposition -> proposition
| Tprop : nat -> proposition
.

(* Definition of goals as a list of hypothesis *)
Notation hyps := (list proposition).      

(* Definition of lists of subgoals  (set of open goals) *)
Notation lhyps := (list hyps).

(* a syngle goal packed in a subgoal list *)
Notation singleton :=  [a: hyps] (cons a (nil hyps)).

(* an absurd goal *)
Definition absurd := (cons FalseTerm (nil proposition)).

(* \subsubsection{Traces for merging equations}
   This inductive type describes how the monomial of two equations should be
   merged when the equations are added.

   For [F_equal], both equations have the same head variable and coefficient
   must be added, furthermore if coefficients are opposite, [F_cancel] should
   be used to collapse the term. [F_left] and [F_right] indicate which monomial
   should be put first in the result *)

Inductive t_fusion : Set :=
    F_equal : t_fusion | F_cancel : t_fusion
  | F_left : t_fusion  | F_right : t_fusion.

(* \subsubsection{Rewriting steps to normalize terms} *)
Inductive step : Set := 
 (* apply the rewriting steps to both subterms of an operation *)
 | C_DO_BOTH : step -> step -> step
 (* apply the rewriting step to the first branch *)
 | C_LEFT : step -> step
 (* apply the rewriting step to the second branch *)
 | C_RIGHT : step -> step
 (* apply two steps consecutively to a term *)
 | C_SEQ : step -> step -> step
 (* empty step *)
 | C_NOP : step
 (* the following operations correspond to actual rewriting *)
 | C_OPP_PLUS : step
 | C_OPP_OPP : step
 | C_OPP_MULT_R : step
 | C_OPP_ONE : step
 (* This is a special step that reduces the term (computation) *)
 | C_REDUCE : step
 | C_MULT_PLUS_DISTR : step
 | C_MULT_OPP_LEFT : step
 | C_MULT_ASSOC_R : step
 | C_PLUS_ASSOC_R : step
 | C_PLUS_ASSOC_L : step
 | C_PLUS_PERMUTE : step
 | C_PLUS_SYM : step
 | C_RED0 : step
 | C_RED1 : step
 | C_RED2 : step
 | C_RED3 : step
 | C_RED4 : step
 | C_RED5 : step
 | C_RED6 : step
 | C_MULT_ASSOC_REDUCED : step
 | C_MINUS :step
 | C_MULT_SYM : step
.

(* \subsubsection{Omega steps} *)
(* The following inductive type describes steps as they can be found in
   the trace coming from the decision procedure Omega. *)

Inductive t_omega : Set :=
   (* n = 0 n!= 0 *)
 | O_CONSTANT_NOT_NUL : nat -> t_omega
 | O_CONSTANT_NEG : nat -> t_omega
   (* division et approximation of an equation *)
 | O_DIV_APPROX : Z -> Z -> term -> nat -> t_omega -> nat -> t_omega
   (* no solution because no exact division *)
 | O_NOT_EXACT_DIVIDE :  Z -> Z -> term -> nat -> nat -> t_omega
   (* exact division *)
 | O_EXACT_DIVIDE : Z -> term -> nat -> t_omega -> nat -> t_omega
 | O_SUM : Z -> nat -> Z -> nat -> (list t_fusion) -> t_omega -> t_omega
 | O_CONTRADICTION : nat -> nat -> nat -> t_omega
 | O_MERGE_EQ : nat -> nat -> nat -> t_omega -> t_omega
 | O_SPLIT_INEQ : nat -> nat -> t_omega -> t_omega -> t_omega
 | O_CONSTANT_NUL : nat -> t_omega 
 | O_NEGATE_CONTRADICT : nat -> nat -> t_omega
 | O_NEGATE_CONTRADICT_INV : nat -> nat -> nat -> t_omega
 | O_STATE : Z -> step -> nat -> nat -> t_omega -> t_omega.

(* \subsubsection{Règles pour normaliser les hypothèses} *)
(* Ces règles indiquent comment normaliser les propositions utiles 
   de chaque hypothèse utile avant la décomposition des hypothèses et 
   incluent l'étape d'inversion pour la suppression des négations *)
Inductive p_step : Set :=
  P_LEFT : p_step -> p_step
| P_RIGHT :  p_step -> p_step
| P_INVERT :  step -> p_step
| P_STEP : step -> p_step
| P_NOP : p_step
.
(* Liste des normalisations a effectuer : avec un constructeur dans le
   type [p_step] permettant
   de parcourir à la fois les branches gauches et droit, on pourrait n'avoir
   qu'une normalisation par hypothèse. Et comme toutes les hypothèses sont 
   utiles (sinon on ne les inclurait pas), on pourrait remplacer [h_step] 
   par une simple liste *)

Inductive h_step : Set := pair_step : nat -> p_step -> h_step.

(* \subsubsection{Règles pour décomposer les hypothèses} *)
(* Ce type permet de se diriger dans les constructeurs logiques formant les
   prédicats des hypothèses pour aller les décomposer. Ils permettent
   en particulier d'extraire une hypothèse d'une conjonction avec
   éventuellement le bon niveau de négations. *)

Inductive direction : Set :=
   D_left : direction
 | D_right : direction
 | D_mono : direction.

(* Ce type permet d'extraire les composants utiles des hypothèses : que ce
   soit des hypothèses générées par éclatement d'une disjonction, ou 
   des équations. Le constructeur terminal indique comment résoudre le système
   obtenu en recourrant au type de trace d'Omega [t_omega] *)

Inductive e_step : Set :=
   E_SPLIT : nat -> (list direction) -> e_step -> e_step -> e_step
 | E_EXTRACT : nat -> (list direction) -> e_step -> e_step
 | E_SOLVE : t_omega -> e_step.

(* \subsection{Egalité décidable efficace} *)
(* Pour chaque type de donnée réifié, on calcule un test d'égalité efficace.
   Ce n'est pas le cas de celui rendu par [Decide Equality].
   
   Puis on prouve deux théorèmes permettant d'éliminer de telles égalités :
   \begin{verbatim}
   (t1,t2: typ) (eq_typ t1 t2) = true -> t1 = t2.
   (t1,t2: typ) (eq_typ t1 t2) = false -> ~ t1 = t2.
   \end{verbatim} *)

(* Ces deux tactiques permettent de résoudre pas mal de cas. L'une pour
   les théorèmes positifs, l'autre pour les théorèmes négatifs *)

Tactic Definition absurd_case := Simpl; Intros; Discriminate.
Tactic Definition trivial_case := Unfold not; Intros; Discriminate.

(* \subsubsection{Entiers naturels} *)

Fixpoint eq_nat [t1,t2: nat] : bool := 
  Cases t1 of
    O => Cases t2 of O => true | _ => false end
  | (S n1)=> Cases t2 of O => false | (S n2)  => (eq_nat n1 n2) end
  end.

Theorem eq_nat_true : (t1,t2: nat) (eq_nat t1 t2) = true -> t1 = t2.

Induction t1; [
  Intro t2; Case t2; [ Trivial | absurd_case ]
| Intros n H t2; Case t2; 
    [ absurd_case |  Simpl; Intros; Rewrite (H n0); [ Trivial | Assumption]]].

Save.
  
Theorem eq_nat_false : (t1,t2: nat) (eq_nat t1 t2) = false -> ~t1 = t2.

Induction t1; [
  Intro t2; Case t2;
   [ Simpl;Intros; Discriminate | trivial_case ]
| Intros n H t2; Case t2; Simpl; Unfold not; Intros; [
    Discriminate
  | Elim (H n0 H0); Simplify_eq H1; Trivial]].

Save.
                                   

(* \subsubsection{Entiers positifs} *)

Fixpoint eq_pos [p1,p2 : positive] : bool := 
  Cases p1 of
    (xI n1) => Cases p2 of (xI n2) => (eq_pos n1 n2) | _ => false end
  | (xO n1) =>  Cases p2 of (xO n2) => (eq_pos n1 n2) | _ => false end
  | xH =>  Cases p2 of xH => true | _ => false end
  end.

Theorem eq_pos_true : (t1,t2: positive) (eq_pos t1 t2) = true -> t1 = t2.

Induction t1; [
  Intros p H t2; Case t2; [
    Simpl; Intros; Rewrite (H p0 H0); Trivial | absurd_case | absurd_case ]
| Intros p H t2; Case t2; [
    absurd_case | Simpl; Intros; Rewrite (H p0 H0); Trivial | absurd_case ]
| Intro t2; Case t2; [ absurd_case | absurd_case | Auto ]].

Save.
  
Theorem eq_pos_false : (t1,t2: positive) (eq_pos t1 t2) = false -> ~t1 = t2.

Induction t1; [
  Intros p H t2; Case t2; [
    Simpl; Unfold not; Intros; Elim (H p0 H0); Simplify_eq H1; Auto
  | trivial_case | trivial_case ]
| Intros p H t2; Case t2; [
    trivial_case 
  | Simpl; Unfold not; Intros; Elim (H p0 H0); Simplify_eq H1; Auto
  | trivial_case ]
| Intros t2; Case t2; [ trivial_case | trivial_case  | absurd_case ]].
Save.

(* \subsubsection{Entiers relatifs} *)

Definition eq_Z [z1,z2: Z] : bool :=
  Cases z1 of
     ZERO     => Cases z2 of ZERO => true | _ => false end
   | (POS p1) => Cases z2 of (POS p2) => (eq_pos p1 p2) | _ => false end
   | (NEG p1) => Cases z2 of (NEG p2) => (eq_pos p1 p2) | _ => false end
  end.

Theorem eq_Z_true : (t1,t2: Z) (eq_Z t1 t2) = true -> t1 = t2.

Induction t1; [
  Intros t2; Case t2; [ Auto | absurd_case | absurd_case ]
| Intros p t2; Case t2; [
    absurd_case | Simpl; Intros; Rewrite (eq_pos_true p p0 H); Trivial 
  | absurd_case ]
| Intros p t2; Case t2; [
    absurd_case | absurd_case
  | Simpl; Intros; Rewrite (eq_pos_true p p0 H); Trivial ]].

Save.

Theorem eq_Z_false : (t1,t2: Z) (eq_Z t1 t2) = false -> ~(t1 = t2).

Induction t1; [
  Intros t2; Case t2; [ absurd_case | trivial_case | trivial_case ]
| Intros p t2; Case t2; [
    absurd_case
  | Simpl; Unfold not; Intros; Elim (eq_pos_false p p0 H); Simplify_eq H0; Auto
  | trivial_case ]
| Intros p t2; Case t2; [
    absurd_case | trivial_case 
  | Simpl; Unfold not; Intros; Elim (eq_pos_false p p0 H); 
    Simplify_eq H0; Auto]].
Save.

(* \subsubsection{Termes réifiés} *)

Fixpoint eq_term [t1,t2: term] : bool := 
   Cases t1 of
      (Tint st1) =>
         Cases t2 of (Tint st2) => (eq_Z st1 st2) | _ => false end
    | (Tplus st11 st12) =>
         Cases t2 of
            (Tplus st21 st22) => 
               (andb (eq_term st11 st21) (eq_term st12 st22))
         | _ => false 
         end
    | (Tmult st11 st12) =>
         Cases t2 of
            (Tmult st21 st22) => 
               (andb (eq_term st11 st21) (eq_term st12 st22))
         | _ => false 
         end
    | (Tminus st11 st12) =>
         Cases t2 of
            (Tminus st21 st22) => 
               (andb (eq_term st11 st21) (eq_term st12 st22))
         | _ => false 
         end
    | (Topp st1) =>
         Cases t2 of (Topp st2) => (eq_term st1 st2) | _ => false end
    | (Tvar st1) =>
         Cases t2 of (Tvar st2) => (eq_nat st1 st2) | _ => false end
   end.  

Theorem eq_term_true : (t1,t2: term) (eq_term t1 t2) = true -> t1 = t2.


Induction t1; Intros until t2; Case t2; Try absurd_case; Simpl; [
  Intros; Elim eq_Z_true with 1 := H; Trivial
| Intros t21 t22 H3; Elim andb_prop with 1:= H3; Intros H4 H5; 
  Elim H with 1 := H4; Elim H0 with 1 := H5; Trivial
| Intros t21 t22 H3; Elim andb_prop with 1:= H3; Intros H4 H5;
  Elim H with 1 := H4; Elim H0 with 1 := H5; Trivial
| Intros t21 t22 H3; Elim andb_prop with 1:= H3; Intros H4 H5; 
  Elim H with 1 := H4; Elim H0 with 1 := H5; Trivial
| Intros t21 H3; Elim H with 1 := H3; Trivial
| Intros; Elim eq_nat_true with 1 := H; Trivial ].

Save.

Theorem eq_term_false : (t1,t2: term) (eq_term t1 t2) = false -> ~(t1 = t2).

Induction t1; [
  Intros z t2; Case t2; Try trivial_case; Simpl; Unfold not; Intros;
  Elim eq_Z_false with 1:=H; Simplify_eq H0; Auto
| Intros t11 H1 t12 H2 t2; Case t2; Try trivial_case; Simpl; Intros t21 t22 H3;
  Unfold not; Intro H4; Elim andb_false_elim with 1:= H3; Intros H5; 
  [ Elim H1 with 1 := H5; Simplify_eq H4; Auto |
    Elim H2 with 1 := H5; Simplify_eq H4; Auto ]
| Intros t11 H1 t12 H2 t2; Case t2; Try trivial_case; Simpl; Intros t21 t22 H3;
  Unfold not; Intro H4; Elim andb_false_elim with 1:= H3; Intros H5; 
  [ Elim H1 with 1 := H5; Simplify_eq H4; Auto |
    Elim H2 with 1 := H5; Simplify_eq H4; Auto ]
| Intros t11 H1 t12 H2 t2; Case t2; Try trivial_case; Simpl; Intros t21 t22 H3;
  Unfold not; Intro H4; Elim andb_false_elim with 1:= H3; Intros H5; 
  [ Elim H1 with 1 := H5; Simplify_eq H4; Auto |
    Elim H2 with 1 := H5; Simplify_eq H4; Auto ]
| Intros t11 H1 t2; Case t2; Try trivial_case; Simpl; Intros t21 H3;
  Unfold not; Intro H4; Elim H1 with 1 := H3; Simplify_eq H4; Auto 
| Intros n t2; Case t2; Try trivial_case; Simpl; Unfold not; Intros;
  Elim eq_nat_false with 1:=H; Simplify_eq H0; Auto ].

Save.

(* \subsubsection{Tactiques pour éliminer ces tests} 

   Si on se contente de faire un [Case (eq_typ t1 t2)] on perd 
   totalement dans chaque branche le fait que [t1=t2] ou [~t1=t2].

   Initialement, les développements avaient été réalisés avec les
   tests rendus par [Decide Equality], c'est à dire un test rendant
   des termes du type [{t1=t2}+{~t1=t2}]. Faire une élimination sur un 
   tel test préserve bien l'information voulue mais calculatoirement de
   telles fonctions sont trop lentes. *)

(* Le théorème suivant permet de garder dans les hypothèses la valeur
   du booléen lors de l'élimination. *)

Theorem bool_ind2 : 
   (P:(bool->Prop)) (b:bool)
     (b = true -> (P true))->
     (b = false -> (P false)) -> (P b).

Induction b; Auto.
Save.

(* Les tactiques définies si après se comportent exactement comme si on
   avait utilisé le test précédent et fait une elimination dessus. *)

Tactic Definition Elim_eq_term t1 t2 :=
  Pattern (eq_term t1 t2); Apply bool_ind2; Intro Aux; [
    Generalize (eq_term_true t1 t2 Aux); Clear Aux
  | Generalize (eq_term_false t1 t2 Aux); Clear Aux ].

Tactic Definition Elim_eq_Z t1 t2 :=
  Pattern (eq_Z t1 t2); Apply bool_ind2; Intro Aux; [
    Generalize (eq_Z_true t1 t2 Aux); Clear Aux
  | Generalize (eq_Z_false t1 t2 Aux); Clear Aux ].

Tactic Definition Elim_eq_pos t1 t2 :=
  Pattern (eq_pos t1 t2); Apply bool_ind2; Intro Aux; [
    Generalize (eq_pos_true t1 t2 Aux); Clear Aux
  | Generalize (eq_pos_false t1 t2 Aux); Clear Aux ].

(* \subsubsection{Comparaison sur Z} *)

(* Sujet très lié au précédent : on introduit la tactique d'élimination
   avec son théorème *)

Theorem relation_ind2 : 
   (P:(relation->Prop)) (b:relation)
     (b = EGAL -> (P EGAL))->
     (b = INFERIEUR -> (P INFERIEUR))->
     (b = SUPERIEUR -> (P SUPERIEUR)) -> (P b).

Induction b; Auto.
Save.

Tactic Definition Elim_Zcompare t1 t2 :=
  Pattern (Zcompare t1 t2); Apply relation_ind2.

(* \subsection{Interprétations}
   \subsubsection{Interprétation des termes dans Z} *)

Fixpoint interp_term [env:(list Z); t:term] : Z :=
  Cases t of
    (Tint x) => x
  | (Tplus t1 t2) => (Zplus (interp_term env t1) (interp_term env t2))
  | (Tmult t1 t2) => (Zmult (interp_term env t1) (interp_term env t2))
  | (Tminus t1 t2) => (Zminus (interp_term env t1) (interp_term env t2))
  | (Topp t) => (Zopp (interp_term env t))
  | (Tvar n) => (nth n env ZERO)
  end.

(* \subsubsection{Interprétation des prédicats} *) 
Fixpoint interp_proposition 
    [envp : PropList; env: (list Z); p:proposition] : Prop := 
  Cases p of
    (EqTerm t1 t2) => ((interp_term env t1) = (interp_term env t2))
  | (LeqTerm t1 t2) => `(interp_term env t1) <= (interp_term env t2)`
  | TrueTerm => True
  | FalseTerm => False
  | (Tnot p') => ~(interp_proposition envp env p')
  | (GeqTerm t1 t2) => `(interp_term env t1) >= (interp_term env t2)`
  | (GtTerm t1 t2) => `(interp_term env t1) > (interp_term env t2)`
  | (LtTerm t1 t2) => `(interp_term env t1) < (interp_term env t2)`
  | (NeqTerm t1 t2) => `(Zne (interp_term env t1) (interp_term env t2))`

  | (Tor p1 p2) => 
	(interp_proposition envp env p1) \/ (interp_proposition envp env p2)
  | (Tand p1 p2) =>
	(interp_proposition envp env p1) /\ (interp_proposition envp env p2)
  | (Timp p1 p2) =>
	(interp_proposition envp env p1) -> (interp_proposition envp env p2)
  | (Tprop n) => (nthProp n envp True)
  end.

(* \subsubsection{Inteprétation des listes d'hypothèses}
   \paragraph{Sous forme de conjonction}
   Interprétation sous forme d'une conjonction d'hypothèses plus faciles
   à manipuler individuellement *)

Fixpoint interp_hyps [envp: PropList; env : (list Z); l: hyps] : Prop :=
  Cases l of 
     nil => True
   | (cons p' l') => 
	(interp_proposition envp env p') /\ (interp_hyps envp env l')
  end.

(* \paragraph{sous forme de but}
   C'est cette interpétation que l'on utilise sur le but (car on utilise
   [Generalize] et qu'une conjonction est forcément lourde (répétition des
   types dans les conjonctions intermédiaires) *)

Fixpoint interp_goal_concl [c: proposition; envp: PropList;env : (list Z); l: hyps] : Prop :=
  Cases l of 
     nil => (interp_proposition envp env c)
   | (cons p' l') => 
	(interp_proposition envp env p') -> (interp_goal_concl c envp env l')
  end.

Notation interp_goal := (interp_goal_concl FalseTerm).

(* Les théorèmes qui suivent assurent la correspondance entre les deux
   interprétations. *)

Theorem goal_to_hyps : 
  (envp: PropList; env : (list Z); l: hyps) 
     ((interp_hyps envp env l) -> False) -> (interp_goal envp env l).

Induction l; [
  Simpl; Auto
| Simpl; Intros a l1 H1 H2 H3; Apply H1; Intro H4; Apply H2; Auto ].
Save.

Theorem hyps_to_goal : 
  (envp: PropList; env : (list Z); l: hyps) 
     (interp_goal envp env l) -> ((interp_hyps envp env l) -> False).

Induction l; Simpl; [
  Auto
| Intros; Apply H; Elim H1; Auto ].
Save.
      
(* \subsection{Manipulations sur les hypothèses} *)

(* \subsubsection{Définitions de base de stabilité pour la réflexion} *)
(* Une opération laisse un terme stable si l'égalité est préservée *)
Definition term_stable [f: term -> term] :=
 (e: (list Z); t:term) (interp_term e t) = (interp_term e (f t)).

(* Une opération est valide sur une hypothèse, si l'hypothèse implique le
   résultat de l'opération. \emph{Attention : cela ne concerne que des 
   opérations sur les hypothèses et non sur les buts (contravariance)}.
   On définit la validité pour une opération prenant une ou deux propositions
   en argument (cela suffit pour omega). *)

Definition valid1 [f: proposition -> proposition] :=
  (ep : PropList; e: (list Z)) (p1: proposition) 
    (interp_proposition ep e p1) -> (interp_proposition ep e (f p1)).

Definition valid2 [f: proposition -> proposition -> proposition] :=
  (ep : PropList; e: (list Z)) (p1,p2: proposition) 
    (interp_proposition ep e p1) -> (interp_proposition ep e p2) ->
      (interp_proposition ep e (f p1 p2)).

(* Dans cette notion de validité, la fonction prend directement une 
   liste de propositions et rend une nouvelle liste de proposition. 
   On reste contravariant *)

Definition valid_hyps [f: hyps -> hyps] :=
  (ep : PropList; e : (list Z))
    (lp: hyps) (interp_hyps ep e lp) -> (interp_hyps ep e (f lp)).

(* Enfin ce théorème élimine la contravariance et nous ramène à une 
   opération sur les buts *)

 Theorem valid_goal :
  (ep: PropList; env : (list Z); l: hyps; a : hyps -> hyps) 
    (valid_hyps a) -> (interp_goal ep env (a l)) -> (interp_goal ep env l).

Intros; Simpl; Apply goal_to_hyps; Intro H1;
Apply (hyps_to_goal ep env (a l) H0); Apply H; Assumption.
Save.

(* \subsubsection{Généralisation a des listes de buts (disjonctions)} *)


Fixpoint interp_list_hyps [envp: PropList; env: (list Z); l : lhyps] : Prop :=
   Cases l of
      nil => False
    | (cons h l') => (interp_hyps envp env h) \/ (interp_list_hyps envp env l')
   end.

Fixpoint interp_list_goal [envp: PropList; env: (list Z);l : lhyps] : Prop :=
   Cases l of
      nil => True
    | (cons h l') => (interp_goal envp env h) /\ (interp_list_goal envp env l')
   end.

Theorem list_goal_to_hyps : 
  (envp: PropList; env: (list Z); l: lhyps)
    ((interp_list_hyps envp env l) -> False) -> (interp_list_goal envp env l).

Induction l; Simpl; [
  Auto
| Intros h1 l1 H H1; Split; [
    Apply goal_to_hyps; Intro H2; Apply H1; Auto
  | Apply H; Intro H2; Apply H1; Auto ]].
Save.

Theorem list_hyps_to_goal : 
  (envp: PropList; env: (list Z); l: lhyps)
    (interp_list_goal envp env l) -> ((interp_list_hyps envp env l) -> False).

Induction l; Simpl; [
  Auto
|  Intros h1 l1 H (H1,H2) H3; Elim H3; Intro H4; [
     Apply hyps_to_goal with 1 := H1; Assumption
   | Auto ]].
Save.

Definition valid_list_hyps [f: hyps -> lhyps] :=
  (ep : PropList; e : (list Z)) (lp: hyps)
    (interp_hyps ep e lp) -> (interp_list_hyps ep e (f lp)).

Definition valid_list_goal [f: hyps -> lhyps] :=
  (ep : PropList; e : (list Z)) (lp: hyps) 
     (interp_list_goal ep e (f lp)) -> (interp_goal ep e lp) .

Theorem goal_valid : 
  (f: hyps -> lhyps) (valid_list_hyps f) -> (valid_list_goal f).

Unfold valid_list_goal; Intros f H ep e lp H1; Apply goal_to_hyps;
Intro H2; Apply list_hyps_to_goal with 1:=H1; Apply (H ep e lp); Assumption.
Save.
 
Theorem append_valid :
  (ep: PropList; e: (list Z)) (l1,l2:lhyps)
     (interp_list_hyps ep e l1) \/ (interp_list_hyps ep e l2) ->
     (interp_list_hyps ep e (app l1 l2)).

Intros ep e; Induction l1; [
  Simpl; Intros l2 [H | H]; [ Contradiction | Trivial ]
| Simpl; Intros h1 t1 HR l2 [[H | H] | H] ;[
    Auto
  | Right; Apply (HR l2); Left; Trivial
  | Right; Apply (HR l2); Right; Trivial ]].

Save.

(* \subsubsection{Opérateurs valides sur les hypothèses} *)

(* Extraire une hypothèse de la liste *)
Definition nth_hyps [n:nat; l: hyps] := (nth n l TrueTerm).

Theorem nth_valid :
  (ep: PropList; e: (list Z); i:nat; l: hyps) 
     (interp_hyps ep e l) -> (interp_proposition ep e (nth_hyps i l)).

Unfold nth_hyps; Induction i; [
  Induction l; Simpl; [ Auto | Intros; Elim H0; Auto ]
| Intros n H; Induction l;
    [ Simpl; Trivial | Intros; Simpl; Apply H; Elim H1; Auto ]].
Save.

(* Appliquer une opération (valide) sur deux hypothèses extraites de 
   la liste et ajouter le résultat à la liste. *)
Definition apply_oper_2 
  [i,j : nat; f : proposition -> proposition -> proposition ] :=
  [l: hyps] (cons (f (nth_hyps i l)  (nth_hyps j l)) l).

Theorem apply_oper_2_valid :
  (i,j : nat; f : proposition -> proposition -> proposition )
    (valid2 f) -> (valid_hyps (apply_oper_2 i j f)).

Intros i j f Hf; Unfold apply_oper_2 valid_hyps; Simpl; Intros lp Hlp; Split;
  [ Apply Hf; Apply nth_valid; Assumption | Assumption].
Save.

(* Modifier une hypothèse par application d'une opération valide *)

Fixpoint apply_oper_1 [i:nat] : (proposition -> proposition) -> hyps -> hyps :=
  [f : (proposition -> proposition); l : hyps] 
    Cases l of 
       nil => (nil proposition)
    | (cons p l') =>
	 Cases i of
           O => (cons (f p) l')
         | (S j) => (cons p (apply_oper_1 j f l'))
         end
    end.

Theorem apply_oper_1_valid :
  (i : nat; f : proposition -> proposition )
    (valid1 f) -> (valid_hyps (apply_oper_1 i f)).

Unfold valid_hyps; Intros i f Hf ep e; Elim i; [
  Intro lp; Case lp; [
    Simpl; Trivial
  | Simpl; Intros p l' (H1, H2); Split; [ Apply Hf with 1:=H1 | Assumption ]]
| Intros n Hrec lp; Case lp; [
    Simpl; Auto
  | Simpl; Intros p l' (H1, H2); 
    Split; [ Assumption | Apply Hrec; Assumption ]]].

Save.

(* \subsubsection{Manipulations de termes} *)
(* Les fonctions suivantes permettent d'appliquer une fonction de
   réécriture sur un sous terme du terme principal. Avec la composition,
   cela permet de construire des réécritures complexes proches des 
   tactiques de conversion *)

Definition apply_left [f: term -> term; t : term]:= 
  Cases t of
    (Tplus x y) => (Tplus (f x) y)
  | (Tmult x y) => (Tmult (f x) y)
  | (Topp x) => (Topp (f x))
  | x => x
  end.

Definition apply_right [f: term -> term; t : term]:= 
  Cases t of
    (Tplus x y) => (Tplus x (f y))
  | (Tmult x y) => (Tmult x (f y))
  | x => x
  end.

Definition apply_both [f,g: term -> term; t : term]:= 
  Cases t of
    (Tplus x y) => (Tplus (f x) (g y))
  | (Tmult x y) => (Tmult (f x) (g y))
  | x => x
  end.

(* Les théorèmes suivants montrent la stabilité (conditionnée) des 
   fonctions. *)

Theorem apply_left_stable :
  (f: term -> term) (term_stable f) -> (term_stable (apply_left f)).

Unfold term_stable; Intros f H e t; Case t; Auto; Simpl; 
Intros;  Elim H; Trivial.
Save.

Theorem apply_right_stable :
  (f: term -> term) (term_stable f) -> (term_stable (apply_right f)).

Unfold term_stable; Intros f H e t; Case t; Auto; Simpl; 
Intros t0 t1; Elim H; Trivial.
Save.

Theorem apply_both_stable :
  (f,g: term -> term) (term_stable f) -> (term_stable g) -> 
     (term_stable (apply_both f g)).

Unfold term_stable; Intros f g H1 H2 e t; Case t; Auto; Simpl; 
Intros t0 t1; Elim H1; Elim H2; Trivial.
Save.

Theorem compose_term_stable :
  (f,g: term -> term) (term_stable f) -> (term_stable g) -> 
    (term_stable [t: term](f (g t))).

Unfold term_stable; Intros f g Hf Hg e t; Elim Hf; Apply Hg.
Save.

(* \subsection{Les règles de réécriture} *)
(* Chacune des règles de réécriture est accompagnée par sa preuve de 
   stabilité. Toutes ces preuves ont la même forme : il faut analyser 
   suivant la forme du terme (élimination de chaque Case). On a besoin d'une
   élimination uniquement dans les cas d'utilisation d'égalité décidable. 

   Cette tactique itère la décomposition des Case. Elle est
   constituée de deux fonctions s'appelant mutuellement :
   \begin{itemize} 
    \item une fonction d'enrobage qui lance la recherche sur le but,
    \item une fonction récursive qui décompose ce but. Quand elle a trouvé un
          Case, elle l'élimine. 
   \end{itemize}  
   Les motifs sur les cas sont très imparfaits et dans certains cas, il
   semble que cela ne marche pas. On aimerait plutot un motif de la
   forme [ Case (?1 :: T) of _ end ] permettant de s'assurer que l'on 
   utilise le bon type.

   Chaque élimination introduit correctement exactement le nombre d'hypothèses
   nécessaires et conserve dans le cas d'une égalité la connaissance du
   résultat du test en faisant la réécriture. Pour un test de comparaison,
   on conserve simplement le résultat.

   Cette fonction déborde très largement la résolution des réécritures
   simples et fait une bonne partie des preuves des pas de Omega.
*)

(* \subsubsection{La tactique pour prouver la stabilité} *)

Recursive Tactic Definition loop t := (
  Match t With
  (* Global *)
    [(?1 = ?2)] -> (loop ?1) Orelse (loop ?2)
  | [ ? -> ?1 ] ->  (loop ?1)
  (* Interpretations *)
  | [ (interp_hyps ? ? ?1) ] -> (loop ?1)
  | [ (interp_list_hyps ? ? ?1) ] -> (loop ?1)
  | [ (interp_proposition ? ? ?1) ] -> (loop ?1)
  | [ (interp_term ? ?1) ] -> (loop ?1)
  (* Propositions *)
  | [(EqTerm ?1 ?2)] -> (loop ?1) Orelse (loop ?2)
  | [(LeqTerm ?1 ?2)] -> (loop ?1) Orelse (loop ?2)
  (* Termes *)
  | [(Tplus ?1 ?2)] -> (loop ?1) Orelse (loop ?2)
  | [(Tminus ?1 ?2)] -> (loop ?1) Orelse (loop ?2)
  | [(Tmult ?1 ?2)] -> (loop ?1) Orelse (loop ?2)
  | [(Topp ?1)] -> (loop ?1)
  | [(Tint ?1)] -> (loop ?1)
  (* Eliminations *)
  |  [(Cases ?1 of
        | (EqTerm _ _) => ?
        | (LeqTerm _ _) => ?
        | TrueTerm => ?
        | FalseTerm => ?
        | (Tnot _) => ?
        | (GeqTerm _ _) => ?
        | (GtTerm _ _) => ?
        | (LtTerm _ _) => ?
        | (NeqTerm _ _) => ?
        | (Tor _ _) => ?
        | (Tand _ _) => ?
        | (Timp _ _) => ?
        | (Tprop _) => ?
        end)] -> 
       (Case ?1; [ Intro; Intro | Intro; Intro | Idtac | Idtac 
                 | Intro | Intro; Intro | Intro; Intro | Intro; Intro
                 | Intro; Intro
                 | Intro;Intro | Intro;Intro | Intro;Intro | Intro  ]);
        Auto; Simplify
  | [(Cases ?1 of
        (Tint _) => ?
      | (Tplus _ _) => ?
      | (Tmult _ _) => ?
      | (Tminus _ _) => ?
      | (Topp _) => ?
      | (Tvar _) => ?
      end)] -> 
       (Case ?1; [ Intro | Intro; Intro | Intro; Intro | Intro; Intro | 
                   Intro | Intro ]); Auto; Simplify
  | [(Cases (Zcompare ?1 ?2) of
        EGAL => ?
      | INFERIEUR => ?
      | SUPERIEUR => ?
      end)] -> 
       (Elim_Zcompare ?1 ?2) ; Intro ; Auto; Simplify
  | [(Cases ?1 of ZERO => ? | (POS _) => ? | (NEG _) => ? end)] -> 
       (Case ?1; [ Idtac | Intro | Intro ]); Auto; Simplify
  | [(if (eq_Z ?1 ?2) then ? else ?)] -> 
       ((Elim_eq_Z ?1 ?2); Intro H; [Rewrite H; Clear H | Clear H]);
       Simpl; Auto; Simplify
  | [(if (eq_term ?1 ?2) then ? else ?)] -> 
       ((Elim_eq_term ?1 ?2); Intro H; [Rewrite H; Clear H | Clear H]); 
       Simpl; Auto; Simplify
  | [(if (eq_pos ?1 ?2) then ? else ?)] -> 
       ((Elim_eq_pos ?1 ?2); Intro H; [Rewrite H; Clear H | Clear H]);
       Simpl; Auto; Simplify
  | _ -> Fail)
And Simplify := (
  Match Context With [|- ?1 ] -> Try (loop ?1) | _ -> Idtac).


Tactic Definition ProveStable x th :=
  (Match x With [?1] -> Unfold term_stable ?1; Intros; Simplify; Simpl; Apply th).

(* \subsubsection{Les règles elle mêmes} *)
Definition Tplus_assoc_l [t: term] :=
  Cases t of
    (Tplus n (Tplus m p)) => (Tplus (Tplus n m) p)
  | _ => t
  end.

Theorem  Tplus_assoc_l_stable : (term_stable  Tplus_assoc_l).

(ProveStable Tplus_assoc_l Zplus_assoc_l).
Save.

Definition Tplus_assoc_r [t: term] :=
  Cases t of
    (Tplus (Tplus n m) p) => (Tplus n (Tplus m p))
  | _ => t
  end.

Theorem  Tplus_assoc_r_stable : (term_stable  Tplus_assoc_r).

(ProveStable Tplus_assoc_r Zplus_assoc_r).
Save.

Definition Tmult_assoc_r [t: term] :=
  Cases t of
    (Tmult (Tmult n m) p) => (Tmult n (Tmult m p))
  | _ => t
  end.

Theorem  Tmult_assoc_r_stable : (term_stable  Tmult_assoc_r).

(ProveStable Tmult_assoc_r Zmult_assoc_r).
Save.

Definition Tplus_permute [t: term] :=
  Cases t of
    (Tplus n (Tplus m p)) => (Tplus m (Tplus n p))
  | _ => t
  end.

Theorem  Tplus_permute_stable : (term_stable  Tplus_permute).

(ProveStable Tplus_permute Zplus_permute).
Save.

Definition Tplus_sym [t: term] :=
  Cases t of
    (Tplus x y) => (Tplus y x)
  | _ => t
  end.

Theorem Tplus_sym_stable : (term_stable Tplus_sym).

(ProveStable Tplus_sym Zplus_sym).
Save.

Definition Tmult_sym [t: term] :=
  Cases t of
    (Tmult x y) => (Tmult y x)
  | _ => t
  end.

Theorem Tmult_sym_stable : (term_stable Tmult_sym).

(ProveStable Tmult_sym Zmult_sym).
Save.

Definition T_OMEGA10 [t: term] :=
  Cases t of
    (Tplus (Tmult (Tplus (Tmult v (Tint c1)) l1) (Tint k1))
           (Tmult (Tplus (Tmult v' (Tint c2)) l2) (Tint k2))) =>
	Case (eq_term v v') of
	    (Tplus (Tmult v (Tint (Zplus (Zmult c1 k1) (Zmult c2 k2)))) 
                   (Tplus (Tmult l1 (Tint k1)) (Tmult l2 (Tint k2))))
           t
        end
  | _ => t
  end.

Theorem  T_OMEGA10_stable : (term_stable  T_OMEGA10).

(ProveStable T_OMEGA10 OMEGA10).
Save.

Definition T_OMEGA11 [t: term] :=
  Cases t of
    (Tplus (Tmult (Tplus (Tmult v1 (Tint c1)) l1) (Tint k1)) l2) =>
	(Tplus (Tmult v1 (Tint (Zmult c1 k1))) (Tplus (Tmult l1 (Tint k1)) l2))
  | _ => t
  end.

Theorem  T_OMEGA11_stable : (term_stable  T_OMEGA11).

(ProveStable T_OMEGA11 OMEGA11).
Save.

Definition T_OMEGA12 [t: term] :=
  Cases t of
    (Tplus l1 (Tmult (Tplus (Tmult v2 (Tint c2)) l2) (Tint k2))) =>
        (Tplus (Tmult v2 (Tint (Zmult c2 k2))) (Tplus l1 (Tmult l2 (Tint k2))))
  | _ => t
  end.

Theorem  T_OMEGA12_stable : (term_stable  T_OMEGA12).

(ProveStable T_OMEGA12 OMEGA12).
Save. 

Definition T_OMEGA13 [t: term] :=
  Cases t of
    (Tplus (Tplus (Tmult v (Tint (POS x))) l1) 
	   (Tplus (Tmult v' (Tint (NEG x'))) l2)) =>
	Case (eq_term v v') of
	  Case (eq_pos x x') of
	    (Tplus l1 l2)
            t
	  end
	  t
	end
  | (Tplus (Tplus (Tmult v (Tint (NEG x))) l1) 
	   (Tplus (Tmult v' (Tint (POS x'))) l2)) =>
	Case (eq_term v v') of
	  Case (eq_pos x x') of
	    (Tplus l1 l2)
             t
	  end
	  t
	end

  | _ => t
  end.

Theorem  T_OMEGA13_stable : (term_stable  T_OMEGA13).

Unfold term_stable T_OMEGA13; Intros; Simplify; Simpl; 
  [ Apply OMEGA13 | Apply OMEGA14 ].
Save.

Definition T_OMEGA15 [t: term] :=
  Cases t of
    (Tplus (Tplus (Tmult v (Tint c1)) l1) 
	   (Tmult (Tplus (Tmult v' (Tint c2)) l2) (Tint k2))) =>
	Case (eq_term v v') of
	  (Tplus (Tmult v (Tint (Zplus c1 (Zmult c2 k2))))
	                  (Tplus l1 (Tmult l2 (Tint k2))))
	  t
	end
  | _ => t
  end.

Theorem  T_OMEGA15_stable : (term_stable  T_OMEGA15).

(ProveStable T_OMEGA15 OMEGA15).
Save.

Definition T_OMEGA16 [t: term] :=
  Cases t of
    (Tmult (Tplus (Tmult v (Tint c)) l) (Tint k)) =>
       (Tplus (Tmult v (Tint (Zmult c k))) (Tmult l (Tint k)))
  | _ => t
  end.


Theorem  T_OMEGA16_stable : (term_stable  T_OMEGA16).

(ProveStable T_OMEGA16 OMEGA16).
Save.

Definition Tred_factor5 [t: term] := 
   Cases t of
      (Tplus (Tmult x (Tint ZERO)) y) => y
   | _ => t
   end.

Theorem Tred_factor5_stable : (term_stable  Tred_factor5).


(ProveStable Tred_factor5 Zred_factor5).
Save.

Definition Topp_plus [t: term] :=
  Cases t of
    (Topp (Tplus x y)) => (Tplus (Topp x) (Topp y))
  | _ => t
  end.

Theorem Topp_plus_stable : (term_stable Topp_plus).

(ProveStable Topp_plus Zopp_Zplus).
Save.


Definition Topp_opp [t: term] :=
  Cases t of
    (Topp (Topp x)) => x
  | _ => t
  end.

Theorem Topp_opp_stable : (term_stable Topp_opp).

(ProveStable Topp_opp Zopp_Zopp).
Save.

Definition Topp_mult_r [t: term] :=
  Cases t of
    (Topp (Tmult x (Tint k))) => (Tmult x (Tint (Zopp k)))
  | _ => t
  end.

Theorem Topp_mult_r_stable : (term_stable Topp_mult_r).

(ProveStable Topp_mult_r Zopp_Zmult_r).
Save.

Definition Topp_one [t: term] :=
  Cases t of
    (Topp x) => (Tmult x (Tint `-1`))
  | _ => t
  end.

Theorem Topp_one_stable : (term_stable Topp_one).

(ProveStable Topp_one Zopp_one).
Save.

Definition Tmult_plus_distr  [t: term] :=
  Cases t of
    (Tmult (Tplus n m) p) => (Tplus (Tmult n p) (Tmult m p))
  | _ => t
  end.

Theorem Tmult_plus_distr_stable : (term_stable Tmult_plus_distr).

(ProveStable Tmult_plus_distr Zmult_plus_distr).
Save.

Definition Tmult_opp_left [t: term] :=
  Cases t of
    (Tmult (Topp x) (Tint y)) => (Tmult x (Tint (Zopp y)))
  | _ => t
  end.

Theorem Tmult_opp_left_stable : (term_stable Tmult_opp_left).

(ProveStable Tmult_opp_left Zmult_Zopp_left).
Save.

Definition Tmult_assoc_reduced [t: term] :=
  Cases t of
    (Tmult (Tmult n (Tint m)) (Tint p)) => (Tmult n (Tint (Zmult m p)))
  | _ => t
  end.

Theorem  Tmult_assoc_reduced_stable : (term_stable  Tmult_assoc_reduced).

(ProveStable Tmult_assoc_reduced Zmult_assoc_r).
Save.

Definition Tred_factor0 [t: term] := (Tmult t (Tint `1`)).

Theorem  Tred_factor0_stable : (term_stable  Tred_factor0).

(ProveStable Tred_factor0 Zred_factor0).
Save.

Definition Tred_factor1 [t: term] :=
  Cases t of
    (Tplus x y) => 
	Case (eq_term x y) of
	  (Tmult x (Tint `2`))
	  t
        end
  | _ => t
  end.

Theorem  Tred_factor1_stable : (term_stable  Tred_factor1).

(ProveStable Tred_factor1 Zred_factor1).
Save.

Definition Tred_factor2 [t: term] :=
  Cases t of
    (Tplus x (Tmult y (Tint k))) => 
	Case (eq_term x y) of
	  (Tmult x (Tint (Zplus `1` k)))
	  t
        end
  | _ => t
  end.

(* Attention : il faut rendre opaque [Zplus] pour éviter que la tactique
   de simplification n'aille trop loin et défasse [Zplus 1 k] *)

Opaque Zplus.

Theorem  Tred_factor2_stable : (term_stable  Tred_factor2).
(ProveStable Tred_factor2 Zred_factor2).
Save.

Definition Tred_factor3 [t: term] :=
  Cases t of
    (Tplus (Tmult x (Tint k)) y) => 
	Case (eq_term x y) of
	  (Tmult x (Tint `1+k`))
	  t
        end
  | _ => t
  end.

Theorem  Tred_factor3_stable : (term_stable  Tred_factor3).

(ProveStable Tred_factor3 Zred_factor3).
Save.


Definition Tred_factor4 [t: term] :=
  Cases t of
    (Tplus (Tmult x (Tint k1)) (Tmult y (Tint k2))) => 
	Case (eq_term x y) of
	  (Tmult x (Tint `k1+k2`))
	  t
        end
  | _ => t
  end.

Theorem  Tred_factor4_stable : (term_stable  Tred_factor4).

(ProveStable Tred_factor4 Zred_factor4).
Save.

Definition Tred_factor6 [t: term] := (Tplus t (Tint `0`)).

Theorem  Tred_factor6_stable : (term_stable  Tred_factor6).

(ProveStable Tred_factor6 Zred_factor6).
Save.

Transparent Zplus.

Definition Tminus_def [t:term] :=
  Cases t of
    (Tminus x y) => (Tplus x (Topp y))
  | _ => t
  end.

Theorem  Tminus_def_stable : (term_stable  Tminus_def).

(* Le théorème ne sert à rien. Le but est prouvé avant. *)
(ProveStable Tminus_def False).
Save.

(* \subsection{Fonctions de réécriture complexes} *)

(* \subsubsection{Fonction de réduction} *)
(* Cette fonction réduit un terme dont la forme normale est un entier. Il
   suffit pour cela d'échanger le constructeur [Tint] avec les opérateurs
   réifiés. La réduction est ``gratuite''.  *)

Fixpoint reduce [t:term] : term :=
  Cases t of
     (Tplus x y) =>
	 Cases (reduce x) of
	   (Tint x') =>
	      Cases (reduce y) of
	        (Tint y') => (Tint (Zplus x' y'))
              | y' => (Tplus (Tint x') y')
              end
         | x' => (Tplus x' (reduce y))
	 end
  | (Tmult x y) =>
	 Cases (reduce x) of
	   (Tint x') =>
	      Cases (reduce y) of
	        (Tint y') => (Tint (Zmult x' y'))
              | y' => (Tmult (Tint x') y')
              end
         | x' => (Tmult x' (reduce y))
	 end
  | (Tminus x y) =>
	 Cases (reduce x) of
	   (Tint x') =>
	      Cases (reduce y) of
	        (Tint y') => (Tint (Zminus x' y'))
              | y' => (Tminus (Tint x') y')
              end
         | x' => (Tminus x' (reduce y))
	 end
  | (Topp x) =>
        Cases (reduce x) of
	  (Tint x') => (Tint (Zopp x'))
	| x' => (Topp x')
	end
  | _ => t
  end.

Theorem reduce_stable : (term_stable reduce).

Unfold term_stable; Intros e t; Elim t; Auto; 
Try (Intros t0 H0 t1 H1; Simpl; Rewrite H0; Rewrite H1; (
 Case (reduce t0); [ 
   Intro z0; Case (reduce t1); Intros; Auto
 | Intros; Auto
 | Intros; Auto
 | Intros; Auto
 | Intros; Auto
 | Intros; Auto ]));
Intros t0 H0; Simpl; Rewrite H0; Case (reduce t0); Intros; Auto.
Save.

(* \subsubsection{Fusions}
    \paragraph{Fusion de deux équations} *)
(* On donne une somme de deux équations qui sont supposées normalisées. 
   Cette fonction prend une trace de fusion en argument et transforme
   le terme en une équation normalisée. C'est une version très simplifiée
   du moteur de réécriture [rewrite]. *)

Fixpoint fusion [trace : (list t_fusion)] : term -> term := [t: term]
  Cases trace of
    nil => (reduce t)
  | (cons step trace') =>
	Cases step of
        | F_equal => 
	    (apply_right (fusion trace') (T_OMEGA10 t))
        | F_cancel => 
	    (fusion trace' (Tred_factor5 (T_OMEGA10 t)))
        | F_left => 
	    (apply_right (fusion trace') (T_OMEGA11 t))
        | F_right =>
	    (apply_right (fusion trace') (T_OMEGA12 t))
	end
  end.
    
Theorem fusion_stable : (t : (list t_fusion)) (term_stable (fusion t)).

Induction t; Simpl; [
  Exact reduce_stable
| Intros stp l H; Case stp; [
    Apply compose_term_stable; 
      [ Apply apply_right_stable; Assumption | Exact T_OMEGA10_stable ]
  | Unfold term_stable; Intros e t1; Rewrite T_OMEGA10_stable; 
    Rewrite Tred_factor5_stable; Apply H
  | Apply compose_term_stable; 
      [ Apply apply_right_stable; Assumption | Exact T_OMEGA11_stable ]
  | Apply compose_term_stable;
      [ Apply apply_right_stable; Assumption | Exact T_OMEGA12_stable ]]].

Save.

(* \paragraph{Fusion de deux équations dont une sans coefficient} *)

Definition fusion_right [trace : (list t_fusion)] : term -> term := [t: term]
  Cases trace of
    nil => (reduce t)  (* Il faut mettre un compute *)
  | (cons step trace') =>
	Cases step of
        | F_equal => 
	    (apply_right (fusion trace') (T_OMEGA15 t))
        | F_cancel => 
	    (fusion trace' (Tred_factor5 (T_OMEGA15 t)))
        | F_left => 
	    (apply_right (fusion trace') (Tplus_assoc_r t))
        | F_right =>
	    (apply_right (fusion trace') (T_OMEGA12 t))
	end
  end.

(* \paragraph{Fusion avec annihilation} *)
(* Normalement le résultat est une constante *)

Fixpoint fusion_cancel [trace:nat] : term -> term := [t:term]
  Cases trace of
    O => (reduce t)
  | (S trace') => (fusion_cancel trace' (T_OMEGA13 t))
  end.

Theorem fusion_cancel_stable : (t:nat) (term_stable (fusion_cancel t)).

Unfold term_stable fusion_cancel; Intros trace e; Elim trace; [
  Exact (reduce_stable e)
| Intros n H t; Elim H; Exact (T_OMEGA13_stable e t) ].
Save. 

(* \subsubsection{Opérations affines sur une équation} *)
(* \paragraph{Multiplication scalaire et somme d'une constante} *)

Fixpoint scalar_norm_add [trace:nat] : term -> term := [t: term]
  Cases trace of
    O => (reduce t)
  | (S trace') => (apply_right (scalar_norm_add trace') (T_OMEGA11 t))
  end.

Theorem scalar_norm_add_stable : (t:nat) (term_stable (scalar_norm_add t)).

Unfold term_stable scalar_norm_add; Intros trace; Elim trace; [
  Exact reduce_stable
| Intros n H e t; Elim apply_right_stable; 
    [ Exact (T_OMEGA11_stable e t) | Exact H ]].
Save.
   
(* \paragraph{Multiplication scalaire} *)
Fixpoint scalar_norm [trace:nat] : term -> term := [t: term]
  Cases trace of
    O => (reduce t)
  | (S trace') => (apply_right (scalar_norm trace') (T_OMEGA16 t))
  end.

Theorem scalar_norm_stable : (t:nat) (term_stable (scalar_norm t)).

Unfold term_stable scalar_norm; Intros trace; Elim trace; [
  Exact reduce_stable
| Intros n H e t; Elim apply_right_stable;
    [ Exact (T_OMEGA16_stable e t) | Exact H ]].
Save.

(* \paragraph{Somme d'une constante} *)
Fixpoint add_norm [trace:nat] : term -> term := [t: term]
  Cases trace of
    O => (reduce t)
  | (S trace') => (apply_right (add_norm trace') (Tplus_assoc_r t))
  end.

Theorem add_norm_stable : (t:nat) (term_stable (add_norm t)).

Unfold term_stable add_norm; Intros trace; Elim trace; [
  Exact reduce_stable
| Intros n H e t; Elim apply_right_stable;
    [ Exact (Tplus_assoc_r_stable e t) | Exact H ]].
Save.

(* \subsection{La fonction de normalisation des termes (moteur de réécriture)} *)


Fixpoint rewrite [s: step] : term -> term :=
  Cases s of 
   | (C_DO_BOTH s1 s2) => (apply_both (rewrite s1) (rewrite s2))
   | (C_LEFT s) => (apply_left (rewrite s))
   | (C_RIGHT s) => (apply_right (rewrite s))
   | (C_SEQ s1 s2) => [t: term] (rewrite s2 (rewrite s1 t))
   | C_NOP => [t:term] t
   | C_OPP_PLUS => Topp_plus
   | C_OPP_OPP => Topp_opp
   | C_OPP_MULT_R => Topp_mult_r
   | C_OPP_ONE => Topp_one
   | C_REDUCE => reduce
   | C_MULT_PLUS_DISTR => Tmult_plus_distr
   | C_MULT_OPP_LEFT => Tmult_opp_left
   | C_MULT_ASSOC_R => Tmult_assoc_r
   | C_PLUS_ASSOC_R => Tplus_assoc_r
   | C_PLUS_ASSOC_L => Tplus_assoc_l
   | C_PLUS_PERMUTE => Tplus_permute
   | C_PLUS_SYM => Tplus_sym
   | C_RED0 => Tred_factor0
   | C_RED1 => Tred_factor1
   | C_RED2 => Tred_factor2
   | C_RED3 => Tred_factor3
   | C_RED4 => Tred_factor4
   | C_RED5 => Tred_factor5
   | C_RED6 => Tred_factor6
   | C_MULT_ASSOC_REDUCED => Tmult_assoc_reduced
   | C_MINUS => Tminus_def
   | C_MULT_SYM => Tmult_sym
  end.

Theorem rewrite_stable : (s:step) (term_stable (rewrite s)).

Induction s; Simpl; [
  Intros; Apply apply_both_stable; Auto
| Intros; Apply apply_left_stable; Auto
| Intros; Apply apply_right_stable; Auto
| Unfold term_stable; Intros; Elim H0; Apply H
| Unfold term_stable; Auto
| Exact Topp_plus_stable
| Exact Topp_opp_stable
| Exact Topp_mult_r_stable
| Exact Topp_one_stable
| Exact reduce_stable
| Exact Tmult_plus_distr_stable
| Exact Tmult_opp_left_stable
| Exact Tmult_assoc_r_stable
| Exact Tplus_assoc_r_stable
| Exact Tplus_assoc_l_stable
| Exact Tplus_permute_stable
| Exact Tplus_sym_stable
| Exact Tred_factor0_stable
| Exact Tred_factor1_stable
| Exact Tred_factor2_stable
| Exact Tred_factor3_stable
| Exact Tred_factor4_stable
| Exact Tred_factor5_stable
| Exact Tred_factor6_stable
| Exact Tmult_assoc_reduced_stable
| Exact Tminus_def_stable
| Exact Tmult_sym_stable ].
Save.

(* \subsection{tactiques de résolution d'un but omega normalisé} 
   Trace de la procédure 
\subsubsection{Tactiques générant une contradiction}
\paragraph{[O_CONSTANT_NOT_NUL]} *)

Definition constant_not_nul [i:nat; h: hyps] :=
  Cases (nth_hyps i h) of
     (EqTerm (Tint ZERO) (Tint n)) =>
	Case (eq_Z n ZERO) of
	    h
            absurd
        end
   | _ => h
  end.

Theorem constant_not_nul_valid : 
  (i:nat) (valid_hyps (constant_not_nul i)).

Unfold valid_hyps constant_not_nul; Intros;
Generalize (nth_valid ep e i lp); Simplify; Simpl; (Elim_eq_Z z0 ZERO); Auto;
Simpl; Intros H1 H2; Elim H1; Symmetry; Auto.
Save.   

(* \paragraph{[O_CONSTANT_NEG]} *)

Definition constant_neg [i:nat; h: hyps] :=
   Cases (nth_hyps i h) of
      (LeqTerm (Tint ZERO) (Tint (NEG n))) => absurd
   | _ => h
   end.

Theorem constant_neg_valid : (i:nat) (valid_hyps (constant_neg i)).

Unfold valid_hyps constant_neg; Intros;
Generalize (nth_valid ep e i lp); Simplify; Simpl; Unfold Zle; Simpl;
Intros H1; Elim H1; [ Assumption | Trivial ].
Save.   

(* \paragraph{[NOT_EXACT_DIVIDE]} *)
Definition not_exact_divide [k1,k2:Z; body:term; t:nat; i : nat; l:hyps] :=
  Cases (nth_hyps i l) of
      (EqTerm (Tint ZERO) b) =>
         Case (eq_term
	         (scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2))) b) of
	   Cases (Zcompare k2 ZERO) of
	     SUPERIEUR =>
	       Cases (Zcompare k1 k2) of
		 SUPERIEUR => absurd
	       | _ => l
	       end
	   | _ => l
           end
	   l
         end
   | _ => l
   end.

Theorem not_exact_divide_valid : (k1,k2:Z; body:term; t:nat; i:nat) 
	(valid_hyps (not_exact_divide k1 k2 body t i)).

Unfold valid_hyps not_exact_divide; Intros; Generalize (nth_valid ep e i lp);
Simplify;
(Elim_eq_term '(scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2)))
	     't1); Auto; 
Simplify; 
Intro H2; Elim H2; Simpl; Elim (scalar_norm_add_stable t e); Simpl;
Intro H4; Absurd `(interp_term e body)*k1+k2 = 0`; [
   Apply OMEGA4; Assumption | Symmetry; Auto ].

Save.

(* \paragraph{[O_CONTRADICTION]} *)

Definition contradiction [t: nat; i,j:nat;l:hyps] :=
  Cases (nth_hyps i l) of
    (LeqTerm  (Tint ZERO) b1) =>
	Cases (nth_hyps j l) of 
	  (LeqTerm  (Tint ZERO) b2) => 
	     Cases (fusion_cancel t (Tplus b1 b2)) of
	       (Tint k) =>
		  Cases (Zcompare ZERO k) of
	            SUPERIEUR => absurd
	          | _ => l
                  end
             | _ => l
             end
         | _ => l 
        end
  | _ => l 
  end.

Theorem contradiction_valid : (t,i,j: nat) (valid_hyps (contradiction t i j)).

Unfold valid_hyps contradiction; Intros t i j ep e l H;
Generalize (nth_valid ? ? i ? H); Generalize (nth_valid ? ? j ? H);
Case (nth_hyps i l); Auto; Intros t1 t2; Case t1; Auto; Intros z; Case z; Auto;
Case (nth_hyps j l); Auto; Intros t3 t4; Case t3; Auto; Intros z'; Case z'; 
Auto; Simpl; Intros H1 H2;
Generalize (refl_equal Z (interp_term e (fusion_cancel t (Tplus t2 t4))));
Pattern 2 3 (fusion_cancel t (Tplus t2 t4));
Case (fusion_cancel t (Tplus t2 t4)); 
Simpl; Auto; Intro k; Elim (fusion_cancel_stable t);
Simpl; Intro E; Generalize (OMEGA2 ? ? H2 H1); Rewrite E; Case k; 
Auto;Unfold Zle; Simpl; Intros p H3; Elim H3; Auto.

Save.

(* \paragraph{[O_NEGATE_CONTRADICT]} *)

Definition negate_contradict [i1,i2:nat; h:hyps]:=
  Cases (nth_hyps i1 h) of
    (EqTerm (Tint ZERO) b1) =>
	Cases (nth_hyps i2 h) of
           (NeqTerm (Tint ZERO) b2) =>
	      Cases (eq_term b1 b2) of
	         true => absurd
              |  false => h
	    end
        | _ => h
        end
  | (NeqTerm (Tint ZERO) b1) =>
	Cases (nth_hyps i2 h) of
           (EqTerm (Tint ZERO) b2) =>
	      Cases (eq_term b1 b2) of
	         true => absurd
              |  false => h
	    end
        | _ => h
        end
  | _ => h
  end.

Definition negate_contradict_inv [t:nat; i1,i2:nat; h:hyps]:=
  Cases (nth_hyps i1 h) of
    (EqTerm (Tint ZERO) b1) =>
	Cases (nth_hyps i2 h) of
           (NeqTerm (Tint ZERO) b2) =>
              Cases (eq_term b1 (scalar_norm t (Tmult b2 (Tint `-1`)))) of
	         true => absurd
              |  false => h
	    end
        | _ => h
        end
  | (NeqTerm (Tint ZERO) b1) =>
	Cases (nth_hyps i2 h) of
           (EqTerm (Tint ZERO) b2) =>
              Cases (eq_term b1 (scalar_norm t (Tmult b2 (Tint `-1`)))) of
	         true => absurd
              |  false => h
	    end
        | _ => h
        end
  | _ => h
  end.

Theorem negate_contradict_valid :
  (i,j:nat) (valid_hyps (negate_contradict i j)).

Unfold valid_hyps negate_contradict; Intros i j ep e l H;
Generalize (nth_valid ? ? i ? H); Generalize (nth_valid ? ? j ? H);
Case (nth_hyps i l); Auto; Intros t1 t2; Case t1; Auto; Intros z; Case z; Auto;
Case (nth_hyps j l); Auto; Intros t3 t4; Case t3; Auto; Intros z'; Case z'; 
Auto; Simpl; Intros H1 H2; [
  (Elim_eq_term t2 t4); Intro H3; [ Elim H1; Elim H3; Assumption | Assumption ]
| (Elim_eq_term t2 t4); Intro H3; 
    [ Elim H2; Rewrite H3; Assumption | Assumption ]].

Save.

Theorem negate_contradict_inv_valid :
  (t,i,j:nat) (valid_hyps (negate_contradict_inv t i j)).


Unfold valid_hyps negate_contradict_inv; Intros t i j ep e l H;
Generalize (nth_valid ? ? i ? H); Generalize (nth_valid ? ? j ? H);
Case (nth_hyps i l); Auto; Intros t1 t2; Case t1; Auto; Intros z; Case z; Auto;
Case (nth_hyps j l); Auto; Intros t3 t4; Case t3; Auto; Intros z'; Case z'; 
Auto; Simpl; Intros H1 H2;
(Pattern (eq_term t2 (scalar_norm t (Tmult t4 (Tint (NEG xH))))); Apply bool_ind2; Intro Aux; [
  Generalize (eq_term_true t2 (scalar_norm t (Tmult t4 (Tint (NEG xH)))) Aux);
  Clear Aux
| Generalize (eq_term_false t2 (scalar_norm t (Tmult t4 (Tint (NEG xH)))) Aux);
  Clear Aux ]); [
   Intro H3; Elim H1; Generalize H2; Rewrite H3; 
   Rewrite <- (scalar_norm_stable t e); Simpl; Elim (interp_term e t4) ; 
   Simpl; Auto; Intros p H4; Discriminate H4
 | Auto 
 | Intro H3; Elim H2; Rewrite H3; Elim (scalar_norm_stable t e); Simpl;
   Elim H1; Simpl; Trivial
 | Auto ].

Save.

(* \subsubsection{Tactiques générant une nouvelle équation} *)
(* \paragraph{[O_SUM]}
 C'est une oper2 valide mais elle traite plusieurs cas à la fois (suivant
 les opérateurs de comparaison des deux arguments) d'où une
 preuve un peu compliquée. On utilise quelques lemmes qui sont des 
 généralisations des théorèmes utilisés par OMEGA. *)

Definition sum [k1,k2: Z; trace: (list t_fusion); prop1,prop2:proposition]:=
  Cases prop1 of
    (EqTerm (Tint ZERO) b1) =>
	Cases prop2 of
          (EqTerm (Tint ZERO) b2) =>
	    (EqTerm 
	       (Tint ZERO) 
	       (fusion trace 
	               (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2)))))
        | (LeqTerm (Tint ZERO) b2) =>
	    Cases (Zcompare k2 ZERO) of
	       SUPERIEUR =>
		 (LeqTerm 
		    (Tint ZERO) 
		    (fusion trace 
			 (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2)))))
            | _ => TrueTerm
           end
       | _ => TrueTerm
       end
  | (LeqTerm (Tint ZERO) b1) =>
      Cases (Zcompare k1 ZERO) of
        SUPERIEUR =>
	  Cases prop2 of
	    (EqTerm (Tint ZERO) b2) =>
	      (LeqTerm 
		 (Tint ZERO) 
		 (fusion trace 
			 (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2)))))
	  | (LeqTerm (Tint ZERO) b2) =>
	       Cases (Zcompare k2 ZERO) of
		  SUPERIEUR =>
		    (LeqTerm 
		       (Tint ZERO) 
		       (fusion trace 
			    (Tplus (Tmult b1 (Tint k1)) 
                                   (Tmult b2 (Tint k2)))))
	       | _ => TrueTerm
	      end
	 | _ => TrueTerm
	 end
     | _ => TrueTerm
     end
  | (NeqTerm (Tint ZERO) b1) =>
       Cases prop2 of
	 (EqTerm (Tint ZERO) b2) =>
	    Case (eq_Z k1 ZERO) of
	       TrueTerm
	       (NeqTerm 
		  (Tint ZERO) 
		  (fusion trace 
			  (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2)))))
	    end
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem sum1 :
  (a,b,c,d:Z) (`0 = a`) -> (`0 = b`) -> (`0 = a*c + b*d`).

Intros; Elim H; Elim H0; Simpl; Auto.
Save.
  
Theorem sum2 :
  (a,b,c,d:Z)  (`0 <= d`) -> (`0 = a`) -> (`0 <= b`) ->(`0 <= a*c + b*d`).

Intros; Elim H0; Simpl; Generalize H H1; Case b; Case d; 
Unfold Zle; Simpl; Auto.  
Save.

Theorem sum3 :
  (a,b,c,d:Z)  (`0 <= c`) -> (`0 <= d`) -> (`0 <= a`) -> (`0 <= b`) ->(`0 <= a*c + b*d`).

Intros a b c d; Case a; Case b; Case c; Case d; Unfold Zle; Simpl; Auto. 
Save.

Theorem sum4 : (k:Z) (Zcompare k `0`)=SUPERIEUR -> (`0 <= k`).

Intro; Case k; Unfold Zle; Simpl; Auto; Intros; Discriminate.  
Save.

Theorem sum5 :
  (a,b,c,d:Z) (`c <> 0`) -> (`0 <> a`) -> (`0 = b`) -> (`0 <> a*c + b*d`).

Intros a b c d H1 H2 H3; Elim H3; Simpl; Rewrite Zplus_sym;
Simpl; Generalize H1 H2; Case a; Case c; Simpl; Intros; Try Discriminate;
Assumption.
Save.


Theorem sum_valid : (k1,k2:Z; t:(list t_fusion)) (valid2 (sum k1 k2 t)).

Unfold valid2; Intros k1 k2 t ep e p1 p2; Unfold sum; Simplify; Simpl; Auto;
Try (Elim (fusion_stable t)); Simpl; Intros; [
  Apply sum1; Assumption
| Apply sum2; Try Assumption; Apply sum4; Assumption
| Rewrite Zplus_sym; Apply sum2; Try Assumption; Apply sum4; Assumption
| Apply sum3; Try Assumption; Apply sum4; Assumption
| (Elim_eq_Z k1 ZERO); Simpl; Auto; Elim (fusion_stable t); Simpl; Intros;
  Unfold Zne; Apply sum5; Assumption].
Save.

(* \paragraph{[O_EXACT_DIVIDE]}
   c'est une oper1 valide mais on préfère une substitution a ce point la *)

Definition exact_divide [k:Z; body:term; t: nat; prop:proposition] :=
   Cases prop of
      (EqTerm (Tint ZERO) b) =>
         Case (eq_term (scalar_norm t (Tmult body (Tint k))) b) of
	   Case (eq_Z k ZERO) of
	      TrueTerm
	      (EqTerm (Tint ZERO) body)
           end
           TrueTerm
         end
   | _ => TrueTerm
   end.

Theorem exact_divide_valid :
  (k:Z) (t:term) (n:nat) (valid1 (exact_divide k t n)).


Unfold valid1 exact_divide; Intros k1 k2 t ep e p1; Simplify;Simpl; Auto;
(Elim_eq_term  '(scalar_norm t (Tmult k2 (Tint k1))) 't1); Simpl; Auto;
(Elim_eq_Z 'k1 'ZERO); Simpl; Auto;  Intros H1 H2; Elim H2; 
Elim scalar_norm_stable; Simpl; Generalize H1; Case (interp_term e k2);
Try Trivial; (Case k1; Simpl; [
  Intros; Absurd `0 = 0`; Assumption
| Intros p2 p3 H3 H4; Discriminate H4
| Intros p2 p3 H3 H4; Discriminate H4 ]).

Save.



(* \paragraph{[O_DIV_APPROX]}
  La preuve reprend le schéma de la précédente mais on
  est sur une opération de type valid1 et non sur une opération terminale. *)

Definition divide_and_approx [k1,k2:Z; body:term; t:nat; prop:proposition] :=
  Cases prop of
      (LeqTerm (Tint ZERO) b) =>
         Case (eq_term
                (scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2))) b) of
	   Cases (Zcompare k1 ZERO) of
	     SUPERIEUR =>
	       Cases (Zcompare k1 k2) of
		 SUPERIEUR =>(LeqTerm (Tint ZERO) body)
	       | _ => prop
	       end
	   | _ => prop
           end
	   prop
         end
   | _ => prop
   end.

Theorem divide_and_approx_valid : (k1,k2:Z; body:term; t:nat) 
	(valid1 (divide_and_approx k1 k2 body t)).

Unfold valid1 divide_and_approx; Intros k1 k2 body t ep e p1;Simplify;
(Elim_eq_term '(scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2))) 't1); Simplify; Auto;  Intro E; Elim E; Simpl; 
Elim (scalar_norm_add_stable t e); Simpl; Intro H1; 
Apply Zmult_le_approx with 3 := H1; Assumption.
Save.

(* \paragraph{[MERGE_EQ]} *)

Definition merge_eq [t: nat; prop1, prop2: proposition] :=
  Cases prop1 of
     (LeqTerm (Tint ZERO) b1) =>
	Cases prop2 of
     	  (LeqTerm (Tint ZERO) b2) =>
             Case (eq_term b1 (scalar_norm t (Tmult b2 (Tint `-1`)))) of
	        (EqTerm (Tint ZERO) b1)
 	       	TrueTerm
	     end
        | _ => TrueTerm
	end
  | _ => TrueTerm
  end.

Theorem merge_eq_valid : (n:nat) (valid2 (merge_eq n)).

Unfold valid2 merge_eq; Intros n ep e p1 p2; Simplify; Simpl; Auto;
Elim (scalar_norm_stable n e); Simpl; Intros; Symmetry; 
Apply OMEGA8 with 2 := H0; [ Assumption | Elim Zopp_one; Trivial ].
Save.



(* \paragraph{[O_CONSTANT_NUL]} *)

Definition constant_nul [i:nat; h: hyps] :=
  Cases (nth_hyps i h) of
     (NeqTerm (Tint ZERO) (Tint ZERO)) => absurd
   | _ => h
  end.

Theorem constant_nul_valid : 
  (i:nat) (valid_hyps (constant_nul i)).

Unfold valid_hyps constant_nul; Intros; Generalize (nth_valid ep e i lp);
Simplify; Simpl; Unfold Zne; Intro H1; Absurd `0=0`; Auto.
Save.

(* \paragraph{[O_STATE]} *)

Definition state [m:Z;s:step; prop1,prop2:proposition] :=
  Cases prop1 of
     (EqTerm (Tint ZERO) b1) =>
	Cases prop2 of
	   (EqTerm (Tint ZERO) (Tplus b2 (Topp b3))) =>
	      (EqTerm (Tint ZERO) (rewrite s (Tplus b1 (Tmult (Tplus (Topp b3) b2) (Tint m)))))
	| _ => TrueTerm
	end
  | _ => TrueTerm
  end.

Theorem state_valid : (m:Z; s:step) (valid2 (state m s)).

Unfold valid2; Intros m s ep e p1 p2; Unfold state; Simplify; Simpl;Auto;
Elim (rewrite_stable s e); Simpl; Intros H1 H2; Elim H1;
Rewrite (Zplus_sym `-(interp_term e t5)` `(interp_term e t3)`);
Elim H2; Simpl; Reflexivity.

Save.

(* \subsubsection{Tactiques générant plusieurs but}
   \paragraph{[O_SPLIT_INEQ]} 
   La seule pour le moment (tant que la normalisation n'est pas réfléchie). *)

Definition split_ineq  [i,t: nat; f1,f2:hyps -> lhyps;  l:hyps] :=
  Cases (nth_hyps i l) of
    (NeqTerm  (Tint ZERO) b1) =>
       (app (f1 (cons (LeqTerm (Tint ZERO) (add_norm t (Tplus b1 (Tint `-1`)))) l))
            (f2 (cons (LeqTerm (Tint ZERO) 
                               (scalar_norm_add t 
	                         (Tplus (Tmult b1 (Tint `-1`)) (Tint `-1`))))
                      l)))
  | _ => (cons l (nil ?))
  end.

Theorem split_ineq_valid : 
  (i,t: nat; f1,f2: hyps -> lhyps) 
    (valid_list_hyps f1) ->(valid_list_hyps f2) -> 
      (valid_list_hyps (split_ineq i t f1 f2)).

Unfold valid_list_hyps split_ineq; Intros i t f1 f2 H1 H2 ep e lp H; 
Generalize (nth_valid ? ? i ? H); 
Case (nth_hyps i lp); Simpl; Auto; Intros t1 t2; Case t1; Simpl; Auto;
Intros z; Case z; Simpl; Auto;
Intro H3; Apply append_valid;Elim (OMEGA19 (interp_term e t2)) ;[
  Intro H4; Left; Apply H1; Simpl; Elim (add_norm_stable t); Simpl; Auto
| Intro H4; Right; Apply H2; Simpl; Elim (scalar_norm_add_stable t); 
  Simpl; Auto
| Generalize H3; Unfold Zne not; Intros E1 E2; Apply E1; Symmetry; Trivial ].
Save.


(* \subsection{La fonction de rejeu de la trace} *)

Fixpoint execute_omega [t: t_omega] : hyps -> lhyps := 
  [l : hyps] Cases t of
   | (O_CONSTANT_NOT_NUL n) => (singleton (constant_not_nul n l))
   | (O_CONSTANT_NEG n) => (singleton (constant_neg n l))
   | (O_DIV_APPROX  k1 k2 body t cont n) =>
       (execute_omega cont 
	  (apply_oper_1 n (divide_and_approx k1 k2 body t) l))
   | (O_NOT_EXACT_DIVIDE  k1 k2 body t i) =>
       (singleton (not_exact_divide k1 k2 body t i l))
   | (O_EXACT_DIVIDE k body t cont n) =>
       (execute_omega cont (apply_oper_1 n (exact_divide k body t) l))
   | (O_SUM k1 i1 k2 i2 t cont) =>
       (execute_omega cont (apply_oper_2 i1 i2 (sum k1 k2 t) l))
   | (O_CONTRADICTION t i j) =>
       (singleton (contradiction t i j l))
   | (O_MERGE_EQ t i1 i2 cont) =>
       (execute_omega cont (apply_oper_2 i1 i2 (merge_eq t) l))
   | (O_SPLIT_INEQ t i cont1 cont2) =>
       (split_ineq i t (execute_omega cont1) (execute_omega cont2) l)
   | (O_CONSTANT_NUL i) => (singleton (constant_nul i l))
   | (O_NEGATE_CONTRADICT i j) =>  (singleton (negate_contradict i j l))
   | (O_NEGATE_CONTRADICT_INV t i j) => (singleton (negate_contradict_inv t i j l))
   | (O_STATE m s i1 i2 cont) =>
       (execute_omega cont (apply_oper_2 i1 i2 (state m s) l))
  end.

Theorem omega_valid : (t: t_omega) (valid_list_hyps (execute_omega t)).

Induction t; Simpl; [
  Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (constant_not_nul_valid n ep e lp H)
| Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (constant_neg_valid n ep e lp H)
| Unfold valid_list_hyps valid_hyps; Intros k1 k2 body n t' Ht' m ep e lp H; 
  Apply Ht';
  Apply (apply_oper_1_valid m (divide_and_approx k1 k2 body n)
	  (divide_and_approx_valid k1 k2 body n) ep e lp H)
| Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (not_exact_divide_valid z z0 t0 n n0 ep e lp H)
| Unfold valid_list_hyps valid_hyps; Intros k body n t' Ht' m ep e lp H; 
  Apply Ht';
  Apply (apply_oper_1_valid m (exact_divide k body n)
	  (exact_divide_valid k body n) ep e lp H)
| Unfold valid_list_hyps valid_hyps; Intros k1 i1 k2 i2 trace t' Ht' ep e lp H;
  Apply Ht'; 
  Apply (apply_oper_2_valid i1 i2 (sum k1 k2 trace) 
	  (sum_valid k1 k2 trace) ep e lp H)
| Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (contradiction_valid n n0 n1 ep e lp H)
| Unfold valid_list_hyps valid_hyps; Intros trace i1 i2 t' Ht' ep e lp H; 
  Apply Ht';
  Apply (apply_oper_2_valid i1 i2 (merge_eq trace) 
          (merge_eq_valid trace) ep e lp H) 
| Intros t' i k1 H1 k2 H2; Unfold valid_list_hyps; Simpl; Intros ep e lp H;
  Apply (split_ineq_valid i t' (execute_omega k1) (execute_omega k2) 
	 H1 H2 ep e lp H)
| Unfold valid_list_hyps; Simpl; Intros i ep e lp H; Left; 
  Apply (constant_nul_valid i ep e lp H)
| Unfold valid_list_hyps; Simpl; Intros i j ep e lp H; Left; 
  Apply (negate_contradict_valid i j ep e lp H)
| Unfold valid_list_hyps; Simpl; Intros n i j ep e lp H; Left; 
  Apply (negate_contradict_inv_valid n i j ep e lp H)
| Unfold valid_list_hyps valid_hyps; Intros m s i1 i2 t' Ht' ep e lp H; Apply Ht';
  Apply (apply_oper_2_valid i1 i2 (state m s) (state_valid m s) ep e lp H)
].
Save.


(* \subsection{Les opérations globales sur le but} 
   \subsubsection{Normalisation} *)

Definition move_right [s: step; p:proposition] :=
  Cases p of
     (EqTerm t1 t2) => (EqTerm (Tint ZERO) (rewrite s (Tplus t1 (Topp t2))))
   | (LeqTerm t1 t2) => (LeqTerm (Tint ZERO) (rewrite s (Tplus t2 (Topp t1))))
   | (GeqTerm t1 t2) => (LeqTerm (Tint ZERO) (rewrite s (Tplus t1 (Topp t2))))
   | (LtTerm t1 t2) =>
        (LeqTerm (Tint ZERO)
	         (rewrite s (Tplus (Tplus t2 (Tint `-1`)) (Topp t1))))
   | (GtTerm t1 t2) => 
        (LeqTerm (Tint ZERO)
                 (rewrite s (Tplus (Tplus t1 (Tint `-1`)) (Topp t2))))
   | (NeqTerm t1 t2) => (NeqTerm (Tint ZERO) (rewrite s (Tplus t1 (Topp t2))))
   | p => p
  end.

Theorem Zne_left_2 : (x,y:Z)(Zne x y)->(Zne `0` `x+(-y)`).
Unfold Zne not; Intros x y H1 H2; Apply H1; Apply (Zsimpl_plus_l `-y`);
Rewrite Zplus_sym; Elim H2; Rewrite Zplus_inverse_l; Trivial.
Save.

Theorem move_right_valid : (s: step) (valid1 (move_right s)).

Unfold valid1 move_right; Intros s ep e p; Simplify; Simpl;
Elim (rewrite_stable s e); Simpl; [
  Symmetry; Apply Zegal_left; Assumption
| Intro; Apply Zle_left; Assumption 
| Intro; Apply Zge_left; Assumption
| Intro; Apply Zgt_left; Assumption
| Intro; Apply Zlt_left; Assumption
| Intro; Apply Zne_left_2; Assumption
].
Save.

Definition do_normalize [i:nat; s: step] := (apply_oper_1 i (move_right s)).

Theorem do_normalize_valid : (i:nat; s:step) (valid_hyps (do_normalize i s)).

Intros; Unfold do_normalize; Apply apply_oper_1_valid; Apply move_right_valid.
Save.

Fixpoint do_normalize_list [l:(list step)] : nat -> hyps -> hyps := 
  [i:nat; h:hyps] Cases l of
    (cons s l') => (do_normalize_list l' (S i) (do_normalize i s h))
  | nil => h
  end.

Theorem do_normalize_list_valid : 
  (l:(list step); i:nat) (valid_hyps (do_normalize_list l i)).

Induction l; Simpl; Unfold valid_hyps; [
  Auto
| Intros a l' Hl' i ep e lp H; Unfold valid_hyps in Hl'; Apply Hl';
  Apply (do_normalize_valid i a ep e lp); Assumption ].
Save.

Theorem normalize_goal :
  (s: (list step); ep: PropList; env : (list Z); l: hyps)
    (interp_goal ep env (do_normalize_list s O l)) -> 
      (interp_goal ep env l).

Intros; Apply valid_goal with 2:=H; Apply do_normalize_list_valid.
Save.

(* \subsubsection{Exécution de la trace} *)

Theorem execute_goal :
  (t : t_omega; ep: PropList; env : (list Z); l: hyps)
    (interp_list_goal ep env (execute_omega t l)) -> (interp_goal ep env l).

Intros; Apply (goal_valid (execute_omega t) (omega_valid t) ep env l H).
Save.


Theorem append_goal :
  (ep: PropList; e: (list Z)) (l1,l2:lhyps)
     (interp_list_goal ep e l1) /\ (interp_list_goal ep e l2) ->
     (interp_list_goal ep e (app l1 l2)).

Intros ep e; Induction l1; [
  Simpl; Intros l2 (H1, H2); Assumption
| Simpl; Intros h1 t1 HR l2 ((H1 , H2), H3) ; Split; Auto].

Save.

Require Decidable.

(* A simple decidability checker : if the proposition belongs to the
   simple grammar describe below then it is decidable. Proof is by 
   induction and uses well known theorem about arithmetic and propositional
   calculus *)

Fixpoint decidability [p:proposition] : bool :=
  Cases p of
    (EqTerm _ _) => true
  | (LeqTerm _ _) => true
  | (GeqTerm _ _) => true
  | (GtTerm _ _) => true
  | (LtTerm _ _) => true
  | (NeqTerm _ _) => true
  | (FalseTerm) => true
  | (TrueTerm) => true
  | (Tnot t) => (decidability t)
  | (Tand t1 t2) => (andb (decidability t1) (decidability t2))
  | (Timp t1 t2) => (andb (decidability t1) (decidability t2))
  | (Tor t1 t2) =>  (andb (decidability t1) (decidability t2))
  | (Tprop _) => false
  end
.

Theorem decidable_correct :
  (ep: PropList) (e: (list Z)) (p:proposition)
    (decidability p)=true -> (decidable (interp_proposition ep e p)).

Induction p; Simpl; Intros; [
  Apply dec_eq
| Apply dec_Zle
| Left;Auto
| Right; Unfold not; Auto
| Apply dec_not; Auto
| Apply dec_Zge
| Apply dec_Zgt
| Apply dec_Zlt
| Apply dec_Zne
| Apply dec_or; Elim andb_prop with 1 := H1; Auto
| Apply dec_and; Elim andb_prop with 1 := H1; Auto
| Apply dec_imp; Elim andb_prop with 1 := H1; Auto
| Discriminate H].

Save.

(* An interpretation function for a complete goal with an explicit
   conclusion. We use an intermediate fixpoint. *)

Fixpoint interp_full_goal 
    [envp: PropList;env : (list Z); c : proposition; l: hyps] : Prop :=
  Cases l of 
     nil => (interp_proposition envp env c)
   | (cons p' l') => 
	(interp_proposition envp env p') -> (interp_full_goal envp env c l')
  end.

Definition interp_full 
    [ep: PropList;e : (list Z); lc : (hyps * proposition)] : Prop :=
      Cases lc of (l,c) => (interp_full_goal ep e c l) end.

(* Relates the interpretation of a complete goal with the interpretation
   of its hypothesis and conclusion *)

Theorem interp_full_false :
  (ep: PropList; e : (list Z); l: hyps; c : proposition) 
    ((interp_hyps ep e l) -> (interp_proposition ep e c)) -> 
	(interp_full ep e (l,c)).

Induction l; Unfold interp_full; Simpl; [
  Auto
| Intros a l1 H1 c H2 H3; Apply H1; Auto].

Save.

(* Push the conclusion in the list of hypothesis using a double negation
   If the decidability cannot be "proven", then just forget about the 
   conclusion (equivalent of replacing it with false) *)

Definition to_contradict [lc : hyps * proposition] :=
   Cases lc of
      (l,c) => (if (decidability c) then (cons (Tnot c) l) else l)
   end.

(* The previous operation is valid in the sense that the new list of
   hypothesis implies the original goal *)

Theorem to_contradict_valid :
  (ep: PropList; e : (list Z); lc: hyps * proposition)
	(interp_goal ep e (to_contradict lc)) -> (interp_full ep e lc).

Intros ep e lc; Case lc; Intros l c; Simpl; (Pattern (decidability c));
Apply bool_ind2; [
   Simpl; Intros H H1; Apply interp_full_false; Intros H2; Apply not_not; [
     Apply decidable_correct; Assumption
   | Unfold 1 not; Intro H3; Apply hyps_to_goal with 2:=H2; Auto]
| Intros H1 H2; Apply interp_full_false; Intro H3; Elim hyps_to_goal with 1:= H2; Assumption ].
Save.

(* [map_cons x l] adds [x] at the head of each list in [l] (which is a list
   of lists *)

Fixpoint map_cons [A:Set; x:A; l:(list (list A))] : (list (list A)) :=
  Cases l of
    nil => (nil ?)
  | (cons l ll) => (cons (cons x l) (map_cons A x ll))
  end.

(* This function breaks up a list of hypothesis in a list of simpler 
   list of hypothesis that together implie the original one. The goal
   of all this is to transform the goal in a list of solvable problems. 
   Note that :
	- we need a way to drive the analysis as some hypotheis may not
          require a split. 
        - this procedure must be perfectly mimicked by the ML part otherwise
          hypothesis will get desynchronised and this will be a mess.
 *)
 
Fixpoint destructure_hyps [nn: nat] : hyps -> lhyps :=
  [ll:hyps]Cases nn of
    O => (cons ll (nil ?))
  | (S n) =>
       Cases ll of 
	  nil => (cons (nil ?) (nil ?))
       | (cons (Tor p1 p2) l) => 
	    (app (destructure_hyps n (cons p1 l))
	         (destructure_hyps n (cons p2 l)))
       | (cons (Tand p1 p2) l) => 
	    (destructure_hyps n (cons p1 (cons p2 l)))
       | (cons (Timp p1 p2) l) =>
	    (if (decidability p1) then 
	      (app (destructure_hyps n (cons (Tnot p1) l))
		   (destructure_hyps n (cons p2 l)))
	     else (map_cons ? (Timp p1 p2) (destructure_hyps n l)))
       | (cons (Tnot p) l) =>
	    Cases p of 
	       (Tnot p1) =>
		    (if (decidability p1) then (destructure_hyps n (cons p1 l))
		     else (map_cons ? (Tnot (Tnot p1)) (destructure_hyps n l)))
 	    | (Tor p1 p2) =>
		  (destructure_hyps n (cons (Tnot p1) (cons (Tnot p2) l)))
 	    | (Tand p1 p2) =>
   	         (if (decidability p1) then 
 		    (app (destructure_hyps n (cons (Tnot p1) l))
			 (destructure_hyps n (cons (Tnot p2) l)))
		 else (map_cons ? (Tnot p) (destructure_hyps n l)))
	    | _ =>  (map_cons ? (Tnot p) (destructure_hyps n l))
	    end
       | (cons x l) => (map_cons ? x (destructure_hyps n l))
       end
  end.

Theorem map_cons_val : 
  (ep: PropList; e : (list Z))
  (p:proposition;l:lhyps) 
	(interp_proposition ep e p) ->
	(interp_list_hyps ep e l) ->
	(interp_list_hyps ep e (map_cons ? p l) ).

Induction l; Simpl; [ Auto | Intros; Elim H1;  Intro H2; Auto ].
Save.

Hints Resolve map_cons_val append_valid decidable_correct.

Theorem destructure_hyps_valid : 
  (n:nat) (valid_list_hyps (destructure_hyps n)).

Induction n; [
  Unfold valid_list_hyps; Simpl; Auto
| Unfold 2 valid_list_hyps; Intros n1 H  ep e lp; Case lp; [
    Simpl; Auto
  | Intros p l; Case p; 
    Try (Simpl; Intros; Apply map_cons_val; Simpl; Elim H0; Auto); [
      Intro p'; Case p';
      Try (Simpl; Intros; Apply map_cons_val; Simpl; Elim H0; Auto); [
	Simpl; Intros p1 (H1,H2);  Pattern (decidability p1); Apply bool_ind2;
	Intro H3; [
	  Apply H; Simpl; Split; [ Apply not_not; Auto | Assumption ]
        | Auto]
      | Simpl; Intros p1 p2 (H1,H2); Apply H; Simpl; 
	Elim not_or with 1 := H1; Auto
      | Simpl; Intros p1 p2 (H1,H2);Pattern (decidability p1); Apply bool_ind2;
        Intro H3; [
	  Apply append_valid; Elim not_and with 2 := H1; [
	    Intro; Left; Apply H; Simpl; Auto
	  | Intro; Right; Apply H; Simpl; Auto
          | Auto ]
        | Auto ]]
    | Simpl; Intros p1 p2 (H1, H2); Apply append_valid; 
      (Elim H1; Intro H3; Simpl; [ Left | Right ]); Apply H; Simpl; Auto 
    | Simpl; Intros; Apply H; Simpl; Tauto
    | Simpl; Intros p1 p2 (H1, H2); Pattern (decidability p1); Apply bool_ind2;
      Intro H3; [ 
	Apply append_valid; Elim imp_simp with 2:=H1; [
	  Intro H4; Left; Simpl; Apply H; Simpl; Auto
	| Intro H4; Right; Simpl; Apply H; Simpl; Auto
	| Auto ]
      | Auto ]]]].

Save.

Definition prop_stable [f: proposition -> proposition] :=
  (ep: PropList; e: (list Z); p:proposition) 
     (interp_proposition ep e p) <-> (interp_proposition ep e (f p)).

Definition p_apply_left [f: proposition -> proposition; p : proposition]:= 
  Cases p of
    (Timp x y) => (Timp (f x) y)
  | (Tor x y) => (Tor (f x) y)
  | (Tand x y) => (Tand (f x) y)
  | (Tnot x) => (Tnot (f x))
  | x => x
  end.

Theorem p_apply_left_stable :
  (f : proposition -> proposition) 
    (prop_stable f) -> (prop_stable (p_apply_left f)).

Unfold prop_stable; Intros f H ep e p; Split; 
(Case p; Simpl; Auto; Intros p1; Elim (H ep e p1); Tauto).
Save.

Definition p_apply_right [f: proposition -> proposition; p : proposition]:= 
  Cases p of
    (Timp x y) => (Timp x (f y))
  | (Tor x y) => (Tor x (f y))
  | (Tand x y) => (Tand x (f y))
  | (Tnot x) => (Tnot (f x))
  | x => x
  end.

Theorem p_apply_right_stable :
  (f : proposition -> proposition) 
    (prop_stable f) -> (prop_stable (p_apply_right f)).

Unfold prop_stable; Intros f H ep e p; Split; 
(Case p; Simpl; Auto; [
   Intros p1; Elim (H ep e p1); Tauto
 | Intros p1 p2; Elim (H ep e p2); Tauto
 | Intros p1 p2; Elim (H ep e p2); Tauto
 | Intros p1 p2; Elim (H ep e p2); Tauto
 ]).
Save.

Definition p_invert [f : proposition -> proposition; p : proposition] := 
Cases p of
  (EqTerm x y) => (Tnot (f (NeqTerm x y)))
| (LeqTerm x y) => (Tnot (f (GtTerm x y)))
| (GeqTerm x y) => (Tnot (f (LtTerm x y)))
| (GtTerm x y) => (Tnot (f (LeqTerm x y)))
| (LtTerm x y) => (Tnot (f (GeqTerm x y)))
| (NeqTerm x y) => (Tnot (f (EqTerm x y)))
| x => x
end.

Theorem p_invert_stable :
  (f : proposition -> proposition) 
    (prop_stable f) -> (prop_stable (p_invert f)).

Unfold prop_stable; Intros f H ep e p; Split;(Case p; Simpl; Auto; [
  Intros t1 t2; Elim (H ep e (NeqTerm t1 t2)); Simpl; Unfold Zne; 
  Generalize (dec_eq (interp_term e t1) (interp_term e t2)); 
  Unfold decidable; Tauto
| Intros t1 t2; Elim (H ep e (GtTerm t1 t2)); Simpl; Unfold Zgt; 
  Generalize (dec_Zgt (interp_term e t1) (interp_term e t2)); 
  Unfold decidable Zgt Zle; Tauto
| Intros t1 t2; Elim (H ep e (LtTerm t1 t2)); Simpl; Unfold Zlt; 
  Generalize (dec_Zlt (interp_term e t1) (interp_term e t2)); 
  Unfold decidable Zge; Tauto
| Intros t1 t2; Elim (H ep e (LeqTerm t1 t2)); Simpl; 
  Generalize (dec_Zgt (interp_term e t1) (interp_term e t2)); Unfold Zle Zgt;
  Unfold decidable; Tauto
| Intros t1 t2; Elim (H ep e (GeqTerm t1 t2)); Simpl;
  Generalize (dec_Zlt (interp_term e t1) (interp_term e t2));  Unfold Zge Zlt; 
  Unfold decidable; Tauto
| Intros t1 t2; Elim (H ep e (EqTerm t1 t2)); Simpl;
  Generalize (dec_eq (interp_term e t1) (interp_term e t2)); 
  Unfold decidable Zne; Tauto ]).
Save.

Theorem Zlt_left_inv : (x,y:Z) `0 <= ((y + (-1)) + (-x))` ->  `x<y`.

Intros; Apply Zlt_S_n; Apply Zle_lt_n_Sm; 
Apply (Zsimpl_le_plus_r (Zplus `-1` (Zopp x))); Rewrite Zplus_assoc_l; 
Unfold Zs; Rewrite (Zplus_assoc_r x); Rewrite (Zplus_assoc_l y); Simpl;
Rewrite Zero_right; Rewrite Zplus_inverse_r; Assumption.
Save.

Theorem move_right_stable : (s: step) (prop_stable (move_right s)).

Unfold move_right prop_stable; Intros s ep e p; Split; [
    Simplify; Simpl; Elim (rewrite_stable s e); Simpl; [
    Symmetry; Apply Zegal_left; Assumption
  | Intro; Apply Zle_left; Assumption
  | Intro; Apply Zge_left; Assumption
  | Intro; Apply Zgt_left; Assumption
  | Intro; Apply Zlt_left; Assumption
  | Intro; Apply Zne_left_2; Assumption ]
| Case p; Simpl; Intros; Auto; Generalize H; Elim (rewrite_stable s); Simpl; 
  Intro H1; [
    Rewrite (Zplus_n_O (interp_term e t0)); Rewrite H1; Rewrite Zplus_permute;
    Rewrite Zplus_inverse_r; Rewrite Zero_right; Trivial
  | Apply (Zsimpl_le_plus_r (Zopp (interp_term e t))); Rewrite Zplus_inverse_r;
    Assumption
  | Apply Zle_ge; Apply (Zsimpl_le_plus_r (Zopp (interp_term e t0))); 
    Rewrite Zplus_inverse_r; Assumption
  | Apply Zlt_gt; Apply Zlt_left_inv; Assumption
  | Apply Zlt_left_inv; Assumption
  | Unfold Zne not; Unfold Zne in H1; Intro H2; Apply H1; Rewrite H2;
    Rewrite Zplus_inverse_r; Trivial ]].
Save.


Fixpoint p_rewrite [s: p_step] : proposition -> proposition :=
  Cases s of 
   | (P_LEFT s) => (p_apply_left (p_rewrite s))
   | (P_RIGHT s) => (p_apply_right (p_rewrite s))
   | (P_STEP s) => (move_right s)
   | (P_INVERT s) => (p_invert (move_right s))
   | P_NOP => [p:proposition]p
  end.

Theorem p_rewrite_stable : (s : p_step) (prop_stable (p_rewrite s)).


Induction s; Simpl; [
  Intros; Apply p_apply_left_stable; Trivial
| Intros; Apply p_apply_right_stable; Trivial
| Intros; Apply p_invert_stable; Apply move_right_stable
| Apply move_right_stable
| Unfold prop_stable; Simpl; Intros; Split; Auto ].
Save.

Fixpoint normalize_hyps [l: (list h_step)] : hyps -> hyps :=
  [lh:hyps] Cases l of
    nil => lh
  | (cons (pair_step i s) r) =>
	 (normalize_hyps r (apply_oper_1 i (p_rewrite s) lh))
  end.

Theorem normalize_hyps_valid : 
  (l: (list h_step)) (valid_hyps (normalize_hyps l)).

Induction l; Unfold valid_hyps; Simpl; [
  Auto
| Intros n_s r; Case n_s; Intros n s H ep e lp H1; Apply H; 
  Apply apply_oper_1_valid; [
    Unfold valid1; Intros ep1 e1 p1 H2; Elim (p_rewrite_stable s ep1 e1 p1);
    Auto
  | Assumption ]].
Save.

Theorem normalize_hyps_goal :
  (s: (list h_step); ep: PropList; env : (list Z); l: hyps)
    (interp_goal ep env (normalize_hyps s l)) -> 
      (interp_goal ep env l).

Intros; Apply valid_goal with 2:=H; Apply normalize_hyps_valid.
Save.

Fixpoint extract_hyp_pos [s: (list direction)] : proposition -> proposition :=
  [p: proposition]
  Cases s of 
   | (cons D_left l) =>
	Cases p of
          (Tand x y) => (extract_hyp_pos l x)
        | _ => p
        end
   | (cons D_right l) =>
	Cases p of
          (Tand x y) => (extract_hyp_pos l y)
        | _ => p
        end
   | (cons D_mono l) =>
	Cases p of
          (Tnot x ) => (extract_hyp_neg l x)
        | _ => p
        end
   | _ => p
  end
with extract_hyp_neg [s: (list direction)] : proposition -> proposition :=
  [p: proposition]
  Cases s of 
   | (cons D_left l) =>
	Cases p of
          (Tor x y) => (extract_hyp_neg l x)
	| (Timp x y) =>
	    (if (decidability x) then (extract_hyp_pos l x) else (Tnot p))
        | _ => (Tnot p)
        end
   | (cons D_right l) =>
	Cases p of
          (Tor x y) => (extract_hyp_neg l y)
	| (Timp x y) => (extract_hyp_neg l y)
        | _ => (Tnot p)
        end
   | (cons D_mono l) =>
	Cases p of
          (Tnot x) => 
	     (if (decidability x) then (extract_hyp_pos l x) else (Tnot p))
        | _ => (Tnot p)
        end
   | _ => 
	Cases p of
	  (Tnot x) => (if (decidability x) then x else (Tnot p))
        | _ => (Tnot p) 
	end
  end.

Definition co_valid1 [f: proposition -> proposition] :=
  (ep : PropList; e: (list Z)) (p1: proposition) 
     (interp_proposition ep e (Tnot p1)) -> (interp_proposition ep e (f p1)).

Theorem extract_valid : 
  (s: (list direction))
    ((valid1 (extract_hyp_pos s)) /\ (co_valid1 (extract_hyp_neg s))).

Unfold valid1 co_valid1; Induction s; [
  Split; [
    Simpl; Auto
  | Intros ep e p1; Case p1; Simpl; Auto; Intro p; Pattern (decidability p);
    Apply bool_ind2; [
      Intro H; Generalize (decidable_correct ep e p H); Unfold decidable; Tauto
    | Simpl; Auto]]
| Intros a s' (H1,H2);  Simpl in H2; Split; Intros ep e p; Case a; Auto; 
  Case p; Auto; Simpl; Intros; 
  (Apply H1; Tauto) Orelse (Apply H2; Tauto) Orelse
  (Pattern (decidability p0); Apply bool_ind2; [
     Intro H3; Generalize (decidable_correct ep e p0 H3);Unfold decidable;
     Intro H4; Apply H1; Tauto
   | Intro; Tauto ])].

Save.

Fixpoint decompose_solve [s: e_step] : hyps -> lhyps := 
 [h:hyps]
 Cases s of 
   (E_SPLIT i dl s1 s2) => 
	(Cases (extract_hyp_pos dl (nth_hyps i h)) of
	   (Tor x y) => 
	      (app (decompose_solve s1 (cons x h)) 
	           (decompose_solve s2 (cons y h)))
	|  (Tnot (Tand x y)) => 
	      (if (decidability x) then
		      (app (decompose_solve s1 (cons (Tnot x) h)) 
		           (decompose_solve s2 (cons (Tnot y) h)))
		else (cons h (nil hyps)))
	| _ => (cons h (nil hyps))
	end)
 | (E_EXTRACT i dl s1) =>
     (decompose_solve s1 (cons (extract_hyp_pos dl (nth_hyps i h)) h))
 | (E_SOLVE t) => (execute_omega t h)
 end.

Theorem decompose_solve_valid : 
   (s:e_step)(valid_list_goal (decompose_solve s)).

Intro s; Apply goal_valid; Unfold valid_list_hyps; Elim s; Simpl; Intros; [
  Cut (interp_proposition ep e1 (extract_hyp_pos l (nth_hyps n lp))); [
    Case (extract_hyp_pos l (nth_hyps n lp)); Simpl; Auto; [
      Intro p; Case p; Simpl;Auto; Intros p1 p2 H2;
      Pattern (decidability p1); Apply bool_ind2; [
        Intro H3; Generalize (decidable_correct ep e1 p1 H3); 
        Intro H4; Apply append_valid; Elim H4; Intro H5; [
          Right; Apply H0; Simpl; Tauto
        | Left; Apply H; Simpl; Tauto ]
      | Simpl; Auto]
    | Intros p1 p2 H2; Apply append_valid; Simpl; Elim H2; [
        Intros H3; Left; Apply H; Simpl; Auto
      | Intros H3; Right; Apply H0; Simpl; Auto ]]
  | Elim (extract_valid l); Intros H2 H3; Apply H2; Apply nth_valid; Auto]
| Intros; Apply H; Simpl; Split; [
    Elim (extract_valid l); Intros H2 H3; Apply H2; Apply nth_valid; Auto
  | Auto ]
| Apply omega_valid with 1:= H].

Save.

(* \subsection{La dernière étape qui élimine tous les séquents inutiles} *)

Definition valid_lhyps [f: lhyps -> lhyps] :=
  (ep : PropList; e : (list Z)) (lp: lhyps)
    (interp_list_hyps ep e lp) -> (interp_list_hyps ep e (f lp)).

Fixpoint reduce_lhyps [lp:lhyps] : lhyps :=
   Cases lp of
     (cons (cons FalseTerm nil) lp') => (reduce_lhyps lp')
   | (cons x lp') => (cons x (reduce_lhyps lp'))
   | nil => (nil hyps)
   end.

Theorem reduce_lhyps_valid : (valid_lhyps reduce_lhyps).

Unfold valid_lhyps; Intros ep e lp; Elim lp; [
  Simpl; Auto
| Intros a l HR; Elim a; [
    Simpl; Tauto
  | Intros a1 l1; Case l1; Case a1; Simpl; Try Tauto]].
Save.

Theorem do_reduce_lhyps : 
  (envp: PropList; env: (list Z); l: lhyps)
    (interp_list_goal envp env (reduce_lhyps l)) ->
	 (interp_list_goal envp env l).

Intros envp env l H; Apply list_goal_to_hyps; Intro H1; 
Apply list_hyps_to_goal with 1 := H; Apply reduce_lhyps_valid; Assumption.
Save.

Definition concl_to_hyp := [p:proposition]
  (if (decidability p) then (Tnot p) else TrueTerm).

Definition do_concl_to_hyp :
  (envp: PropList; env: (list Z); c : proposition; l:hyps)
    (interp_goal envp env (cons (concl_to_hyp c) l)) ->
       (interp_goal_concl c envp env l).

Simpl; Intros envp env c l; Induction l; [
  Simpl; Unfold concl_to_hyp; Pattern (decidability c); Apply bool_ind2; [
    Intro H; Generalize (decidable_correct envp env c H); Unfold decidable;
    Simpl; Tauto
  | Simpl; Intros H1 H2; Elim H2; Trivial]
| Simpl; Tauto ].
Save.

Definition omega_tactic := 
  [t1:e_step ; t2:(list h_step) ; c:proposition; l:hyps] 
    (reduce_lhyps 
      (decompose_solve t1 (normalize_hyps t2 (cons (concl_to_hyp c) l)))).

Theorem do_omega:
  (t1: e_step ; t2: (list h_step);
   envp: PropList; env: (list Z); c: proposition; l:hyps)
    (interp_list_goal envp env (omega_tactic t1 t2 c l)) ->
       (interp_goal_concl c envp env l).

Unfold omega_tactic; Intros; Apply do_concl_to_hyp; 
Apply (normalize_hyps_goal t2); Apply (decompose_solve_valid t1); 
Apply do_reduce_lhyps; Assumption.
Save.
