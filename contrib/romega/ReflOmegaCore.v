(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence du projet : LGPL version 2.1

 *************************************************************************)

Require Import Arith.
Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import OmegaLemmas.

(* \subsection{Definition of basic types} *)

(* \subsubsection{Environment of propositions (lists) *)
Inductive PropList : Type :=
  | Pnil : PropList
  | Pcons : Prop -> PropList -> PropList.

(* Access function for the environment with a default *)
Fixpoint nthProp (n : nat) (l : PropList) (default : Prop) {struct l} :
 Prop :=
  match n, l with
  | O, Pcons x l' => x
  | O, other => default
  | S m, Pnil => default
  | S m, Pcons x t => nthProp m t default
  end.
   
(* \subsubsection{Définition of reified integer expressions}
   Terms are either:
   \begin{itemize}
   \item integers [Tint]
   \item variables [Tvar]
   \item operation over integers (addition, product, opposite, subtraction)
   The last two are translated in additions and products. *)

Inductive term : Set :=
  | Tint : Z -> term
  | Tplus : term -> term -> term
  | Tmult : term -> term -> term
  | Tminus : term -> term -> term
  | Topp : term -> term
  | Tvar : nat -> term.

(* \subsubsection{Definition of reified goals} *)
(* Very restricted definition of handled predicates that should be extended
   to cover a wider set of operations.
   Taking care of negations and disequations require solving more than a
   goal in parallel. This is a major improvement over previous versions. *)

Inductive proposition : Set :=
  | EqTerm : term -> term -> proposition (* egalité entre termes *)
  | LeqTerm : term -> term -> proposition (* plus petit ou egal *)
  | TrueTerm : proposition (* vrai *)
  | FalseTerm : proposition (* faux *)
  | Tnot : proposition -> proposition (* négation *)
  | GeqTerm : term -> term -> proposition
  | GtTerm : term -> term -> proposition
  | LtTerm : term -> term -> proposition
  | NeqTerm : term -> term -> proposition
  | Tor : proposition -> proposition -> proposition
  | Tand : proposition -> proposition -> proposition
  | Timp : proposition -> proposition -> proposition
  | Tprop : nat -> proposition.

(* Definition of goals as a list of hypothesis *)
Notation hyps := (list proposition) (only parsing).      

(* Definition of lists of subgoals  (set of open goals) *)
Notation lhyps := (list (list proposition)) (only parsing).

(* a syngle goal packed in a subgoal list *)
Notation singleton := (fun a : list proposition => a :: nil) (only parsing).

(* an absurd goal *)
Definition absurd := FalseTerm :: nil.

(* \subsubsection{Traces for merging equations}
   This inductive type describes how the monomial of two equations should be
   merged when the equations are added.

   For [F_equal], both equations have the same head variable and coefficient
   must be added, furthermore if coefficients are opposite, [F_cancel] should
   be used to collapse the term. [F_left] and [F_right] indicate which monomial
   should be put first in the result *)

Inductive t_fusion : Set :=
  | F_equal : t_fusion
  | F_cancel : t_fusion
  | F_left : t_fusion
  | F_right : t_fusion.

(* \subsubsection{Rewriting steps to normalize terms} *)
Inductive step : Set := 
 (* apply the rewriting steps to both subterms of an operation *)
  | C_DO_BOTH :
      step -> step -> step
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
  | C_OPP_ONE :
      step
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
  | C_MINUS : step
  | C_MULT_SYM : step.

(* \subsubsection{Omega steps} *)
(* The following inductive type describes steps as they can be found in
   the trace coming from the decision procedure Omega. *)

Inductive t_omega : Set :=
 (* n = 0 n!= 0 *)
  | O_CONSTANT_NOT_NUL : nat -> t_omega
  | O_CONSTANT_NEG :
      nat -> t_omega
      (* division et approximation of an equation *)
  | O_DIV_APPROX :
      Z ->
      Z ->
      term ->
      nat ->
      t_omega -> nat -> t_omega
                 (* no solution because no exact division *)
  | O_NOT_EXACT_DIVIDE :
      Z -> Z -> term -> nat -> nat -> t_omega
                               (* exact division *)
  | O_EXACT_DIVIDE : Z -> term -> nat -> t_omega -> nat -> t_omega
  | O_SUM : Z -> nat -> Z -> nat -> list t_fusion -> t_omega -> t_omega
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
  | P_LEFT : p_step -> p_step
  | P_RIGHT : p_step -> p_step
  | P_INVERT : step -> p_step
  | P_STEP : step -> p_step
  | P_NOP : p_step.
(* Liste des normalisations a effectuer : avec un constructeur dans le
   type [p_step] permettant
   de parcourir à la fois les branches gauches et droit, on pourrait n'avoir
   qu'une normalisation par hypothèse. Et comme toutes les hypothèses sont 
   utiles (sinon on ne les incluerait pas), on pourrait remplacer [h_step] 
   par une simple liste *)

Inductive h_step : Set :=
    pair_step : nat -> p_step -> h_step.

(* \subsubsection{Règles pour décomposer les hypothèses} *)
(* Ce type permet de se diriger dans les constructeurs logiques formant les
   prédicats des hypothèses pour aller les décomposer. Ils permettent
   en particulier d'extraire une hypothèse d'une conjonction avec
   éventuellement le bon niveau de négations. *)

Inductive direction : Set :=
  | D_left : direction
  | D_right : direction
  | D_mono : direction.

(* Ce type permet d'extraire les composants utiles des hypothèses : que ce
   soit des hypothèses générées par éclatement d'une disjonction, ou 
   des équations. Le constructeur terminal indique comment résoudre le système
   obtenu en recourrant au type de trace d'Omega [t_omega] *)

Inductive e_step : Set :=
  | E_SPLIT : nat -> list direction -> e_step -> e_step -> e_step
  | E_EXTRACT : nat -> list direction -> e_step -> e_step
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

Ltac absurd_case := simpl in |- *; intros; discriminate.
Ltac trivial_case := unfold not in |- *; intros; discriminate.

(* \subsubsection{Entiers naturels} *)

Fixpoint eq_nat (t1 t2 : nat) {struct t2} : bool :=
  match t1 with
  | O => match t2 with
         | O => true
         | _ => false
         end
  | S n1 => match t2 with
            | O => false
            | S n2 => eq_nat n1 n2
            end
  end.

Theorem eq_nat_true : forall t1 t2 : nat, eq_nat t1 t2 = true -> t1 = t2.

simple induction t1;
 [ intro t2; case t2; [ trivial | absurd_case ]
 | intros n H t2; case t2;
    [ absurd_case
    | simpl in |- *; intros; rewrite (H n0); [ trivial | assumption ] ] ].

Qed.
  
Theorem eq_nat_false : forall t1 t2 : nat, eq_nat t1 t2 = false -> t1 <> t2.

simple induction t1;
 [ intro t2; case t2; [ simpl in |- *; intros; discriminate | trivial_case ]
 | intros n H t2; case t2; simpl in |- *; unfold not in |- *; intros;
    [ discriminate | elim (H n0 H0); simplify_eq H1; trivial ] ].

Qed.
                                   

(* \subsubsection{Entiers positifs} *)

Fixpoint eq_pos (p1 p2 : positive) {struct p2} : bool :=
  match p1 with
  | xI n1 => match p2 with
             | xI n2 => eq_pos n1 n2
             | _ => false
             end
  | xO n1 => match p2 with
             | xO n2 => eq_pos n1 n2
             | _ => false
             end
  | xH => match p2 with
          | xH => true
          | _ => false
          end
  end.

Theorem eq_pos_true : forall t1 t2 : positive, eq_pos t1 t2 = true -> t1 = t2.

simple induction t1;
 [ intros p H t2; case t2;
    [ simpl in |- *; intros; rewrite (H p0 H0); trivial
    | absurd_case
    | absurd_case ]
 | intros p H t2; case t2;
    [ absurd_case
    | simpl in |- *; intros; rewrite (H p0 H0); trivial
    | absurd_case ]
 | intro t2; case t2; [ absurd_case | absurd_case | auto ] ].

Qed.
  
Theorem eq_pos_false :
 forall t1 t2 : positive, eq_pos t1 t2 = false -> t1 <> t2.

simple induction t1;
 [ intros p H t2; case t2;
    [ simpl in |- *; unfold not in |- *; intros; elim (H p0 H0);
       simplify_eq H1; auto
    | trivial_case
    | trivial_case ]
 | intros p H t2; case t2;
    [ trivial_case
    | simpl in |- *; unfold not in |- *; intros; elim (H p0 H0);
       simplify_eq H1; auto
    | trivial_case ]
 | intros t2; case t2; [ trivial_case | trivial_case | absurd_case ] ].
Qed.

(* \subsubsection{Entiers relatifs} *)

Definition eq_Z (z1 z2 : Z) : bool :=
  match z1 with
  | Z0 => match z2 with
          | Z0 => true
          | _ => false
          end
  | Zpos p1 => match z2 with
               | Zpos p2 => eq_pos p1 p2
               | _ => false
               end
  | Zneg p1 => match z2 with
               | Zneg p2 => eq_pos p1 p2
               | _ => false
               end
  end.

Theorem eq_Z_true : forall t1 t2 : Z, eq_Z t1 t2 = true -> t1 = t2.

simple induction t1;
 [ intros t2; case t2; [ auto | absurd_case | absurd_case ]
 | intros p t2; case t2;
    [ absurd_case
    | simpl in |- *; intros; rewrite (eq_pos_true p p0 H); trivial
    | absurd_case ]
 | intros p t2; case t2;
    [ absurd_case
    | absurd_case
    | simpl in |- *; intros; rewrite (eq_pos_true p p0 H); trivial ] ].

Qed.

Theorem eq_Z_false : forall t1 t2 : Z, eq_Z t1 t2 = false -> t1 <> t2.

simple induction t1;
 [ intros t2; case t2; [ absurd_case | trivial_case | trivial_case ]
 | intros p t2; case t2;
    [ absurd_case
    | simpl in |- *; unfold not in |- *; intros; elim (eq_pos_false p p0 H);
       simplify_eq H0; auto
    | trivial_case ]
 | intros p t2; case t2;
    [ absurd_case
    | trivial_case
    | simpl in |- *; unfold not in |- *; intros; elim (eq_pos_false p p0 H);
       simplify_eq H0; auto ] ].
Qed.

(* \subsubsection{Termes réifiés} *)

Fixpoint eq_term (t1 t2 : term) {struct t2} : bool :=
  match t1 with
  | Tint st1 => match t2 with
                | Tint st2 => eq_Z st1 st2
                | _ => false
                end
  | Tplus st11 st12 =>
      match t2 with
      | Tplus st21 st22 => eq_term st11 st21 && eq_term st12 st22
      | _ => false
      end
  | Tmult st11 st12 =>
      match t2 with
      | Tmult st21 st22 => eq_term st11 st21 && eq_term st12 st22
      | _ => false
      end
  | Tminus st11 st12 =>
      match t2 with
      | Tminus st21 st22 => eq_term st11 st21 && eq_term st12 st22
      | _ => false
      end
  | Topp st1 => match t2 with
                | Topp st2 => eq_term st1 st2
                | _ => false
                end
  | Tvar st1 => match t2 with
                | Tvar st2 => eq_nat st1 st2
                | _ => false
                end
  end.  

Theorem eq_term_true : forall t1 t2 : term, eq_term t1 t2 = true -> t1 = t2.


simple induction t1; intros until t2; case t2; try absurd_case; simpl in |- *;
 [ intros; elim eq_Z_true with (1 := H); trivial
 | intros t21 t22 H3; elim andb_prop with (1 := H3); intros H4 H5;
    elim H with (1 := H4); elim H0 with (1 := H5); 
    trivial
 | intros t21 t22 H3; elim andb_prop with (1 := H3); intros H4 H5;
    elim H with (1 := H4); elim H0 with (1 := H5); 
    trivial
 | intros t21 t22 H3; elim andb_prop with (1 := H3); intros H4 H5;
    elim H with (1 := H4); elim H0 with (1 := H5); 
    trivial
 | intros t21 H3; elim H with (1 := H3); trivial
 | intros; elim eq_nat_true with (1 := H); trivial ].

Qed.

Theorem eq_term_false :
 forall t1 t2 : term, eq_term t1 t2 = false -> t1 <> t2.

simple induction t1;
 [ intros z t2; case t2; try trivial_case; simpl in |- *; unfold not in |- *;
    intros; elim eq_Z_false with (1 := H); simplify_eq H0; 
    auto
 | intros t11 H1 t12 H2 t2; case t2; try trivial_case; simpl in |- *;
    intros t21 t22 H3; unfold not in |- *; intro H4;
    elim andb_false_elim with (1 := H3); intros H5;
    [ elim H1 with (1 := H5); simplify_eq H4; auto
    | elim H2 with (1 := H5); simplify_eq H4; auto ]
 | intros t11 H1 t12 H2 t2; case t2; try trivial_case; simpl in |- *;
    intros t21 t22 H3; unfold not in |- *; intro H4;
    elim andb_false_elim with (1 := H3); intros H5;
    [ elim H1 with (1 := H5); simplify_eq H4; auto
    | elim H2 with (1 := H5); simplify_eq H4; auto ]
 | intros t11 H1 t12 H2 t2; case t2; try trivial_case; simpl in |- *;
    intros t21 t22 H3; unfold not in |- *; intro H4;
    elim andb_false_elim with (1 := H3); intros H5;
    [ elim H1 with (1 := H5); simplify_eq H4; auto
    | elim H2 with (1 := H5); simplify_eq H4; auto ]
 | intros t11 H1 t2; case t2; try trivial_case; simpl in |- *; intros t21 H3;
    unfold not in |- *; intro H4; elim H1 with (1 := H3); 
    simplify_eq H4; auto
 | intros n t2; case t2; try trivial_case; simpl in |- *; unfold not in |- *;
    intros; elim eq_nat_false with (1 := H); simplify_eq H0; 
    auto ].

Qed.

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
 forall (P : bool -> Prop) (b : bool),
 (b = true -> P true) -> (b = false -> P false) -> P b.

simple induction b; auto.
Qed.

(* Les tactiques définies si après se comportent exactement comme si on
   avait utilisé le test précédent et fait une elimination dessus. *)

Ltac elim_eq_term t1 t2 :=
  pattern (eq_term t1 t2) in |- *; apply bool_ind2; intro Aux;
   [ generalize (eq_term_true t1 t2 Aux); clear Aux
   | generalize (eq_term_false t1 t2 Aux); clear Aux ].

Ltac elim_eq_Z t1 t2 :=
  pattern (eq_Z t1 t2) in |- *; apply bool_ind2; intro Aux;
   [ generalize (eq_Z_true t1 t2 Aux); clear Aux
   | generalize (eq_Z_false t1 t2 Aux); clear Aux ].

Ltac elim_eq_pos t1 t2 :=
  pattern (eq_pos t1 t2) in |- *; apply bool_ind2; intro Aux;
   [ generalize (eq_pos_true t1 t2 Aux); clear Aux
   | generalize (eq_pos_false t1 t2 Aux); clear Aux ].

(* \subsubsection{Comparaison sur Z} *)

(* Sujet très lié au précédent : on introduit la tactique d'élimination
   avec son théorème *)

Theorem relation_ind2 :
 forall (P : Datatypes.comparison -> Prop) (b : Datatypes.comparison),
 (b = Datatypes.Eq -> P Datatypes.Eq) ->
 (b = Datatypes.Lt -> P Datatypes.Lt) ->
 (b = Datatypes.Gt -> P Datatypes.Gt) -> P b.

simple induction b; auto.
Qed.

Ltac elim_Zcompare t1 t2 := pattern (t1 ?= t2)%Z in |- *; apply relation_ind2.

(* \subsection{Interprétations}
   \subsubsection{Interprétation des termes dans Z} *)

Fixpoint interp_term (env : list Z) (t : term) {struct t} : Z :=
  match t with
  | Tint x => x
  | Tplus t1 t2 => (interp_term env t1 + interp_term env t2)%Z
  | Tmult t1 t2 => (interp_term env t1 * interp_term env t2)%Z
  | Tminus t1 t2 => (interp_term env t1 - interp_term env t2)%Z
  | Topp t => (- interp_term env t)%Z
  | Tvar n => nth n env 0%Z
  end.

(* \subsubsection{Interprétation des prédicats} *) 
Fixpoint interp_proposition (envp : PropList) (env : list Z)
 (p : proposition) {struct p} : Prop :=
  match p with
  | EqTerm t1 t2 => interp_term env t1 = interp_term env t2
  | LeqTerm t1 t2 => (interp_term env t1 <= interp_term env t2)%Z
  | TrueTerm => True
  | FalseTerm => False
  | Tnot p' => ~ interp_proposition envp env p'
  | GeqTerm t1 t2 => (interp_term env t1 >= interp_term env t2)%Z
  | GtTerm t1 t2 => (interp_term env t1 > interp_term env t2)%Z
  | LtTerm t1 t2 => (interp_term env t1 < interp_term env t2)%Z
  | NeqTerm t1 t2 => Zne (interp_term env t1) (interp_term env t2)
  | Tor p1 p2 =>
      interp_proposition envp env p1 \/ interp_proposition envp env p2
  | Tand p1 p2 =>
      interp_proposition envp env p1 /\ interp_proposition envp env p2
  | Timp p1 p2 =>
      interp_proposition envp env p1 -> interp_proposition envp env p2
  | Tprop n => nthProp n envp True
  end.

(* \subsubsection{Inteprétation des listes d'hypothèses}
   \paragraph{Sous forme de conjonction}
   Interprétation sous forme d'une conjonction d'hypothèses plus faciles
   à manipuler individuellement *)

Fixpoint interp_hyps (envp : PropList) (env : list Z) 
 (l : list proposition) {struct l} : Prop :=
  match l with
  | nil => True
  | p' :: l' => interp_proposition envp env p' /\ interp_hyps envp env l'
  end.

(* \paragraph{sous forme de but}
   C'est cette interpétation que l'on utilise sur le but (car on utilise
   [Generalize] et qu'une conjonction est forcément lourde (répétition des
   types dans les conjonctions intermédiaires) *)

Fixpoint interp_goal_concl (envp : PropList) (env : list Z) 
 (c : proposition) (l : list proposition) {struct l} : Prop :=
  match l with
  | nil => interp_proposition envp env c
  | p' :: l' =>
      interp_proposition envp env p' -> interp_goal_concl envp env c l'
  end.

Notation interp_goal :=
  (fun (envp : PropList) (env : list Z) (l : list proposition) =>
   interp_goal_concl envp env FalseTerm l) (only parsing).

(* Les théorèmes qui suivent assurent la correspondance entre les deux
   interprétations. *)

Theorem goal_to_hyps :
 forall (envp : PropList) (env : list Z) (l : list proposition),
 (interp_hyps envp env l -> False) ->
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) envp env l.

simple induction l;
 [ simpl in |- *; auto
 | simpl in |- *; intros a l1 H1 H2 H3; apply H1; intro H4; apply H2; auto ].
Qed.

Theorem hyps_to_goal :
 forall (envp : PropList) (env : list Z) (l : list proposition),
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) envp env l ->
 interp_hyps envp env l -> False.

simple induction l; simpl in |- *; [ auto | intros; apply H; elim H1; auto ].
Qed.
      
(* \subsection{Manipulations sur les hypothèses} *)

(* \subsubsection{Définitions de base de stabilité pour la réflexion} *)
(* Une opération laisse un terme stable si l'égalité est préservée *)
Definition term_stable (f : term -> term) :=
  forall (e : list Z) (t : term), interp_term e t = interp_term e (f t).

(* Une opération est valide sur une hypothèse, si l'hypothèse implique le
   résultat de l'opération. \emph{Attention : cela ne concerne que des 
   opérations sur les hypothèses et non sur les buts (contravariance)}.
   On définit la validité pour une opération prenant une ou deux propositions
   en argument (cela suffit pour omega). *)

Definition valid1 (f : proposition -> proposition) :=
  forall (ep : PropList) (e : list Z) (p1 : proposition),
  interp_proposition ep e p1 -> interp_proposition ep e (f p1).

Definition valid2 (f : proposition -> proposition -> proposition) :=
  forall (ep : PropList) (e : list Z) (p1 p2 : proposition),
  interp_proposition ep e p1 ->
  interp_proposition ep e p2 -> interp_proposition ep e (f p1 p2).

(* Dans cette notion de validité, la fonction prend directement une 
   liste de propositions et rend une nouvelle liste de proposition. 
   On reste contravariant *)

Definition valid_hyps (f : list proposition -> list proposition) :=
  forall (ep : PropList) (e : list Z) (lp : list proposition),
  interp_hyps ep e lp -> interp_hyps ep e (f lp).

(* Enfin ce théorème élimine la contravariance et nous ramène à une 
   opération sur les buts *)

 Theorem valid_goal :
  forall (ep : PropList) (env : list Z) (l : list proposition)
    (a : list proposition -> list proposition),
  valid_hyps a ->
  (fun (envp : PropList) (env : list Z) (l : list proposition) =>
   interp_goal_concl envp env FalseTerm l) ep env (
    a l) ->
  (fun (envp : PropList) (env : list Z) (l : list proposition) =>
   interp_goal_concl envp env FalseTerm l) ep env l.

intros; simpl in |- *; apply goal_to_hyps; intro H1;
 apply (hyps_to_goal ep env (a l) H0); apply H; assumption.
Qed.

(* \subsubsection{Généralisation a des listes de buts (disjonctions)} *)


Fixpoint interp_list_hyps (envp : PropList) (env : list Z)
 (l : list (list proposition)) {struct l} : Prop :=
  match l with
  | nil => False
  | h :: l' => interp_hyps envp env h \/ interp_list_hyps envp env l'
  end.

Fixpoint interp_list_goal (envp : PropList) (env : list Z)
 (l : list (list proposition)) {struct l} : Prop :=
  match l with
  | nil => True
  | h :: l' =>
      (fun (envp : PropList) (env : list Z) (l : list proposition) =>
       interp_goal_concl envp env FalseTerm l) envp env h /\
      interp_list_goal envp env l'
  end.

Theorem list_goal_to_hyps :
 forall (envp : PropList) (env : list Z) (l : list (list proposition)),
 (interp_list_hyps envp env l -> False) -> interp_list_goal envp env l.

simple induction l; simpl in |- *;
 [ auto
 | intros h1 l1 H H1; split;
    [ apply goal_to_hyps; intro H2; apply H1; auto
    | apply H; intro H2; apply H1; auto ] ].
Qed.

Theorem list_hyps_to_goal :
 forall (envp : PropList) (env : list Z) (l : list (list proposition)),
 interp_list_goal envp env l -> interp_list_hyps envp env l -> False.

simple induction l; simpl in |- *;
 [ auto
 | intros h1 l1 H (H1, H2) H3; elim H3; intro H4;
    [ apply hyps_to_goal with (1 := H1); assumption | auto ] ].
Qed.

Definition valid_list_hyps
  (f : list proposition -> list (list proposition)) :=
  forall (ep : PropList) (e : list Z) (lp : list proposition),
  interp_hyps ep e lp -> interp_list_hyps ep e (f lp).

Definition valid_list_goal
  (f : list proposition -> list (list proposition)) :=
  forall (ep : PropList) (e : list Z) (lp : list proposition),
  interp_list_goal ep e (f lp) ->
  (fun (envp : PropList) (env : list Z) (l : list proposition) =>
   interp_goal_concl envp env FalseTerm l) ep e lp.

Theorem goal_valid :
 forall f : list proposition -> list (list proposition),
 valid_list_hyps f -> valid_list_goal f.

unfold valid_list_goal in |- *; intros f H ep e lp H1; apply goal_to_hyps;
 intro H2; apply list_hyps_to_goal with (1 := H1); 
 apply (H ep e lp); assumption.
Qed.
 
Theorem append_valid :
 forall (ep : PropList) (e : list Z) (l1 l2 : list (list proposition)),
 interp_list_hyps ep e l1 \/ interp_list_hyps ep e l2 ->
 interp_list_hyps ep e (l1 ++ l2).

intros ep e; simple induction l1;
 [ simpl in |- *; intros l2 [H| H]; [ contradiction | trivial ]
 | simpl in |- *; intros h1 t1 HR l2 [[H| H]| H];
    [ auto
    | right; apply (HR l2); left; trivial
    | right; apply (HR l2); right; trivial ] ].

Qed.

(* \subsubsection{Opérateurs valides sur les hypothèses} *)

(* Extraire une hypothèse de la liste *)
Definition nth_hyps (n : nat) (l : list proposition) := nth n l TrueTerm.

Theorem nth_valid :
 forall (ep : PropList) (e : list Z) (i : nat) (l : list proposition),
 interp_hyps ep e l -> interp_proposition ep e (nth_hyps i l).

unfold nth_hyps in |- *; simple induction i;
 [ simple induction l; simpl in |- *; [ auto | intros; elim H0; auto ]
 | intros n H; simple induction l;
    [ simpl in |- *; trivial
    | intros; simpl in |- *; apply H; elim H1; auto ] ].
Qed.

(* Appliquer une opération (valide) sur deux hypothèses extraites de 
   la liste et ajouter le résultat à la liste. *)
Definition apply_oper_2 (i j : nat)
  (f : proposition -> proposition -> proposition) (l : list proposition) :=
  f (nth_hyps i l) (nth_hyps j l) :: l.

Theorem apply_oper_2_valid :
 forall (i j : nat) (f : proposition -> proposition -> proposition),
 valid2 f -> valid_hyps (apply_oper_2 i j f).

intros i j f Hf; unfold apply_oper_2, valid_hyps in |- *; simpl in |- *;
 intros lp Hlp; split; [ apply Hf; apply nth_valid; assumption | assumption ].
Qed.

(* Modifier une hypothèse par application d'une opération valide *)

Fixpoint apply_oper_1 (i : nat) (f : proposition -> proposition)
 (l : list proposition) {struct i} : list proposition :=
  match l with
  | nil => nil (A:=proposition)
  | p :: l' =>
      match i with
      | O => f p :: l'
      | S j => p :: apply_oper_1 j f l'
      end
  end.

Theorem apply_oper_1_valid :
 forall (i : nat) (f : proposition -> proposition),
 valid1 f -> valid_hyps (apply_oper_1 i f).

unfold valid_hyps in |- *; intros i f Hf ep e; elim i;
 [ intro lp; case lp;
    [ simpl in |- *; trivial
    | simpl in |- *; intros p l' (H1, H2); split;
       [ apply Hf with (1 := H1) | assumption ] ]
 | intros n Hrec lp; case lp;
    [ simpl in |- *; auto
    | simpl in |- *; intros p l' (H1, H2); split;
       [ assumption | apply Hrec; assumption ] ] ].

Qed.

(* \subsubsection{Manipulations de termes} *)
(* Les fonctions suivantes permettent d'appliquer une fonction de
   réécriture sur un sous terme du terme principal. Avec la composition,
   cela permet de construire des réécritures complexes proches des 
   tactiques de conversion *)

Definition apply_left (f : term -> term) (t : term) :=
  match t with
  | Tplus x y => Tplus (f x) y
  | Tmult x y => Tmult (f x) y
  | Topp x => Topp (f x)
  | x => x
  end.

Definition apply_right (f : term -> term) (t : term) :=
  match t with
  | Tplus x y => Tplus x (f y)
  | Tmult x y => Tmult x (f y)
  | x => x
  end.

Definition apply_both (f g : term -> term) (t : term) :=
  match t with
  | Tplus x y => Tplus (f x) (g y)
  | Tmult x y => Tmult (f x) (g y)
  | x => x
  end.

(* Les théorèmes suivants montrent la stabilité (conditionnée) des 
   fonctions. *)

Theorem apply_left_stable :
 forall f : term -> term, term_stable f -> term_stable (apply_left f).

unfold term_stable in |- *; intros f H e t; case t; auto; simpl in |- *;
 intros; elim H; trivial.
Qed.

Theorem apply_right_stable :
 forall f : term -> term, term_stable f -> term_stable (apply_right f).

unfold term_stable in |- *; intros f H e t; case t; auto; simpl in |- *;
 intros t0 t1; elim H; trivial.
Qed.

Theorem apply_both_stable :
 forall f g : term -> term,
 term_stable f -> term_stable g -> term_stable (apply_both f g).

unfold term_stable in |- *; intros f g H1 H2 e t; case t; auto; simpl in |- *;
 intros t0 t1; elim H1; elim H2; trivial.
Qed.

Theorem compose_term_stable :
 forall f g : term -> term,
 term_stable f -> term_stable g -> term_stable (fun t : term => f (g t)).

unfold term_stable in |- *; intros f g Hf Hg e t; elim Hf; apply Hg.
Qed.

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

Ltac loop t :=
  match constr:t with
  | (?X1 = ?X2) => 
                    (* Global *)
                    loop X1 || loop X2
  | (_ -> ?X1) => loop X1
  | (interp_hyps _ _ ?X1) =>
      
  (* Interpretations *)
  loop X1
  | (interp_list_hyps _ _ ?X1) => loop X1
  | (interp_proposition _ _ ?X1) => loop X1
  | (interp_term _ ?X1) => loop X1
  | (EqTerm ?X1 ?X2) =>
      
       (* Propositions *)
       loop X1 || loop X2
  | (LeqTerm ?X1 ?X2) => loop X1 || loop X2
  | (Tplus ?X1 ?X2) => 
                        (* Termes *)
                        loop X1 || loop X2
  | (Tminus ?X1 ?X2) => loop X1 || loop X2
  | (Tmult ?X1 ?X2) => loop X1 || loop X2
  | (Topp ?X1) => loop X1
  | (Tint ?X1) =>
      loop X1
  | match ?X1 with
    | EqTerm x x0 => _
    | LeqTerm x x0 => _
    | TrueTerm => _
    | FalseTerm => _
    | Tnot x => _
    | GeqTerm x x0 => _
    | GtTerm x x0 => _
    | LtTerm x x0 => _
    | NeqTerm x x0 => _
    | Tor x x0 => _
    | Tand x x0 => _
    | Timp x x0 => _
    | Tprop x => _
    end =>
      
       (* Eliminations *)
       case X1;
       [ intro; intro
       | intro; intro
       | idtac
       | idtac
       | intro
       | intro; intro
       | intro; intro
       | intro; intro
       | intro; intro
       | intro; intro
       | intro; intro
       | intro; intro
       | intro ]; auto; Simplify
  | match ?X1 with
    | Tint x => _
    | Tplus x x0 => _
    | Tmult x x0 => _
    | Tminus x x0 => _
    | Topp x => _
    | Tvar x => _
    end =>
      case X1;
       [ intro | intro; intro | intro; intro | intro; intro | intro | intro ];
       auto; Simplify
  | match (?X1 ?= ?X2)%Z with
    | Datatypes.Eq => _
    | Datatypes.Lt => _
    | Datatypes.Gt => _
    end =>
      elim_Zcompare X1 X2; intro; auto; Simplify
  | match ?X1 with
    | Z0 => _
    | Zpos x => _
    | Zneg x => _
    end =>
      case X1; [ idtac | intro | intro ]; auto; Simplify
  | (if eq_Z ?X1 ?X2 then _ else _) =>
      elim_eq_Z X1 X2; intro H; [ rewrite H; clear H | clear H ];
       simpl in |- *; auto; Simplify
  | (if eq_term ?X1 ?X2 then _ else _) =>
      elim_eq_term X1 X2; intro H; [ rewrite H; clear H | clear H ];
       simpl in |- *; auto; Simplify
  | (if eq_pos ?X1 ?X2 then _ else _) =>
      elim_eq_pos X1 X2; intro H; [ rewrite H; clear H | clear H ];
       simpl in |- *; auto; Simplify
  | _ => fail
  end
 with Simplify := match goal with
                  |  |- ?X1 => try loop X1
                  | _ => idtac
                  end.


Ltac prove_stable x th :=
  match constr:x with
  | ?X1 =>
      unfold term_stable, X1 in |- *; intros; Simplify; simpl in |- *;
       apply th
  end.

(* \subsubsection{Les règles elle mêmes} *)
Definition Tplus_assoc_l (t : term) :=
  match t with
  | Tplus n (Tplus m p) => Tplus (Tplus n m) p
  | _ => t
  end.

Theorem Tplus_assoc_l_stable : term_stable Tplus_assoc_l.

prove_stable Tplus_assoc_l Zplus_assoc.
Qed.

Definition Tplus_assoc_r (t : term) :=
  match t with
  | Tplus (Tplus n m) p => Tplus n (Tplus m p)
  | _ => t
  end.

Theorem Tplus_assoc_r_stable : term_stable Tplus_assoc_r.

prove_stable Tplus_assoc_r Zplus_assoc_reverse.
Qed.

Definition Tmult_assoc_r (t : term) :=
  match t with
  | Tmult (Tmult n m) p => Tmult n (Tmult m p)
  | _ => t
  end.

Theorem Tmult_assoc_r_stable : term_stable Tmult_assoc_r.

prove_stable Tmult_assoc_r Zmult_assoc_reverse.
Qed.

Definition Tplus_permute (t : term) :=
  match t with
  | Tplus n (Tplus m p) => Tplus m (Tplus n p)
  | _ => t
  end.

Theorem Tplus_permute_stable : term_stable Tplus_permute.

prove_stable Tplus_permute Zplus_permute.
Qed.

Definition Tplus_sym (t : term) :=
  match t with
  | Tplus x y => Tplus y x
  | _ => t
  end.

Theorem Tplus_sym_stable : term_stable Tplus_sym.

prove_stable Tplus_sym Zplus_comm.
Qed.

Definition Tmult_sym (t : term) :=
  match t with
  | Tmult x y => Tmult y x
  | _ => t
  end.

Theorem Tmult_sym_stable : term_stable Tmult_sym.

prove_stable Tmult_sym Zmult_comm.
Qed.

Definition T_OMEGA10 (t : term) :=
  match t with
  | Tplus (Tmult (Tplus (Tmult v (Tint c1)) l1) (Tint k1)) (Tmult (Tplus
    (Tmult v' (Tint c2)) l2) (Tint k2)) =>
      match eq_term v v' with
      | true =>
          Tplus (Tmult v (Tint (c1 * k1 + c2 * k2)))
            (Tplus (Tmult l1 (Tint k1)) (Tmult l2 (Tint k2)))
      | false => t
      end
  | _ => t
  end.

Theorem T_OMEGA10_stable : term_stable T_OMEGA10.

prove_stable T_OMEGA10 OMEGA10.
Qed.

Definition T_OMEGA11 (t : term) :=
  match t with
  | Tplus (Tmult (Tplus (Tmult v1 (Tint c1)) l1) (Tint k1)) l2 =>
      Tplus (Tmult v1 (Tint (c1 * k1))) (Tplus (Tmult l1 (Tint k1)) l2)
  | _ => t
  end.

Theorem T_OMEGA11_stable : term_stable T_OMEGA11.

prove_stable T_OMEGA11 OMEGA11.
Qed.

Definition T_OMEGA12 (t : term) :=
  match t with
  | Tplus l1 (Tmult (Tplus (Tmult v2 (Tint c2)) l2) (Tint k2)) =>
      Tplus (Tmult v2 (Tint (c2 * k2))) (Tplus l1 (Tmult l2 (Tint k2)))
  | _ => t
  end.

Theorem T_OMEGA12_stable : term_stable T_OMEGA12.

prove_stable T_OMEGA12 OMEGA12.
Qed. 

Definition T_OMEGA13 (t : term) :=
  match t with
  | Tplus (Tplus (Tmult v (Tint (Zpos x))) l1) (Tplus (Tmult v' (Tint (Zneg
    x'))) l2) =>
      match eq_term v v' with
      | true => match eq_pos x x' with
                | true => Tplus l1 l2
                | false => t
                end
      | false => t
      end
  | Tplus (Tplus (Tmult v (Tint (Zneg x))) l1) (Tplus (Tmult v' (Tint (Zpos
    x'))) l2) =>
      match eq_term v v' with
      | true => match eq_pos x x' with
                | true => Tplus l1 l2
                | false => t
                end
      | false => t
      end
  | _ => t
  end.

Theorem T_OMEGA13_stable : term_stable T_OMEGA13.

unfold term_stable, T_OMEGA13 in |- *; intros; Simplify; simpl in |- *;
 [ apply OMEGA13 | apply OMEGA14 ].
Qed.

Definition T_OMEGA15 (t : term) :=
  match t with
  | Tplus (Tplus (Tmult v (Tint c1)) l1) (Tmult (Tplus (Tmult v' (Tint c2))
    l2) (Tint k2)) =>
      match eq_term v v' with
      | true =>
          Tplus (Tmult v (Tint (c1 + c2 * k2)))
            (Tplus l1 (Tmult l2 (Tint k2)))
      | false => t
      end
  | _ => t
  end.

Theorem T_OMEGA15_stable : term_stable T_OMEGA15.

prove_stable T_OMEGA15 OMEGA15.
Qed.

Definition T_OMEGA16 (t : term) :=
  match t with
  | Tmult (Tplus (Tmult v (Tint c)) l) (Tint k) =>
      Tplus (Tmult v (Tint (c * k))) (Tmult l (Tint k))
  | _ => t
  end.


Theorem T_OMEGA16_stable : term_stable T_OMEGA16.

prove_stable T_OMEGA16 OMEGA16.
Qed.

Definition Tred_factor5 (t : term) :=
  match t with
  | Tplus (Tmult x (Tint Z0)) y => y
  | _ => t
  end.

Theorem Tred_factor5_stable : term_stable Tred_factor5.


prove_stable Tred_factor5 Zred_factor5.
Qed.

Definition Topp_plus (t : term) :=
  match t with
  | Topp (Tplus x y) => Tplus (Topp x) (Topp y)
  | _ => t
  end.

Theorem Topp_plus_stable : term_stable Topp_plus.

prove_stable Topp_plus Zopp_plus_distr.
Qed.


Definition Topp_opp (t : term) :=
  match t with
  | Topp (Topp x) => x
  | _ => t
  end.

Theorem Topp_opp_stable : term_stable Topp_opp.

prove_stable Topp_opp Zopp_involutive.
Qed.

Definition Topp_mult_r (t : term) :=
  match t with
  | Topp (Tmult x (Tint k)) => Tmult x (Tint (- k))
  | _ => t
  end.

Theorem Topp_mult_r_stable : term_stable Topp_mult_r.

prove_stable Topp_mult_r Zopp_mult_distr_r.
Qed.

Definition Topp_one (t : term) :=
  match t with
  | Topp x => Tmult x (Tint (-1))
  | _ => t
  end.

Theorem Topp_one_stable : term_stable Topp_one.

prove_stable Topp_one Zopp_eq_mult_neg_1.
Qed.

Definition Tmult_plus_distr (t : term) :=
  match t with
  | Tmult (Tplus n m) p => Tplus (Tmult n p) (Tmult m p)
  | _ => t
  end.

Theorem Tmult_plus_distr_stable : term_stable Tmult_plus_distr.

prove_stable Tmult_plus_distr Zmult_plus_distr_l.
Qed.

Definition Tmult_opp_left (t : term) :=
  match t with
  | Tmult (Topp x) (Tint y) => Tmult x (Tint (- y))
  | _ => t
  end.

Theorem Tmult_opp_left_stable : term_stable Tmult_opp_left.

prove_stable Tmult_opp_left Zmult_opp_comm.
Qed.

Definition Tmult_assoc_reduced (t : term) :=
  match t with
  | Tmult (Tmult n (Tint m)) (Tint p) => Tmult n (Tint (m * p))
  | _ => t
  end.

Theorem Tmult_assoc_reduced_stable : term_stable Tmult_assoc_reduced.

prove_stable Tmult_assoc_reduced Zmult_assoc_reverse.
Qed.

Definition Tred_factor0 (t : term) := Tmult t (Tint 1).

Theorem Tred_factor0_stable : term_stable Tred_factor0.

prove_stable Tred_factor0 Zred_factor0.
Qed.

Definition Tred_factor1 (t : term) :=
  match t with
  | Tplus x y =>
      match eq_term x y with
      | true => Tmult x (Tint 2)
      | false => t
      end
  | _ => t
  end.

Theorem Tred_factor1_stable : term_stable Tred_factor1.

prove_stable Tred_factor1 Zred_factor1.
Qed.

Definition Tred_factor2 (t : term) :=
  match t with
  | Tplus x (Tmult y (Tint k)) =>
      match eq_term x y with
      | true => Tmult x (Tint (1 + k))
      | false => t
      end
  | _ => t
  end.

(* Attention : il faut rendre opaque [Zplus] pour éviter que la tactique
   de simplification n'aille trop loin et défasse [Zplus 1 k] *)

Opaque Zplus.

Theorem Tred_factor2_stable : term_stable Tred_factor2.
prove_stable Tred_factor2 Zred_factor2.
Qed.

Definition Tred_factor3 (t : term) :=
  match t with
  | Tplus (Tmult x (Tint k)) y =>
      match eq_term x y with
      | true => Tmult x (Tint (1 + k))
      | false => t
      end
  | _ => t
  end.

Theorem Tred_factor3_stable : term_stable Tred_factor3.

prove_stable Tred_factor3 Zred_factor3.
Qed.


Definition Tred_factor4 (t : term) :=
  match t with
  | Tplus (Tmult x (Tint k1)) (Tmult y (Tint k2)) =>
      match eq_term x y with
      | true => Tmult x (Tint (k1 + k2))
      | false => t
      end
  | _ => t
  end.

Theorem Tred_factor4_stable : term_stable Tred_factor4.

prove_stable Tred_factor4 Zred_factor4.
Qed.

Definition Tred_factor6 (t : term) := Tplus t (Tint 0).

Theorem Tred_factor6_stable : term_stable Tred_factor6.

prove_stable Tred_factor6 Zred_factor6.
Qed.

Transparent Zplus.

Definition Tminus_def (t : term) :=
  match t with
  | Tminus x y => Tplus x (Topp y)
  | _ => t
  end.

Theorem Tminus_def_stable : term_stable Tminus_def.

(* Le théorème ne sert à rien. Le but est prouvé avant. *)
prove_stable Tminus_def False.
Qed.

(* \subsection{Fonctions de réécriture complexes} *)

(* \subsubsection{Fonction de réduction} *)
(* Cette fonction réduit un terme dont la forme normale est un entier. Il
   suffit pour cela d'échanger le constructeur [Tint] avec les opérateurs
   réifiés. La réduction est ``gratuite''.  *)

Fixpoint reduce (t : term) : term :=
  match t with
  | Tplus x y =>
      match reduce x with
      | Tint x' =>
          match reduce y with
          | Tint y' => Tint (x' + y')
          | y' => Tplus (Tint x') y'
          end
      | x' => Tplus x' (reduce y)
      end
  | Tmult x y =>
      match reduce x with
      | Tint x' =>
          match reduce y with
          | Tint y' => Tint (x' * y')
          | y' => Tmult (Tint x') y'
          end
      | x' => Tmult x' (reduce y)
      end
  | Tminus x y =>
      match reduce x with
      | Tint x' =>
          match reduce y with
          | Tint y' => Tint (x' - y')
          | y' => Tminus (Tint x') y'
          end
      | x' => Tminus x' (reduce y)
      end
  | Topp x =>
      match reduce x with
      | Tint x' => Tint (- x')
      | x' => Topp x'
      end
  | _ => t
  end.

Theorem reduce_stable : term_stable reduce.

unfold term_stable in |- *; intros e t; elim t; auto;
 try
  (intros t0 H0 t1 H1; simpl in |- *; rewrite H0; rewrite H1;
    (case (reduce t0);
      [ intro z0; case (reduce t1); intros; auto
      | intros; auto
      | intros; auto
      | intros; auto
      | intros; auto
      | intros; auto ])); intros t0 H0; simpl in |- *; 
 rewrite H0; case (reduce t0); intros; auto.
Qed.

(* \subsubsection{Fusions}
    \paragraph{Fusion de deux équations} *)
(* On donne une somme de deux équations qui sont supposées normalisées. 
   Cette fonction prend une trace de fusion en argument et transforme
   le terme en une équation normalisée. C'est une version très simplifiée
   du moteur de réécriture [rewrite]. *)

Fixpoint fusion (trace : list t_fusion) (t : term) {struct trace} : term :=
  match trace with
  | nil => reduce t
  | step :: trace' =>
      match step with
      | F_equal => apply_right (fusion trace') (T_OMEGA10 t)
      | F_cancel => fusion trace' (Tred_factor5 (T_OMEGA10 t))
      | F_left => apply_right (fusion trace') (T_OMEGA11 t)
      | F_right => apply_right (fusion trace') (T_OMEGA12 t)
      end
  end.
    
Theorem fusion_stable : forall t : list t_fusion, term_stable (fusion t).

simple induction t; simpl in |- *;
 [ exact reduce_stable
 | intros stp l H; case stp;
    [ apply compose_term_stable;
       [ apply apply_right_stable; assumption | exact T_OMEGA10_stable ]
    | unfold term_stable in |- *; intros e t1; rewrite T_OMEGA10_stable;
       rewrite Tred_factor5_stable; apply H
    | apply compose_term_stable;
       [ apply apply_right_stable; assumption | exact T_OMEGA11_stable ]
    | apply compose_term_stable;
       [ apply apply_right_stable; assumption | exact T_OMEGA12_stable ] ] ].

Qed.

(* \paragraph{Fusion de deux équations dont une sans coefficient} *)

Definition fusion_right (trace : list t_fusion) (t : term) : term :=
  match trace with
  | nil => reduce t (* Il faut mettre un compute *)
  | step :: trace' =>
      match step with
      | F_equal => apply_right (fusion trace') (T_OMEGA15 t)
      | F_cancel => fusion trace' (Tred_factor5 (T_OMEGA15 t))
      | F_left => apply_right (fusion trace') (Tplus_assoc_r t)
      | F_right => apply_right (fusion trace') (T_OMEGA12 t)
      end
  end.

(* \paragraph{Fusion avec anihilation} *)
(* Normalement le résultat est une constante *)

Fixpoint fusion_cancel (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => fusion_cancel trace' (T_OMEGA13 t)
  end.

Theorem fusion_cancel_stable : forall t : nat, term_stable (fusion_cancel t).

unfold term_stable, fusion_cancel in |- *; intros trace e; elim trace;
 [ exact (reduce_stable e)
 | intros n H t; elim H; exact (T_OMEGA13_stable e t) ].
Qed. 

(* \subsubsection{Opérations afines sur une équation} *)
(* \paragraph{Multiplication scalaire et somme d'une constante} *)

Fixpoint scalar_norm_add (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => apply_right (scalar_norm_add trace') (T_OMEGA11 t)
  end.

Theorem scalar_norm_add_stable :
 forall t : nat, term_stable (scalar_norm_add t).

unfold term_stable, scalar_norm_add in |- *; intros trace; elim trace;
 [ exact reduce_stable
 | intros n H e t; elim apply_right_stable;
    [ exact (T_OMEGA11_stable e t) | exact H ] ].
Qed.
   
(* \paragraph{Multiplication scalaire} *)
Fixpoint scalar_norm (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => apply_right (scalar_norm trace') (T_OMEGA16 t)
  end.

Theorem scalar_norm_stable : forall t : nat, term_stable (scalar_norm t).

unfold term_stable, scalar_norm in |- *; intros trace; elim trace;
 [ exact reduce_stable
 | intros n H e t; elim apply_right_stable;
    [ exact (T_OMEGA16_stable e t) | exact H ] ].
Qed.

(* \paragraph{Somme d'une constante} *)
Fixpoint add_norm (trace : nat) (t : term) {struct trace} : term :=
  match trace with
  | O => reduce t
  | S trace' => apply_right (add_norm trace') (Tplus_assoc_r t)
  end.

Theorem add_norm_stable : forall t : nat, term_stable (add_norm t).

unfold term_stable, add_norm in |- *; intros trace; elim trace;
 [ exact reduce_stable
 | intros n H e t; elim apply_right_stable;
    [ exact (Tplus_assoc_r_stable e t) | exact H ] ].
Qed.

(* \subsection{La fonction de normalisation des termes (moteur de réécriture)} *)


Fixpoint rewrite (s : step) : term -> term :=
  match s with
  | C_DO_BOTH s1 s2 => apply_both (rewrite s1) (rewrite s2)
  | C_LEFT s => apply_left (rewrite s)
  | C_RIGHT s => apply_right (rewrite s)
  | C_SEQ s1 s2 => fun t : term => rewrite s2 (rewrite s1 t)
  | C_NOP => fun t : term => t
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

Theorem rewrite_stable : forall s : step, term_stable (rewrite s).

simple induction s; simpl in |- *;
 [ intros; apply apply_both_stable; auto
 | intros; apply apply_left_stable; auto
 | intros; apply apply_right_stable; auto
 | unfold term_stable in |- *; intros; elim H0; apply H
 | unfold term_stable in |- *; auto
 | exact Topp_plus_stable
 | exact Topp_opp_stable
 | exact Topp_mult_r_stable
 | exact Topp_one_stable
 | exact reduce_stable
 | exact Tmult_plus_distr_stable
 | exact Tmult_opp_left_stable
 | exact Tmult_assoc_r_stable
 | exact Tplus_assoc_r_stable
 | exact Tplus_assoc_l_stable
 | exact Tplus_permute_stable
 | exact Tplus_sym_stable
 | exact Tred_factor0_stable
 | exact Tred_factor1_stable
 | exact Tred_factor2_stable
 | exact Tred_factor3_stable
 | exact Tred_factor4_stable
 | exact Tred_factor5_stable
 | exact Tred_factor6_stable
 | exact Tmult_assoc_reduced_stable
 | exact Tminus_def_stable
 | exact Tmult_sym_stable ].
Qed.

(* \subsection{tactiques de résolution d'un but omega normalisé} 
   Trace de la procédure 
\subsubsection{Tactiques générant une contradiction}
\paragraph{[O_CONSTANT_NOT_NUL]} *)

Definition constant_not_nul (i : nat) (h : list proposition) :=
  match nth_hyps i h with
  | EqTerm (Tint Z0) (Tint n) =>
      match eq_Z n 0 with
      | true => h
      | false => absurd
      end
  | _ => h
  end.

Theorem constant_not_nul_valid :
 forall i : nat, valid_hyps (constant_not_nul i).

unfold valid_hyps, constant_not_nul in |- *; intros;
 generalize (nth_valid ep e i lp); Simplify; simpl in |- *;
 elim_eq_Z ipattern:z0 0%Z; auto; simpl in |- *; intros H1 H2; 
 elim H1; symmetry  in |- *; auto.
Qed.   

(* \paragraph{[O_CONSTANT_NEG]} *)

Definition constant_neg (i : nat) (h : list proposition) :=
  match nth_hyps i h with
  | LeqTerm (Tint Z0) (Tint (Zneg n)) => absurd
  | _ => h
  end.

Theorem constant_neg_valid : forall i : nat, valid_hyps (constant_neg i).

unfold valid_hyps, constant_neg in |- *; intros;
 generalize (nth_valid ep e i lp); Simplify; simpl in |- *;
 unfold Zle in |- *; simpl in |- *; intros H1; elim H1;
 [ assumption | trivial ].
Qed.   

(* \paragraph{[NOT_EXACT_DIVIDE]} *)
Definition not_exact_divide (k1 k2 : Z) (body : term) 
  (t i : nat) (l : list proposition) :=
  match nth_hyps i l with
  | EqTerm (Tint Z0) b =>
      match
        eq_term (scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2)))
          b
      with
      | true =>
          match (k2 ?= 0)%Z with
          | Datatypes.Gt =>
              match (k1 ?= k2)%Z with
              | Datatypes.Gt => absurd
              | _ => l
              end
          | _ => l
          end
      | false => l
      end
  | _ => l
  end.

Theorem not_exact_divide_valid :
 forall (k1 k2 : Z) (body : term) (t i : nat),
 valid_hyps (not_exact_divide k1 k2 body t i).

unfold valid_hyps, not_exact_divide in |- *; intros;
 generalize (nth_valid ep e i lp); Simplify;
 elim_eq_term (scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2))) t1;
 auto; Simplify; intro H2; elim H2; simpl in |- *;
 elim (scalar_norm_add_stable t e); simpl in |- *; 
 intro H4; absurd ((interp_term e body * k1 + k2)%Z = 0%Z);
 [ apply OMEGA4; assumption | symmetry  in |- *; auto ].

Qed.

(* \paragraph{[O_CONTRADICTION]} *)

Definition contradiction (t i j : nat) (l : list proposition) :=
  match nth_hyps i l with
  | LeqTerm (Tint Z0) b1 =>
      match nth_hyps j l with
      | LeqTerm (Tint Z0) b2 =>
          match fusion_cancel t (Tplus b1 b2) with
          | Tint k =>
              match (0 ?= k)%Z with
              | Datatypes.Gt => absurd
              | _ => l
              end
          | _ => l
          end
      | _ => l
      end
  | _ => l
  end.

Theorem contradiction_valid :
 forall t i j : nat, valid_hyps (contradiction t i j).

unfold valid_hyps, contradiction in |- *; intros t i j ep e l H;
 generalize (nth_valid _ _ i _ H); generalize (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1; 
 auto; intros z; case z; auto; case (nth_hyps j l); 
 auto; intros t3 t4; case t3; auto; intros z'; case z'; 
 auto; simpl in |- *; intros H1 H2;
 generalize (refl_equal (interp_term e (fusion_cancel t (Tplus t2 t4))));
 pattern (fusion_cancel t (Tplus t2 t4)) at 2 3 in |- *;
 case (fusion_cancel t (Tplus t2 t4)); simpl in |- *; 
 auto; intro k; elim (fusion_cancel_stable t); simpl in |- *; 
 intro E; generalize (OMEGA2 _ _ H2 H1); rewrite E; 
 case k; auto; unfold Zle in |- *; simpl in |- *; intros p H3; 
 elim H3; auto.

Qed.

(* \paragraph{[O_NEGATE_CONTRADICT]} *)

Definition negate_contradict (i1 i2 : nat) (h : list proposition) :=
  match nth_hyps i1 h with
  | EqTerm (Tint Z0) b1 =>
      match nth_hyps i2 h with
      | NeqTerm (Tint Z0) b2 =>
          match eq_term b1 b2 with
          | true => absurd
          | false => h
          end
      | _ => h
      end
  | NeqTerm (Tint Z0) b1 =>
      match nth_hyps i2 h with
      | EqTerm (Tint Z0) b2 =>
          match eq_term b1 b2 with
          | true => absurd
          | false => h
          end
      | _ => h
      end
  | _ => h
  end.

Definition negate_contradict_inv (t i1 i2 : nat) (h : list proposition) :=
  match nth_hyps i1 h with
  | EqTerm (Tint Z0) b1 =>
      match nth_hyps i2 h with
      | NeqTerm (Tint Z0) b2 =>
          match eq_term b1 (scalar_norm t (Tmult b2 (Tint (-1)))) with
          | true => absurd
          | false => h
          end
      | _ => h
      end
  | NeqTerm (Tint Z0) b1 =>
      match nth_hyps i2 h with
      | EqTerm (Tint Z0) b2 =>
          match eq_term b1 (scalar_norm t (Tmult b2 (Tint (-1)))) with
          | true => absurd
          | false => h
          end
      | _ => h
      end
  | _ => h
  end.

Theorem negate_contradict_valid :
 forall i j : nat, valid_hyps (negate_contradict i j).

unfold valid_hyps, negate_contradict in |- *; intros i j ep e l H;
 generalize (nth_valid _ _ i _ H); generalize (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1; 
 auto; intros z; case z; auto; case (nth_hyps j l); 
 auto; intros t3 t4; case t3; auto; intros z'; case z'; 
 auto; simpl in |- *; intros H1 H2;
 [ elim_eq_term t2 t4; intro H3;
    [ elim H1; elim H3; assumption | assumption ]
 | elim_eq_term t2 t4; intro H3;
    [ elim H2; rewrite H3; assumption | assumption ] ].

Qed.

Theorem negate_contradict_inv_valid :
 forall t i j : nat, valid_hyps (negate_contradict_inv t i j).


unfold valid_hyps, negate_contradict_inv in |- *; intros t i j ep e l H;
 generalize (nth_valid _ _ i _ H); generalize (nth_valid _ _ j _ H);
 case (nth_hyps i l); auto; intros t1 t2; case t1; 
 auto; intros z; case z; auto; case (nth_hyps j l); 
 auto; intros t3 t4; case t3; auto; intros z'; case z'; 
 auto; simpl in |- *; intros H1 H2;
 (pattern (eq_term t2 (scalar_norm t (Tmult t4 (Tint (-1))))) in |- *;
   apply bool_ind2; intro Aux;
   [ generalize (eq_term_true t2 (scalar_norm t (Tmult t4 (Tint (-1)))) Aux);
      clear Aux
   | generalize (eq_term_false t2 (scalar_norm t (Tmult t4 (Tint (-1)))) Aux);
      clear Aux ]);
 [ intro H3; elim H1; generalize H2; rewrite H3;
    rewrite <- (scalar_norm_stable t e); simpl in |- *;
    elim (interp_term e t4); simpl in |- *; auto; intros p H4;
    discriminate H4
 | auto
 | intro H3; elim H2; rewrite H3; elim (scalar_norm_stable t e);
    simpl in |- *; elim H1; simpl in |- *; trivial
 | auto ].

Qed.

(* \subsubsection{Tactiques générant une nouvelle équation} *)
(* \paragraph{[O_SUM]}
 C'est une oper2 valide mais elle traite plusieurs cas à la fois (suivant
 les opérateurs de comparaison des deux arguments) d'où une
 preuve un peu compliquée. On utilise quelques lemmes qui sont des 
 généralisations des théorèmes utilisés par OMEGA. *)

Definition sum (k1 k2 : Z) (trace : list t_fusion)
  (prop1 prop2 : proposition) :=
  match prop1 with
  | EqTerm (Tint Z0) b1 =>
      match prop2 with
      | EqTerm (Tint Z0) b2 =>
          EqTerm (Tint 0)
            (fusion trace (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2))))
      | LeqTerm (Tint Z0) b2 =>
          match (k2 ?= 0)%Z with
          | Datatypes.Gt =>
              LeqTerm (Tint 0)
                (fusion trace
                   (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2))))
          | _ => TrueTerm
          end
      | _ => TrueTerm
      end
  | LeqTerm (Tint Z0) b1 =>
      match (k1 ?= 0)%Z with
      | Datatypes.Gt =>
          match prop2 with
          | EqTerm (Tint Z0) b2 =>
              LeqTerm (Tint 0)
                (fusion trace
                   (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2))))
          | LeqTerm (Tint Z0) b2 =>
              match (k2 ?= 0)%Z with
              | Datatypes.Gt =>
                  LeqTerm (Tint 0)
                    (fusion trace
                       (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2))))
              | _ => TrueTerm
              end
          | _ => TrueTerm
          end
      | _ => TrueTerm
      end
  | NeqTerm (Tint Z0) b1 =>
      match prop2 with
      | EqTerm (Tint Z0) b2 =>
          match eq_Z k1 0 with
          | true => TrueTerm
          | false =>
              NeqTerm (Tint 0)
                (fusion trace
                   (Tplus (Tmult b1 (Tint k1)) (Tmult b2 (Tint k2))))
          end
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem sum1 :
 forall a b c d : Z, 0%Z = a -> 0%Z = b -> 0%Z = (a * c + b * d)%Z.

intros; elim H; elim H0; simpl in |- *; auto.
Qed.
  
Theorem sum2 :
 forall a b c d : Z,
 (0 <= d)%Z -> 0%Z = a -> (0 <= b)%Z -> (0 <= a * c + b * d)%Z.

intros; elim H0; simpl in |- *; generalize H H1; case b; case d;
 unfold Zle in |- *; simpl in |- *; auto.  
Qed.

Theorem sum3 :
 forall a b c d : Z,
 (0 <= c)%Z ->
 (0 <= d)%Z -> (0 <= a)%Z -> (0 <= b)%Z -> (0 <= a * c + b * d)%Z.

intros a b c d; case a; case b; case c; case d; unfold Zle in |- *;
 simpl in |- *; auto. 
Qed.

Theorem sum4 : forall k : Z, (k ?= 0)%Z = Datatypes.Gt -> (0 <= k)%Z.

intro; case k; unfold Zle in |- *; simpl in |- *; auto; intros; discriminate.  
Qed.

Theorem sum5 :
 forall a b c d : Z,
 c <> 0%Z -> 0%Z <> a -> 0%Z = b -> 0%Z <> (a * c + b * d)%Z.

intros a b c d H1 H2 H3; elim H3; simpl in |- *; rewrite Zplus_comm;
 simpl in |- *; generalize H1 H2; case a; case c; simpl in |- *; 
 intros; try discriminate; assumption.
Qed.


Theorem sum_valid :
 forall (k1 k2 : Z) (t : list t_fusion), valid2 (sum k1 k2 t).

unfold valid2 in |- *; intros k1 k2 t ep e p1 p2; unfold sum in |- *;
 Simplify; simpl in |- *; auto; try elim (fusion_stable t); 
 simpl in |- *; intros;
 [ apply sum1; assumption
 | apply sum2; try assumption; apply sum4; assumption
 | rewrite Zplus_comm; apply sum2; try assumption; apply sum4; assumption
 | apply sum3; try assumption; apply sum4; assumption
 | elim_eq_Z k1 0%Z; simpl in |- *; auto; elim (fusion_stable t);
    simpl in |- *; intros; unfold Zne in |- *; apply sum5; 
    assumption ].
Qed.

(* \paragraph{[O_EXACT_DIVIDE]}
   c'est une oper1 valide mais on préfère une substitution a ce point la *)

Definition exact_divide (k : Z) (body : term) (t : nat)
  (prop : proposition) :=
  match prop with
  | EqTerm (Tint Z0) b =>
      match eq_term (scalar_norm t (Tmult body (Tint k))) b with
      | true =>
          match eq_Z k 0 with
          | true => TrueTerm
          | false => EqTerm (Tint 0) body
          end
      | false => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem exact_divide_valid :
 forall (k : Z) (t : term) (n : nat), valid1 (exact_divide k t n).


unfold valid1, exact_divide in |- *; intros k1 k2 t ep e p1; Simplify;
 simpl in |- *; auto; elim_eq_term (scalar_norm t (Tmult k2 (Tint k1))) t1;
 simpl in |- *; auto; elim_eq_Z k1 0%Z; simpl in |- *; 
 auto; intros H1 H2; elim H2; elim scalar_norm_stable; 
 simpl in |- *; generalize H1; case (interp_term e k2); 
 try trivial;
 (case k1; simpl in |- *;
   [ intros; absurd (0%Z = 0%Z); assumption
   | intros p2 p3 H3 H4; discriminate H4
   | intros p2 p3 H3 H4; discriminate H4 ]).

Qed.



(* \paragraph{[O_DIV_APPROX]}
  La preuve reprend le schéma de la précédente mais on
  est sur une opération de type valid1 et non sur une opération terminale. *)

Definition divide_and_approx (k1 k2 : Z) (body : term) 
  (t : nat) (prop : proposition) :=
  match prop with
  | LeqTerm (Tint Z0) b =>
      match
        eq_term (scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2)))
          b
      with
      | true =>
          match (k1 ?= 0)%Z with
          | Datatypes.Gt =>
              match (k1 ?= k2)%Z with
              | Datatypes.Gt => LeqTerm (Tint 0) body
              | _ => prop
              end
          | _ => prop
          end
      | false => prop
      end
  | _ => prop
  end.

Theorem divide_and_approx_valid :
 forall (k1 k2 : Z) (body : term) (t : nat),
 valid1 (divide_and_approx k1 k2 body t).

unfold valid1, divide_and_approx in |- *; intros k1 k2 body t ep e p1;
 Simplify;
 elim_eq_term (scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2))) t1;
 Simplify; auto; intro E; elim E; simpl in |- *;
 elim (scalar_norm_add_stable t e); simpl in |- *; 
 intro H1; apply Zmult_le_approx with (3 := H1); assumption.
Qed.

(* \paragraph{[MERGE_EQ]} *)

Definition merge_eq (t : nat) (prop1 prop2 : proposition) :=
  match prop1 with
  | LeqTerm (Tint Z0) b1 =>
      match prop2 with
      | LeqTerm (Tint Z0) b2 =>
          match eq_term b1 (scalar_norm t (Tmult b2 (Tint (-1)))) with
          | true => EqTerm (Tint 0) b1
          | false => TrueTerm
          end
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem merge_eq_valid : forall n : nat, valid2 (merge_eq n).

unfold valid2, merge_eq in |- *; intros n ep e p1 p2; Simplify; simpl in |- *;
 auto; elim (scalar_norm_stable n e); simpl in |- *; 
 intros; symmetry  in |- *; apply OMEGA8 with (2 := H0);
 [ assumption | elim Zopp_eq_mult_neg_1; trivial ].
Qed.



(* \paragraph{[O_CONSTANT_NUL]} *)

Definition constant_nul (i : nat) (h : list proposition) :=
  match nth_hyps i h with
  | NeqTerm (Tint Z0) (Tint Z0) => absurd
  | _ => h
  end.

Theorem constant_nul_valid : forall i : nat, valid_hyps (constant_nul i).

unfold valid_hyps, constant_nul in |- *; intros;
 generalize (nth_valid ep e i lp); Simplify; simpl in |- *;
 unfold Zne in |- *; intro H1; absurd (0%Z = 0%Z); 
 auto.
Qed.

(* \paragraph{[O_STATE]} *)

Definition state (m : Z) (s : step) (prop1 prop2 : proposition) :=
  match prop1 with
  | EqTerm (Tint Z0) b1 =>
      match prop2 with
      | EqTerm (Tint Z0) (Tplus b2 (Topp b3)) =>
          EqTerm (Tint 0)
            (rewrite s (Tplus b1 (Tmult (Tplus (Topp b3) b2) (Tint m))))
      | _ => TrueTerm
      end
  | _ => TrueTerm
  end.

Theorem state_valid : forall (m : Z) (s : step), valid2 (state m s).

unfold valid2 in |- *; intros m s ep e p1 p2; unfold state in |- *; Simplify;
 simpl in |- *; auto; elim (rewrite_stable s e); simpl in |- *; 
 intros H1 H2; elim H1;
 rewrite (Zplus_comm (- interp_term e t5) (interp_term e t3)); 
 elim H2; simpl in |- *; reflexivity.

Qed.

(* \subsubsection{Tactiques générant plusieurs but}
   \paragraph{[O_SPLIT_INEQ]} 
   La seule pour le moment (tant que la normalisation n'est pas réfléchie). *)

Definition split_ineq (i t : nat)
  (f1 f2 : list proposition -> list (list proposition))
  (l : list proposition) :=
  match nth_hyps i l with
  | NeqTerm (Tint Z0) b1 =>
      f1 (LeqTerm (Tint 0) (add_norm t (Tplus b1 (Tint (-1)))) :: l) ++
      f2
        (LeqTerm (Tint 0)
           (scalar_norm_add t (Tplus (Tmult b1 (Tint (-1))) (Tint (-1))))
         :: l)
  | _ => l :: nil
  end.

Theorem split_ineq_valid :
 forall (i t : nat) (f1 f2 : list proposition -> list (list proposition)),
 valid_list_hyps f1 ->
 valid_list_hyps f2 -> valid_list_hyps (split_ineq i t f1 f2).

unfold valid_list_hyps, split_ineq in |- *; intros i t f1 f2 H1 H2 ep e lp H;
 generalize (nth_valid _ _ i _ H); case (nth_hyps i lp); 
 simpl in |- *; auto; intros t1 t2; case t1; simpl in |- *; 
 auto; intros z; case z; simpl in |- *; auto; intro H3; 
 apply append_valid; elim (OMEGA19 (interp_term e t2));
 [ intro H4; left; apply H1; simpl in |- *; elim (add_norm_stable t);
    simpl in |- *; auto
 | intro H4; right; apply H2; simpl in |- *; elim (scalar_norm_add_stable t);
    simpl in |- *; auto
 | generalize H3; unfold Zne, not in |- *; intros E1 E2; apply E1;
    symmetry  in |- *; trivial ].
Qed.


(* \subsection{La fonction de rejeu de la trace} *)

Fixpoint execute_omega (t : t_omega) (l : list proposition) {struct t} :
 list (list proposition) :=
  match t with
  | O_CONSTANT_NOT_NUL n =>
      (fun a : list proposition => a :: nil) (constant_not_nul n l)
  | O_CONSTANT_NEG n =>
      (fun a : list proposition => a :: nil) (constant_neg n l)
  | O_DIV_APPROX k1 k2 body t cont n =>
      execute_omega cont (apply_oper_1 n (divide_and_approx k1 k2 body t) l)
  | O_NOT_EXACT_DIVIDE k1 k2 body t i =>
      (fun a : list proposition => a :: nil)
        (not_exact_divide k1 k2 body t i l)
  | O_EXACT_DIVIDE k body t cont n =>
      execute_omega cont (apply_oper_1 n (exact_divide k body t) l)
  | O_SUM k1 i1 k2 i2 t cont =>
      execute_omega cont (apply_oper_2 i1 i2 (sum k1 k2 t) l)
  | O_CONTRADICTION t i j =>
      (fun a : list proposition => a :: nil) (contradiction t i j l)
  | O_MERGE_EQ t i1 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 (merge_eq t) l)
  | O_SPLIT_INEQ t i cont1 cont2 =>
      split_ineq i t (execute_omega cont1) (execute_omega cont2) l
  | O_CONSTANT_NUL i =>
      (fun a : list proposition => a :: nil) (constant_nul i l)
  | O_NEGATE_CONTRADICT i j =>
      (fun a : list proposition => a :: nil) (negate_contradict i j l)
  | O_NEGATE_CONTRADICT_INV t i j =>
      (fun a : list proposition => a :: nil) (negate_contradict_inv t i j l)
  | O_STATE m s i1 i2 cont =>
      execute_omega cont (apply_oper_2 i1 i2 (state m s) l)
  end.

Theorem omega_valid : forall t : t_omega, valid_list_hyps (execute_omega t).

simple induction t; simpl in |- *;
 [ unfold valid_list_hyps in |- *; simpl in |- *; intros; left;
    apply (constant_not_nul_valid n ep e lp H)
 | unfold valid_list_hyps in |- *; simpl in |- *; intros; left;
    apply (constant_neg_valid n ep e lp H)
 | unfold valid_list_hyps, valid_hyps in |- *;
    intros k1 k2 body n t' Ht' m ep e lp H; apply Ht';
    apply
     (apply_oper_1_valid m (divide_and_approx k1 k2 body n)
        (divide_and_approx_valid k1 k2 body n) ep e lp H)
 | unfold valid_list_hyps in |- *; simpl in |- *; intros; left;
    apply (not_exact_divide_valid z z0 t0 n n0 ep e lp H)
 | unfold valid_list_hyps, valid_hyps in |- *;
    intros k body n t' Ht' m ep e lp H; apply Ht';
    apply
     (apply_oper_1_valid m (exact_divide k body n)
        (exact_divide_valid k body n) ep e lp H)
 | unfold valid_list_hyps, valid_hyps in |- *;
    intros k1 i1 k2 i2 trace t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_2_valid i1 i2 (sum k1 k2 trace) (sum_valid k1 k2 trace) ep e
        lp H)
 | unfold valid_list_hyps in |- *; simpl in |- *; intros; left;
    apply (contradiction_valid n n0 n1 ep e lp H)
 | unfold valid_list_hyps, valid_hyps in |- *;
    intros trace i1 i2 t' Ht' ep e lp H; apply Ht';
    apply
     (apply_oper_2_valid i1 i2 (merge_eq trace) (merge_eq_valid trace) ep e
        lp H)
 | intros t' i k1 H1 k2 H2; unfold valid_list_hyps in |- *; simpl in |- *;
    intros ep e lp H;
    apply
     (split_ineq_valid i t' (execute_omega k1) (execute_omega k2) H1 H2 ep e
        lp H)
 | unfold valid_list_hyps in |- *; simpl in |- *; intros i ep e lp H; left;
    apply (constant_nul_valid i ep e lp H)
 | unfold valid_list_hyps in |- *; simpl in |- *; intros i j ep e lp H; left;
    apply (negate_contradict_valid i j ep e lp H)
 | unfold valid_list_hyps in |- *; simpl in |- *; intros n i j ep e lp H;
    left; apply (negate_contradict_inv_valid n i j ep e lp H)
 | unfold valid_list_hyps, valid_hyps in |- *;
    intros m s i1 i2 t' Ht' ep e lp H; apply Ht';
    apply (apply_oper_2_valid i1 i2 (state m s) (state_valid m s) ep e lp H) ].
Qed.


(* \subsection{Les opérations globales sur le but} 
   \subsubsection{Normalisation} *)

Definition move_right (s : step) (p : proposition) :=
  match p with
  | EqTerm t1 t2 => EqTerm (Tint 0) (rewrite s (Tplus t1 (Topp t2)))
  | LeqTerm t1 t2 => LeqTerm (Tint 0) (rewrite s (Tplus t2 (Topp t1)))
  | GeqTerm t1 t2 => LeqTerm (Tint 0) (rewrite s (Tplus t1 (Topp t2)))
  | LtTerm t1 t2 =>
      LeqTerm (Tint 0) (rewrite s (Tplus (Tplus t2 (Tint (-1))) (Topp t1)))
  | GtTerm t1 t2 =>
      LeqTerm (Tint 0) (rewrite s (Tplus (Tplus t1 (Tint (-1))) (Topp t2)))
  | NeqTerm t1 t2 => NeqTerm (Tint 0) (rewrite s (Tplus t1 (Topp t2)))
  | p => p
  end.

Theorem Zne_left_2 : forall x y : Z, Zne x y -> Zne 0 (x + - y).
unfold Zne, not in |- *; intros x y H1 H2; apply H1;
 apply (Zplus_reg_l (- y)); rewrite Zplus_comm; elim H2; 
 rewrite Zplus_opp_l; trivial.
Qed.

Theorem move_right_valid : forall s : step, valid1 (move_right s).

unfold valid1, move_right in |- *; intros s ep e p; Simplify; simpl in |- *;
 elim (rewrite_stable s e); simpl in |- *;
 [ symmetry  in |- *; apply Zegal_left; assumption
 | intro; apply Zle_left; assumption
 | intro; apply Zge_left; assumption
 | intro; apply Zgt_left; assumption
 | intro; apply Zlt_left; assumption
 | intro; apply Zne_left_2; assumption ].
Qed.

Definition do_normalize (i : nat) (s : step) := apply_oper_1 i (move_right s).

Theorem do_normalize_valid :
 forall (i : nat) (s : step), valid_hyps (do_normalize i s).

intros; unfold do_normalize in |- *; apply apply_oper_1_valid;
 apply move_right_valid.
Qed.

Fixpoint do_normalize_list (l : list step) (i : nat) 
 (h : list proposition) {struct l} : list proposition :=
  match l with
  | s :: l' => do_normalize_list l' (S i) (do_normalize i s h)
  | nil => h
  end.

Theorem do_normalize_list_valid :
 forall (l : list step) (i : nat), valid_hyps (do_normalize_list l i).

simple induction l; simpl in |- *; unfold valid_hyps in |- *;
 [ auto
 | intros a l' Hl' i ep e lp H; unfold valid_hyps in Hl'; apply Hl';
    apply (do_normalize_valid i a ep e lp); assumption ].
Qed.

Theorem normalize_goal :
 forall (s : list step) (ep : PropList) (env : list Z) (l : list proposition),
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) ep env (do_normalize_list s 0 l) ->
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) ep env l.

intros; apply valid_goal with (2 := H); apply do_normalize_list_valid.
Qed.

(* \subsubsection{Exécution de la trace} *)

Theorem execute_goal :
 forall (t : t_omega) (ep : PropList) (env : list Z) (l : list proposition),
 interp_list_goal ep env (execute_omega t l) ->
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) ep env l.

intros; apply (goal_valid (execute_omega t) (omega_valid t) ep env l H).
Qed.


Theorem append_goal :
 forall (ep : PropList) (e : list Z) (l1 l2 : list (list proposition)),
 interp_list_goal ep e l1 /\ interp_list_goal ep e l2 ->
 interp_list_goal ep e (l1 ++ l2).

intros ep e; simple induction l1;
 [ simpl in |- *; intros l2 (H1, H2); assumption
 | simpl in |- *; intros h1 t1 HR l2 ((H1, H2), H3); split; auto ].

Qed.

Require Import Decidable.

(* A simple decidability checker : if the proposition belongs to the
   simple grammar describe below then it is decidable. Proof is by 
   induction and uses well known theorem about arithmetic and propositional
   calculus *)

Fixpoint decidability (p : proposition) : bool :=
  match p with
  | EqTerm _ _ => true
  | LeqTerm _ _ => true
  | GeqTerm _ _ => true
  | GtTerm _ _ => true
  | LtTerm _ _ => true
  | NeqTerm _ _ => true
  | FalseTerm => true
  | TrueTerm => true
  | Tnot t => decidability t
  | Tand t1 t2 => decidability t1 && decidability t2
  | Timp t1 t2 => decidability t1 && decidability t2
  | Tor t1 t2 => decidability t1 && decidability t2
  | Tprop _ => false
  end.

Theorem decidable_correct :
 forall (ep : PropList) (e : list Z) (p : proposition),
 decidability p = true -> decidable (interp_proposition ep e p).

simple induction p; simpl in |- *; intros;
 [ apply dec_eq
 | apply dec_Zle
 | left; auto
 | right; unfold not in |- *; auto
 | apply dec_not; auto
 | apply dec_Zge
 | apply dec_Zgt
 | apply dec_Zlt
 | apply dec_Zne
 | apply dec_or; elim andb_prop with (1 := H1); auto
 | apply dec_and; elim andb_prop with (1 := H1); auto
 | apply dec_imp; elim andb_prop with (1 := H1); auto
 | discriminate H ].

Qed.

(* An interpretation function for a complete goal with an explicit
   conclusion. We use an intermediate fixpoint. *)

Fixpoint interp_full_goal (envp : PropList) (env : list Z) 
 (c : proposition) (l : list proposition) {struct l} : Prop :=
  match l with
  | nil => interp_proposition envp env c
  | p' :: l' =>
      interp_proposition envp env p' -> interp_full_goal envp env c l'
  end.

Definition interp_full (ep : PropList) (e : list Z)
  (lc : list proposition * proposition) : Prop :=
  match lc with
  | (l, c) => interp_full_goal ep e c l
  end.

(* Relates the interpretation of a complete goal with the interpretation
   of its hypothesis and conclusion *)

Theorem interp_full_false :
 forall (ep : PropList) (e : list Z) (l : list proposition) (c : proposition),
 (interp_hyps ep e l -> interp_proposition ep e c) -> interp_full ep e (l, c).

simple induction l; unfold interp_full in |- *; simpl in |- *;
 [ auto | intros a l1 H1 c H2 H3; apply H1; auto ].

Qed.

(* Push the conclusion in the list of hypothesis using a double negation
   If the decidability cannot be "proven", then just forget about the 
   conclusion (equivalent of replacing it with false) *)

Definition to_contradict (lc : list proposition * proposition) :=
  match lc with
  | (l, c) => if decidability c then Tnot c :: l else l
  end.

(* The previous operation is valid in the sense that the new list of
   hypothesis implies the original goal *)

Theorem to_contradict_valid :
 forall (ep : PropList) (e : list Z) (lc : list proposition * proposition),
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) ep e (to_contradict lc) ->
 interp_full ep e lc.

intros ep e lc; case lc; intros l c; simpl in |- *;
 pattern (decidability c) in |- *; apply bool_ind2;
 [ simpl in |- *; intros H H1; apply interp_full_false; intros H2;
    apply not_not;
    [ apply decidable_correct; assumption
    | unfold not at 1 in |- *; intro H3; apply hyps_to_goal with (2 := H2);
       auto ]
 | intros H1 H2; apply interp_full_false; intro H3;
    elim hyps_to_goal with (1 := H2); assumption ].
Qed.

(* [map_cons x l] adds [x] at the head of each list in [l] (which is a list
   of lists *)

Fixpoint map_cons (A : Set) (x : A) (l : list (list A)) {struct l} :
 list (list A) :=
  match l with
  | nil => nil
  | l :: ll => (x :: l) :: map_cons A x ll
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
 
Fixpoint destructure_hyps (nn : nat) (ll : list proposition) {struct nn} :
 list (list proposition) :=
  match nn with
  | O => ll :: nil
  | S n =>
      match ll with
      | nil => nil :: nil
      | Tor p1 p2 :: l =>
          destructure_hyps n (p1 :: l) ++ destructure_hyps n (p2 :: l)
      | Tand p1 p2 :: l => destructure_hyps n (p1 :: p2 :: l)
      | Timp p1 p2 :: l =>
          if decidability p1
          then
           destructure_hyps n (Tnot p1 :: l) ++ destructure_hyps n (p2 :: l)
          else map_cons _ (Timp p1 p2) (destructure_hyps n l)
      | Tnot p :: l =>
          match p with
          | Tnot p1 =>
              if decidability p1
              then destructure_hyps n (p1 :: l)
              else map_cons _ (Tnot (Tnot p1)) (destructure_hyps n l)
          | Tor p1 p2 => destructure_hyps n (Tnot p1 :: Tnot p2 :: l)
          | Tand p1 p2 =>
              if decidability p1
              then
               destructure_hyps n (Tnot p1 :: l) ++
               destructure_hyps n (Tnot p2 :: l)
              else map_cons _ (Tnot p) (destructure_hyps n l)
          | _ => map_cons _ (Tnot p) (destructure_hyps n l)
          end
      | x :: l => map_cons _ x (destructure_hyps n l)
      end
  end.

Theorem map_cons_val :
 forall (ep : PropList) (e : list Z) (p : proposition)
   (l : list (list proposition)),
 interp_proposition ep e p ->
 interp_list_hyps ep e l -> interp_list_hyps ep e (map_cons _ p l).

simple induction l; simpl in |- *; [ auto | intros; elim H1; intro H2; auto ].
Qed.

Hint Resolve map_cons_val append_valid decidable_correct.

Theorem destructure_hyps_valid :
 forall n : nat, valid_list_hyps (destructure_hyps n).

simple induction n;
 [ unfold valid_list_hyps in |- *; simpl in |- *; auto
 | unfold valid_list_hyps at 2 in |- *; intros n1 H ep e lp; case lp;
    [ simpl in |- *; auto
    | intros p l; case p;
       try
        (simpl in |- *; intros; apply map_cons_val; simpl in |- *; elim H0;
          auto);
       [ intro p'; case p';
          try
           (simpl in |- *; intros; apply map_cons_val; simpl in |- *; elim H0;
             auto);
          [ simpl in |- *; intros p1 (H1, H2);
             pattern (decidability p1) in |- *; apply bool_ind2; 
             intro H3;
             [ apply H; simpl in |- *; split;
                [ apply not_not; auto | assumption ]
             | auto ]
          | simpl in |- *; intros p1 p2 (H1, H2); apply H; simpl in |- *;
             elim not_or with (1 := H1); auto
          | simpl in |- *; intros p1 p2 (H1, H2);
             pattern (decidability p1) in |- *; apply bool_ind2; 
             intro H3;
             [ apply append_valid; elim not_and with (2 := H1);
                [ intro; left; apply H; simpl in |- *; auto
                | intro; right; apply H; simpl in |- *; auto
                | auto ]
             | auto ] ]
       | simpl in |- *; intros p1 p2 (H1, H2); apply append_valid;
          (elim H1; intro H3; simpl in |- *; [ left | right ]); 
          apply H; simpl in |- *; auto
       | simpl in |- *; intros; apply H; simpl in |- *; tauto
       | simpl in |- *; intros p1 p2 (H1, H2);
          pattern (decidability p1) in |- *; apply bool_ind2; 
          intro H3;
          [ apply append_valid; elim imp_simp with (2 := H1);
             [ intro H4; left; simpl in |- *; apply H; simpl in |- *; auto
             | intro H4; right; simpl in |- *; apply H; simpl in |- *; auto
             | auto ]
          | auto ] ] ] ].

Qed.

Definition prop_stable (f : proposition -> proposition) :=
  forall (ep : PropList) (e : list Z) (p : proposition),
  interp_proposition ep e p <-> interp_proposition ep e (f p).

Definition p_apply_left (f : proposition -> proposition) 
  (p : proposition) :=
  match p with
  | Timp x y => Timp (f x) y
  | Tor x y => Tor (f x) y
  | Tand x y => Tand (f x) y
  | Tnot x => Tnot (f x)
  | x => x
  end.

Theorem p_apply_left_stable :
 forall f : proposition -> proposition,
 prop_stable f -> prop_stable (p_apply_left f).

unfold prop_stable in |- *; intros f H ep e p; split;
 (case p; simpl in |- *; auto; intros p1; elim (H ep e p1); tauto).
Qed.

Definition p_apply_right (f : proposition -> proposition)
  (p : proposition) :=
  match p with
  | Timp x y => Timp x (f y)
  | Tor x y => Tor x (f y)
  | Tand x y => Tand x (f y)
  | Tnot x => Tnot (f x)
  | x => x
  end.

Theorem p_apply_right_stable :
 forall f : proposition -> proposition,
 prop_stable f -> prop_stable (p_apply_right f).

unfold prop_stable in |- *; intros f H ep e p; split;
 (case p; simpl in |- *; auto;
   [ intros p1; elim (H ep e p1); tauto
   | intros p1 p2; elim (H ep e p2); tauto
   | intros p1 p2; elim (H ep e p2); tauto
   | intros p1 p2; elim (H ep e p2); tauto ]).
Qed.

Definition p_invert (f : proposition -> proposition) 
  (p : proposition) :=
  match p with
  | EqTerm x y => Tnot (f (NeqTerm x y))
  | LeqTerm x y => Tnot (f (GtTerm x y))
  | GeqTerm x y => Tnot (f (LtTerm x y))
  | GtTerm x y => Tnot (f (LeqTerm x y))
  | LtTerm x y => Tnot (f (GeqTerm x y))
  | NeqTerm x y => Tnot (f (EqTerm x y))
  | x => x
  end.

Theorem p_invert_stable :
 forall f : proposition -> proposition,
 prop_stable f -> prop_stable (p_invert f).

unfold prop_stable in |- *; intros f H ep e p; split;
 (case p; simpl in |- *; auto;
   [ intros t1 t2; elim (H ep e (NeqTerm t1 t2)); simpl in |- *;
      unfold Zne in |- *;
      generalize (dec_eq (interp_term e t1) (interp_term e t2));
      unfold decidable in |- *; tauto
   | intros t1 t2; elim (H ep e (GtTerm t1 t2)); simpl in |- *;
      unfold Zgt in |- *;
      generalize (dec_Zgt (interp_term e t1) (interp_term e t2));
      unfold decidable, Zgt, Zle in |- *; tauto
   | intros t1 t2; elim (H ep e (LtTerm t1 t2)); simpl in |- *;
      unfold Zlt in |- *;
      generalize (dec_Zlt (interp_term e t1) (interp_term e t2));
      unfold decidable, Zge in |- *; tauto
   | intros t1 t2; elim (H ep e (LeqTerm t1 t2)); simpl in |- *;
      generalize (dec_Zgt (interp_term e t1) (interp_term e t2));
      unfold Zle, Zgt in |- *; unfold decidable in |- *; 
      tauto
   | intros t1 t2; elim (H ep e (GeqTerm t1 t2)); simpl in |- *;
      generalize (dec_Zlt (interp_term e t1) (interp_term e t2));
      unfold Zge, Zlt in |- *; unfold decidable in |- *; 
      tauto
   | intros t1 t2; elim (H ep e (EqTerm t1 t2)); simpl in |- *;
      generalize (dec_eq (interp_term e t1) (interp_term e t2));
      unfold decidable, Zne in |- *; tauto ]).
Qed.

Theorem Zlt_left_inv : forall x y : Z, (0 <= y + -1 + - x)%Z -> (x < y)%Z.

intros; apply Zsucc_lt_reg; apply Zle_lt_succ;
 apply (fun a b : Z => Zplus_le_reg_r a b (-1 + - x)); 
 rewrite Zplus_assoc; unfold Zsucc in |- *; rewrite (Zplus_assoc_reverse x);
 rewrite (Zplus_assoc y); simpl in |- *; rewrite Zplus_0_r;
 rewrite Zplus_opp_r; assumption.
Qed.

Theorem move_right_stable : forall s : step, prop_stable (move_right s).

unfold move_right, prop_stable in |- *; intros s ep e p; split;
 [ Simplify; simpl in |- *; elim (rewrite_stable s e); simpl in |- *;
    [ symmetry  in |- *; apply Zegal_left; assumption
    | intro; apply Zle_left; assumption
    | intro; apply Zge_left; assumption
    | intro; apply Zgt_left; assumption
    | intro; apply Zlt_left; assumption
    | intro; apply Zne_left_2; assumption ]
 | case p; simpl in |- *; intros; auto; generalize H; elim (rewrite_stable s);
    simpl in |- *; intro H1;
    [ rewrite (Zplus_0_r_reverse (interp_term e t0)); rewrite H1;
       rewrite Zplus_permute; rewrite Zplus_opp_r; 
       rewrite Zplus_0_r; trivial
    | apply (fun a b : Z => Zplus_le_reg_r a b (- interp_term e t));
       rewrite Zplus_opp_r; assumption
    | apply Zle_ge;
       apply (fun a b : Z => Zplus_le_reg_r a b (- interp_term e t0));
       rewrite Zplus_opp_r; assumption
    | apply Zlt_gt; apply Zlt_left_inv; assumption
    | apply Zlt_left_inv; assumption
    | unfold Zne, not in |- *; unfold Zne in H1; intro H2; apply H1;
       rewrite H2; rewrite Zplus_opp_r; trivial ] ].
Qed.


Fixpoint p_rewrite (s : p_step) : proposition -> proposition :=
  match s with
  | P_LEFT s => p_apply_left (p_rewrite s)
  | P_RIGHT s => p_apply_right (p_rewrite s)
  | P_STEP s => move_right s
  | P_INVERT s => p_invert (move_right s)
  | P_NOP => fun p : proposition => p
  end.

Theorem p_rewrite_stable : forall s : p_step, prop_stable (p_rewrite s).


simple induction s; simpl in |- *;
 [ intros; apply p_apply_left_stable; trivial
 | intros; apply p_apply_right_stable; trivial
 | intros; apply p_invert_stable; apply move_right_stable
 | apply move_right_stable
 | unfold prop_stable in |- *; simpl in |- *; intros; split; auto ].
Qed.

Fixpoint normalize_hyps (l : list h_step) (lh : list proposition) {struct l}
 : list proposition :=
  match l with
  | nil => lh
  | pair_step i s :: r => normalize_hyps r (apply_oper_1 i (p_rewrite s) lh)
  end.

Theorem normalize_hyps_valid :
 forall l : list h_step, valid_hyps (normalize_hyps l).

simple induction l; unfold valid_hyps in |- *; simpl in |- *;
 [ auto
 | intros n_s r; case n_s; intros n s H ep e lp H1; apply H;
    apply apply_oper_1_valid;
    [ unfold valid1 in |- *; intros ep1 e1 p1 H2;
       elim (p_rewrite_stable s ep1 e1 p1); auto
    | assumption ] ].
Qed.

Theorem normalize_hyps_goal :
 forall (s : list h_step) (ep : PropList) (env : list Z)
   (l : list proposition),
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) ep env (normalize_hyps s l) ->
 (fun (envp : PropList) (env : list Z) (l : list proposition) =>
  interp_goal_concl envp env FalseTerm l) ep env l.

intros; apply valid_goal with (2 := H); apply normalize_hyps_valid.
Qed.

Fixpoint extract_hyp_pos (s : list direction) (p : proposition) {struct s} :
 proposition :=
  match s with
  | D_left :: l =>
      match p with
      | Tand x y => extract_hyp_pos l x
      | _ => p
      end
  | D_right :: l =>
      match p with
      | Tand x y => extract_hyp_pos l y
      | _ => p
      end
  | D_mono :: l => match p with
                   | Tnot x => extract_hyp_neg l x
                   | _ => p
                   end
  | _ => p
  end
 
 with extract_hyp_neg (s : list direction) (p : proposition) {struct s} :
 proposition :=
  match s with
  | D_left :: l =>
      match p with
      | Tor x y => extract_hyp_neg l x
      | Timp x y => if decidability x then extract_hyp_pos l x else Tnot p
      | _ => Tnot p
      end
  | D_right :: l =>
      match p with
      | Tor x y => extract_hyp_neg l y
      | Timp x y => extract_hyp_neg l y
      | _ => Tnot p
      end
  | D_mono :: l =>
      match p with
      | Tnot x => if decidability x then extract_hyp_pos l x else Tnot p
      | _ => Tnot p
      end
  | _ =>
      match p with
      | Tnot x => if decidability x then x else Tnot p
      | _ => Tnot p
      end
  end.

Definition co_valid1 (f : proposition -> proposition) :=
  forall (ep : PropList) (e : list Z) (p1 : proposition),
  interp_proposition ep e (Tnot p1) -> interp_proposition ep e (f p1).

Theorem extract_valid :
 forall s : list direction,
 valid1 (extract_hyp_pos s) /\ co_valid1 (extract_hyp_neg s).

unfold valid1, co_valid1 in |- *; simple induction s;
 [ split;
    [ simpl in |- *; auto
    | intros ep e p1; case p1; simpl in |- *; auto; intro p;
       pattern (decidability p) in |- *; apply bool_ind2;
       [ intro H; generalize (decidable_correct ep e p H);
          unfold decidable in |- *; tauto
       | simpl in |- *; auto ] ]
 | intros a s' (H1, H2); simpl in H2; split; intros ep e p; case a; auto;
    case p; auto; simpl in |- *; intros;
    (apply H1; tauto) ||
      (apply H2; tauto) ||
        (pattern (decidability p0) in |- *; apply bool_ind2;
          [ intro H3; generalize (decidable_correct ep e p0 H3);
             unfold decidable in |- *; intro H4; apply H1; 
             tauto
          | intro; tauto ]) ].

Qed.

Fixpoint decompose_solve (s : e_step) (h : list proposition) {struct s} :
 list (list proposition) :=
  match s with
  | E_SPLIT i dl s1 s2 =>
      match extract_hyp_pos dl (nth_hyps i h) with
      | Tor x y => decompose_solve s1 (x :: h) ++ decompose_solve s2 (y :: h)
      | Tnot (Tand x y) =>
          if decidability x
          then
           decompose_solve s1 (Tnot x :: h) ++
           decompose_solve s2 (Tnot y :: h)
          else h :: nil
      | _ => h :: nil
      end
  | E_EXTRACT i dl s1 =>
      decompose_solve s1 (extract_hyp_pos dl (nth_hyps i h) :: h)
  | E_SOLVE t => execute_omega t h
  end.

Theorem decompose_solve_valid :
 forall s : e_step, valid_list_goal (decompose_solve s).

intro s; apply goal_valid; unfold valid_list_hyps in |- *; elim s;
 simpl in |- *; intros;
 [ cut (interp_proposition ep e1 (extract_hyp_pos l (nth_hyps n lp)));
    [ case (extract_hyp_pos l (nth_hyps n lp)); simpl in |- *; auto;
       [ intro p; case p; simpl in |- *; auto; intros p1 p2 H2;
          pattern (decidability p1) in |- *; apply bool_ind2;
          [ intro H3; generalize (decidable_correct ep e1 p1 H3); intro H4;
             apply append_valid; elim H4; intro H5;
             [ right; apply H0; simpl in |- *; tauto
             | left; apply H; simpl in |- *; tauto ]
          | simpl in |- *; auto ]
       | intros p1 p2 H2; apply append_valid; simpl in |- *; elim H2;
          [ intros H3; left; apply H; simpl in |- *; auto
          | intros H3; right; apply H0; simpl in |- *; auto ] ]
    | elim (extract_valid l); intros H2 H3; apply H2; apply nth_valid; auto ]
 | intros; apply H; simpl in |- *; split;
    [ elim (extract_valid l); intros H2 H3; apply H2; apply nth_valid; auto
    | auto ]
 | apply omega_valid with (1 := H) ].

Qed.

(* \subsection{La dernière étape qui élimine tous les séquents inutiles} *)

Definition valid_lhyps
  (f : list (list proposition) -> list (list proposition)) :=
  forall (ep : PropList) (e : list Z) (lp : list (list proposition)),
  interp_list_hyps ep e lp -> interp_list_hyps ep e (f lp).

Fixpoint reduce_lhyps (lp : list (list proposition)) :
 list (list proposition) :=
  match lp with
  | (FalseTerm :: nil) :: lp' => reduce_lhyps lp'
  | x :: lp' => x :: reduce_lhyps lp'
  | nil => nil (A:=list proposition)
  end.

Theorem reduce_lhyps_valid : valid_lhyps reduce_lhyps.

unfold valid_lhyps in |- *; intros ep e lp; elim lp;
 [ simpl in |- *; auto
 | intros a l HR; elim a;
    [ simpl in |- *; tauto
    | intros a1 l1; case l1; case a1; simpl in |- *; try tauto ] ].
Qed.

Theorem do_reduce_lhyps :
 forall (envp : PropList) (env : list Z) (l : list (list proposition)),
 interp_list_goal envp env (reduce_lhyps l) -> interp_list_goal envp env l.

intros envp env l H; apply list_goal_to_hyps; intro H1;
 apply list_hyps_to_goal with (1 := H); apply reduce_lhyps_valid; 
 assumption.
Qed.

Definition concl_to_hyp (p : proposition) :=
  if decidability p then Tnot p else TrueTerm.

Definition do_concl_to_hyp :
  forall (envp : PropList) (env : list Z) (c : proposition)
    (l : list proposition),
  (fun (envp : PropList) (env : list Z) (l : list proposition) =>
   interp_goal_concl envp env FalseTerm l) envp env (
    concl_to_hyp c :: l) -> interp_goal_concl envp env c l.

simpl in |- *; intros envp env c l; induction  l as [| a l Hrecl];
 [ simpl in |- *; unfold concl_to_hyp in |- *;
    pattern (decidability c) in |- *; apply bool_ind2;
    [ intro H; generalize (decidable_correct envp env c H);
       unfold decidable in |- *; simpl in |- *; tauto
    | simpl in |- *; intros H1 H2; elim H2; trivial ]
 | simpl in |- *; tauto ].
Qed.

Definition omega_tactic (t1 : e_step) (t2 : list h_step) 
  (c : proposition) (l : list proposition) :=
  reduce_lhyps (decompose_solve t1 (normalize_hyps t2 (concl_to_hyp c :: l))).

Theorem do_omega :
 forall (t1 : e_step) (t2 : list h_step) (envp : PropList) 
   (env : list Z) (c : proposition) (l : list proposition),
 interp_list_goal envp env (omega_tactic t1 t2 c l) ->
 interp_goal_concl envp env c l.

unfold omega_tactic in |- *; intros; apply do_concl_to_hyp;
 apply (normalize_hyps_goal t2); apply (decompose_solve_valid t1);
 apply do_reduce_lhyps; assumption.
Qed.