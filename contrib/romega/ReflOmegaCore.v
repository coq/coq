(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

Require Arith.
Require PolyList.
Require Bool.
Require ZArith_base.

(* \subsection{Définition des types} *)

(* \subsubsection{Définition des termes dans Z réifiés}
   Les termes comprennent les entiers relatifs [Tint] et les 
   variables [Tvar] ainsi que les opérations de base sur Z (addition,
   multiplication, opposé et soustraction). Les deux denières sont
   rapidement traduites dans les deux premières durant la normalisation
   des termes. *)

Inductive term : Set :=
   Tint : Z -> term
 | Tplus : term -> term -> term
 | Tmult : term -> term -> term
 | Tminus : term -> term -> term
 | Topp : term -> term
 | Tvar : nat -> term
.

(* \subsubsection{Définition des buts réifiés} *)
(* Définition très restreinte des prédicats manipulés (à enrichir). 
   La prise en compte des négations et des diséquations demande la
   prise en compte de la résolution en parallèle de plusieurs buts.
   Ceci n'est possible qu'en modifiant de manière drastique la définition
   de normalize qui doit pouvoir générer des listes de buts. Il faut
   donc aussi modifier la normalisation qui peut elle aussi amener la
   génération d'une liste de but et donc l'application d'une liste de
   tactiques de résolution ([execute_omega])  *)
Inductive proposition : Set :=
  EqTerm : term -> term -> proposition
| LeqTerm : term -> term -> proposition
| TrueTerm : proposition
| FalseTerm : proposition
| Tnot : proposition -> proposition
| GeqTerm : term -> term -> proposition
| GtTerm : term -> term -> proposition
| LtTerm : term -> term -> proposition
| NeqTerm: term -> term -> proposition.

(* Définition des hypothèses *)
Syntactic Definition hyps := (list proposition).      

Definition absurd := (cons FalseTerm (nil proposition)).

(* \subsubsection{Traces de fusion d'équations} *)

Inductive t_fusion : Set :=
    F_equal : t_fusion | F_cancel : t_fusion
  | F_left : t_fusion  | F_right : t_fusion.

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
Fixpoint interp_proposition [env: (list Z); p:proposition] : Prop := 
  Cases p of
    (EqTerm t1 t2) => ((interp_term env t1) = (interp_term env t2))
  | (LeqTerm t1 t2) => `(interp_term env t1) <= (interp_term env t2)`
  | TrueTerm => True
  | FalseTerm => False
  | (Tnot p') => ~(interp_proposition env p')
  | (GeqTerm t1 t2) => `(interp_term env t1) >= (interp_term env t2)`
  | (GtTerm t1 t2) => `(interp_term env t1) > (interp_term env t2)`
  | (LtTerm t1 t2) => `(interp_term env t1) < (interp_term env t2)`
  | (NeqTerm t1 t2) => `(Zne (interp_term env t1) (interp_term env t2))`
  end.

(* \subsubsection{Inteprétation des listes d'hypothèses}
   \paragraph{Sous forme de conjonction}
   Interprétation sous forme d'une conjonction d'hypothèses plus faciles
   à manipuler individuellement *)

Fixpoint interp_hyps [env : (list Z); l: hyps] : Prop :=
  Cases l of 
     nil => True
   | (cons p' l') => (interp_proposition env p') /\ (interp_hyps env l')
  end.

(* \paragraph{Sous forme de but}
   C'est cette interpétation que l'on utilise sur le but (car on utilise
   [Generalize] et qu'une conjonction est forcément lourde (répétition des
   types dans les conjonctions intermédiaires) *)

Fixpoint interp_goal [env : (list Z); l: hyps] : Prop :=
  Cases l of 
     nil => False
   | (cons p' l') => (interp_proposition env p') -> (interp_goal env l')
  end.

(* Les théorèmes qui suivent assurent la correspondance entre les deux
   interprétations. *)

Theorem goal_to_hyps : 
  (env : (list Z); l: hyps) 
     ((interp_hyps env l) -> False) -> (interp_goal env l).

Induction l; [
  Simpl; Auto
| Simpl; Intros a l1 H1 H2 H3; Apply H1; Intro H4; Apply H2; Auto ].
Save.

Theorem hyps_to_goal : 
  (env : (list Z); l: hyps) 
     (interp_goal env l) -> ((interp_hyps env l) -> False).

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
  (e: (list Z)) (p1: proposition) 
    (interp_proposition e p1) -> (interp_proposition e (f p1)).

Definition valid2 [f: proposition -> proposition -> proposition] :=
  (e: (list Z)) (p1,p2: proposition) 
    (interp_proposition e p1) -> (interp_proposition e p2) ->
      (interp_proposition e (f p1 p2)).

(* Dans cette notion de validité, la fonction prend directement une 
   liste de propositions et rend une nouvelle liste de propositions. 
   On reste contravariant *)

Definition valid_hyps [f: hyps -> hyps] :=
  (e : (list Z)) (lp: hyps) (interp_hyps e lp) -> (interp_hyps e (f lp)).

(* Enfin ce théorème élimine la contravariance et nous ramène à une 
   opération sur les buts *)

Theorem valid_goal :
  (env : (list Z); l: hyps; a : hyps -> hyps) 
    (valid_hyps a) -> (interp_goal env (a l)) -> (interp_goal env l).

Intros; Apply goal_to_hyps; Intro H1; Apply (hyps_to_goal env (a l) H0);
Apply H; Assumption.
Save.

(* \subsubsection{Généralisation à des listes de buts (disjonctions)} *)

Syntactic Definition lhyps := (list hyps).

Fixpoint interp_list_hyps [env: (list Z); l : lhyps] : Prop :=
   Cases l of
      nil => False
    | (cons h l') => (interp_hyps env h) \/ (interp_list_hyps env l')
   end.

Fixpoint interp_list_goal [env: (list Z);l : lhyps] : Prop :=
   Cases l of
      nil => True
    | (cons h l') => (interp_goal env h) /\ (interp_list_goal env l')
   end.

Theorem list_goal_to_hyps : 
  (env: (list Z); l: lhyps)
    ((interp_list_hyps env l) -> False) -> (interp_list_goal env l).

Induction l; Simpl; [
  Auto
| Intros h1 l1 H H1; Split; [
    Apply goal_to_hyps; Intro H2; Apply H1; Auto
  | Apply H; Intro H2; Apply H1; Auto ]].
Save.

Theorem list_hyps_to_goal : 
  (env: (list Z); l: lhyps)
    (interp_list_goal env l) -> ((interp_list_hyps env l) -> False).

Induction l; Simpl; [
  Auto
|  Intros h1 l1 H (H1,H2) H3; Elim H3; Intro H4; [
     Apply hyps_to_goal with 1 := H1; Assumption
   | Auto ]].
Save.

Definition valid_list_hyps [f: hyps -> lhyps] :=
  (e : (list Z)) (lp: hyps) (interp_hyps e lp) -> (interp_list_hyps e (f lp)).

Definition valid_list_goal [f: hyps -> lhyps] :=
  (e : (list Z)) (lp: hyps) 
     (interp_list_goal e (f lp)) -> (interp_goal e lp) .

Theorem goal_valid : 
  (f: hyps -> lhyps) (valid_list_hyps f) -> (valid_list_goal f).

Unfold valid_list_goal; Intros f H e lp H1; Apply goal_to_hyps;
Intro H2; Apply list_hyps_to_goal with 1:=H1; Apply (H e lp); Assumption.
Save.
 
Theorem append_valid :
  (e: (list Z)) (l1,l2:lhyps)
     (interp_list_hyps e l1) \/ (interp_list_hyps e l2) ->
     (interp_list_hyps e (app l1 l2)).

Intros e; Induction l1; [
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
  (e: (list Z); i:nat; l: hyps) 
     (interp_hyps e l) -> (interp_proposition e (nth_hyps i l)).

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

Unfold valid_hyps; Intros i f Hf e; Elim i; [
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
  (* Interprétations *)
  | [ (interp_hyps ? ?1) ] -> (loop ?1)
  | [ (interp_list_hyps ? ?1) ] -> (loop ?1)
  | [ (interp_proposition ? ?1) ] -> (loop ?1)
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
  | [(Case ?1 of ? ? ? ?   ? ? ? ?  ? end)] -> 
       (Case ?1; [ Intro; Intro | Intro; Intro | Idtac | Idtac 
                 | Intro | Intro; Intro | Intro; Intro | Intro; Intro
                 | Intro; Intro ]);
        Auto; (Simplify ())
  | [(Case ?1 of ? ? ? ? ? ? end)] -> 
       (Case ?1; [ Intro | Intro; Intro | Intro; Intro | Intro; Intro | 
                   Intro | Intro ]); Auto; (Simplify ())
  | [(Case (Zcompare ?1 ?2) of ? ? ? end)] -> 
       (Elim_Zcompare ?1 ?2) ; Intro ; Auto; (Simplify ())
  | [(Case ?1 of ? ? ? end)] -> 
       (Case ?1; [ Idtac | Intro | Intro ]); Auto; (Simplify ())
  | [(Case (eq_Z ?1 ?2) of ? ? end)] -> 
       ((Elim_eq_Z ?1 ?2); Intro H; [Rewrite H; Clear H | Clear H]);
       Simpl; Auto; (Simplify ())
  | [(Case (eq_term ?1 ?2) of ? ? end)] -> 
       ((Elim_eq_term ?1 ?2); Intro H; [Rewrite H; Clear H | Clear H]); 
       Simpl; Auto; (Simplify ())
  | [(Case (eq_pos ?1 ?2) of ? ? end)] -> 
       ((Elim_eq_pos ?1 ?2); Intro H; [Rewrite H; Clear H | Clear H]);
       Simpl; Auto; (Simplify ())
  | _ -> Fail)
And Simplify () := (
  Match Context With [|- ?1 ] -> Try (loop ?1) | _ -> Idtac).

(* L'utilisation de Match n'est qu'un hack pour contourner un bug de la 7.0 *)
Tactic Definition ProveStable x th :=
  (Match x With [?1] -> Unfold term_stable ?1; Intros; (Simplify ()); Simpl; Apply th).

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

Unfold term_stable T_OMEGA13; Intros; (Simplify ()); Simpl; 
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
| Intros step l H; Case step; [
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

(* \paragraph{Fusion avec anihilation} *)
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

(* \subsubsection{Opérations afines sur une équation} *)
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

Inductive step : Set := 
 | C_DO_BOTH : step -> step -> step
 | C_LEFT : step -> step
 | C_RIGHT : step -> step
 | C_SEQ : step -> step -> step
 | C_NOP : step
 | C_OPP_PLUS : step
 | C_OPP_OPP : step
 | C_OPP_MULT_R : step
 | C_OPP_ONE : step
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
Generalize (nth_valid e i lp); (Simplify ()); Simpl; (Elim_eq_Z z0 ZERO); Auto;
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
Generalize (nth_valid e i lp); (Simplify ()); Simpl; Unfold Zle; Simpl;
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

Unfold valid_hyps not_exact_divide; Intros; Generalize (nth_valid e i lp);
(Simplify ());
(Elim_eq_term '(scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2)))
	     't1); Auto; 
(Simplify ()); 
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

Unfold valid_hyps contradiction; Intros t i j e l H;
Generalize (nth_valid ? i ? H); Generalize (nth_valid ? j ? H);
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

Unfold valid_hyps negate_contradict; Intros i j e l H;
Generalize (nth_valid ? i ? H); Generalize (nth_valid ? j ? H);
Case (nth_hyps i l); Auto; Intros t1 t2; Case t1; Auto; Intros z; Case z; Auto;
Case (nth_hyps j l); Auto; Intros t3 t4; Case t3; Auto; Intros z'; Case z'; 
Auto; Simpl; Intros H1 H2; [
  (Elim_eq_term t2 t4); Intro H3; [ Elim H1; Elim H3; Assumption | Assumption ]
| (Elim_eq_term t2 t4); Intro H3; 
    [ Elim H2; Rewrite H3; Assumption | Assumption ]].

Save.

Theorem negate_contradict_inv_valid :
  (t,i,j:nat) (valid_hyps (negate_contradict_inv t i j)).


Unfold valid_hyps negate_contradict_inv; Intros t i j e l H;
Generalize (nth_valid ? i ? H); Generalize (nth_valid ? j ? H);
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

Unfold valid2; Intros k1 k2 t e p1 p2; Unfold sum; (Simplify ()); Simpl; Auto;
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


Unfold valid1 exact_divide; Intros k1 k2 t e p1; (Simplify ());Simpl; Auto;
(Elim_eq_term  '(scalar_norm t (Tmult k2 (Tint k1))) 't1); Simpl; Auto;
(Elim_eq_Z 'k1 '(ZERO)); Simpl; Auto;  Intros H1 H2; Elim H2; 
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

Unfold valid1 divide_and_approx; Intros k1 k2 body t e p1;(Simplify ());
(Elim_eq_term '(scalar_norm_add t (Tplus (Tmult body (Tint k1)) (Tint k2))) 't1); (Simplify ()); Auto;  Intro E; Elim E; Simpl; 
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

Unfold valid2 merge_eq; Intros n e p1 p2; (Simplify ()); Simpl; Auto;
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

Unfold valid_hyps constant_nul; Intros; Generalize (nth_valid e i lp);
(Simplify ()); Simpl; Unfold Zne; Intro H1; Absurd `0=0`; Auto.
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

Unfold valid2; Intros m s e p1 p2; Unfold state; (Simplify ()); Simpl;Auto;
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

Unfold valid_list_hyps split_ineq; Intros i t f1 f2 H1 H2 e lp H; 
Generalize (nth_valid ? i ? H); 
Case (nth_hyps i lp); Simpl; Auto; Intros t1 t2; Case t1; Simpl; Auto;
Intros z; Case z; Simpl; Auto;
Intro H3; Apply append_valid;Elim (OMEGA19 (interp_term e t2)) ;[
  Intro H4; Left; Apply H1; Simpl; Elim (add_norm_stable t); Simpl; Auto
| Intro H4; Right; Apply H2; Simpl; Elim (scalar_norm_add_stable t); 
  Simpl; Auto
| Generalize H3; Unfold Zne not; Intros E1 E2; Apply E1; Symmetry; Trivial ].
Save.


(* \subsection{La fonction de rejeu de la trace} *)
Inductive t_omega : Set :=
   (* n = 0 n!= 0 *)
 | O_CONSTANT_NOT_NUL : nat -> t_omega
 | O_CONSTANT_NEG : nat -> t_omega
   (* division et approximation d'une équation *)
 | O_DIV_APPROX : Z -> Z -> term -> nat -> t_omega -> nat -> t_omega
   (* pas de solution car pas de division exacte (fin) *)
 | O_NOT_EXACT_DIVIDE :  Z -> Z -> term -> nat -> nat -> t_omega
   (* division exacte *)
 | O_EXACT_DIVIDE : Z -> term -> nat -> t_omega -> nat -> t_omega
 | O_SUM : Z -> nat -> Z -> nat -> (list t_fusion) -> t_omega -> t_omega
 | O_CONTRADICTION : nat -> nat -> nat -> t_omega
 | O_MERGE_EQ : nat -> nat -> nat -> t_omega -> t_omega
 | O_SPLIT_INEQ : nat -> nat -> t_omega -> t_omega -> t_omega
 | O_CONSTANT_NUL : nat -> t_omega 
 | O_NEGATE_CONTRADICT : nat -> nat -> t_omega
 | O_NEGATE_CONTRADICT_INV : nat -> nat -> nat -> t_omega
 | O_STATE : Z -> step -> nat -> nat -> t_omega -> t_omega.

Syntactic Definition singleton :=  [a: hyps] (cons a (nil hyps)).

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
  Apply (constant_not_nul_valid n e lp H)
| Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (constant_neg_valid n e lp H)
| Unfold valid_list_hyps valid_hyps; Intros k1 k2 body n t' Ht' m e lp H; 
  Apply Ht';
  Apply (apply_oper_1_valid m (divide_and_approx k1 k2 body n)
	  (divide_and_approx_valid k1 k2 body n) e lp H)
| Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (not_exact_divide_valid z z0 t0 n n0 e lp H)
| Unfold valid_list_hyps valid_hyps; Intros k body n t' Ht' m e lp H; 
  Apply Ht';
  Apply (apply_oper_1_valid m (exact_divide k body n)
	  (exact_divide_valid k body n) e lp H)
| Unfold valid_list_hyps valid_hyps; Intros k1 i1 k2 i2 trace t' Ht' e lp H;
  Apply Ht'; 
  Apply (apply_oper_2_valid i1 i2 (sum k1 k2 trace) 
	  (sum_valid k1 k2 trace) e lp H)
| Unfold valid_list_hyps; Simpl; Intros; Left; 
  Apply (contradiction_valid n n0 n1 e lp H)
| Unfold valid_list_hyps valid_hyps; Intros trace i1 i2 t' Ht' e lp H; 
  Apply Ht';
  Apply (apply_oper_2_valid i1 i2 (merge_eq trace) 
          (merge_eq_valid trace) e lp H) 
| Intros t' i k1 H1 k2 H2; Unfold valid_list_hyps; Simpl; Intros e lp H;
  Apply (split_ineq_valid i t' (execute_omega k1) (execute_omega k2) 
	 H1 H2 e lp H)
| Unfold valid_list_hyps; Simpl; Intros i e lp H; Left; 
  Apply (constant_nul_valid i e lp H)
| Unfold valid_list_hyps; Simpl; Intros i j e lp H; Left; 
  Apply (negate_contradict_valid i j e lp H)
| Unfold valid_list_hyps; Simpl; Intros n i j e lp H; Left; 
  Apply (negate_contradict_inv_valid n i j e lp H)
| Unfold valid_list_hyps valid_hyps; Intros m s i1 i2 t' Ht' e lp H; Apply Ht';
  Apply (apply_oper_2_valid i1 i2 (state m s) (state_valid m s) e lp H)
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

Unfold valid1 move_right; Intros s e p; (Simplify ()); Simpl;
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
| Intros a l' Hl' i e lp H; Unfold valid_hyps in Hl'; Apply Hl';
  Apply (do_normalize_valid i a e lp); Assumption ].
Save.

Theorem normalize_goal :
  (s: (list step); env : (list Z); l: hyps)
    (interp_goal env (do_normalize_list s O l)) -> 
      (interp_goal env l).

Intros; Apply valid_goal with 2:=H; Apply do_normalize_list_valid.
Save.

(* \subsubsection{Exécution de la trace} *)

Theorem execute_goal :
  (t : t_omega; env : (list Z); l: hyps)
    (interp_list_goal env (execute_omega t l)) -> (interp_goal env l).

Intros; Apply (goal_valid (execute_omega t) (omega_valid t) env l H).
Save.


Theorem append_goal :
  (e: (list Z)) (l1,l2:lhyps)
     (interp_list_goal e l1) /\ (interp_list_goal e l2) ->
     (interp_list_goal e (app l1 l2)).

Intros e; Induction l1; [
  Simpl; Intros l2 (H1, H2); Assumption
| Simpl; Intros h1 t1 HR l2 ((H1 , H2), H3) ; Split; Auto].


Save.

