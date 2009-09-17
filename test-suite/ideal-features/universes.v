(* Some issues with polymorphic inductive types *)

(* 1- upper constraints with respect to non polymorphic inductive types *)

Unset Elimination Schemes.
Definition Ty := Type (* Top.1 *).

Inductive Q (A:Type (* Top.2 *)) : Prop := q : A -> Q A.
Inductive T (B:Type (* Top.3 *)) := t : B -> Q (T B) -> T B.
(* ajoute Top.4 <= Top.2 inutilement:
   4 est l'univers utilisé dans le calcul du type polymorphe de T *)
Definition C := T Ty.
(* ajoute Top.1 < Top.3 :
   Top.3 jour le rôle de pivot pour propager les contraintes supérieures qu'on
   a sur l'argument B de T: Top.3 sera réutilisé plus tard comme majorant
   des arguments effectifs de T, propageant à cette occasion les contraintes
   supérieures sur Top.3 *)

(* We need either that Q is polymorphic on A (though it is in Type) or
   that the constraint Top.1 < Top.2 is set (and it is not set!) *)

(* 2- upper constraints with respect to unfoldable constants *)

Definition f (A:Type (* Top.1 *)) := True.
Inductive R := r : f R -> R.
(* ajoute Top.3 <= Top.1 inutilement:
   Top.3 est l'univers utilisé dans le calcul du type polymorphe de R *)

(* mais il manque la contrainte que l'univers de R est plus petit que Top.1
   ce qui l'empêcherait en fait d'être vraiment polymorphe *)

(* 3- constraints with respect to global constants *)

Inductive S (A:Ty) := s : A -> S A.

(* Q est considéré polymorphique vis à vis de A alors que le type de A
   n'est pas une variable mais un univers déjà existant *)

(* Malgré tout la contrainte Ty < Ty est ajoutée (car Ty est vu comme
   un pivot pour propager les contraintes sur le type A, comme si Q était
   vraiment polymorphique, ce qu'il n'est pas parce que Ty est une
   constante). Et heureusement qu'elle est ajouté car elle évite de
   pouvoir typer "Q Ty" *)
