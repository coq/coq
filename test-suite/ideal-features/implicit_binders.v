(** * Questions de syntaxe autour de la généralisation implicite

   ** Lieurs de classes
   Aujourd'hui, les lieurs de classe [ ] et les
   lieurs {{ }} sont équivalents et on a toutes les combinaisons de { et ( pour
   les lieurs de classes (où la variable liée peut être anonyme):
   *)

Class Foo (A : Type) := foo : A -> nat.

Definition bar [ Foo A ] (x y : A) := foo x + foo y.

Definition bar₀ {{ Foo A }} (x y : A) := foo x + foo y.

Definition bar₁ {( Foo A )} (x y : A) := foo x + foo y.

Definition bar₂ ({ Foo A }) (x y : A) := foo x + foo y.

Definition bar₃ (( Foo A )) (x y : A) := foo x + foo y.

Definition bar₄ {( F : Foo A )} (x y : A) := foo x + foo y.

(** Les lieurs sont généralisés à tous les termes, pas seulement aux classes: *)

Definition relation A := A -> A -> Prop.

Definition inverse {( R : relation A )} := fun x y => R y x.

(** Autres propositions:
   [Definition inverse ..(R : relation A) := fun x y => R y x] et

   [Definition inverse ..[R : relation A] := fun x y => R y x] ou
   [Definition inverse ..{R : relation A} := fun x y => R y x]
   pour lier [R] implicitement.

   MS: Le .. empêche d'utiliser electric-terminator dans Proof General. Cependant, il existe
   aussi les caractères utf8 ‥ (two dot leader) et … (horizontal ellipsis) qui permettraient
   d'éviter ce souci moyennant l'utilisation d'unicode.

   [Definition inverse _(R : relation A) := fun x y => R y x] et

   [Definition inverse _[R : relation A] := fun x y => R y x] ou
   [Definition inverse _{R : relation A} := fun x y => R y x]

   [Definition inverse `(R : relation A) := fun x y => R y x] et

   [Definition inverse `[R : relation A] := fun x y => R y x] ou
   [Definition inverse `{R : relation A} := fun x y => R y x]


   Toujours avec la possibilité de ne pas donner le nom de la variable:
*)

Definition div (x : nat) ({ y <> 0 }) := 0.

(** Un choix à faire pour les inductifs: accepter ou non de ne pas donner de nom à
   l'argument. Manque de variables anonymes pour l'utilisateur mais pas pour le système... *)

Inductive bla [ Foo A ] : Type :=.

(** *** Les autres syntaxes ne supportent pas de pouvoir spécifier séparément les statuts
   des variables généralisées et celui de la variable liée. Ca peut être utile pour les
   classes où l'on a les cas de figure: *)

(** Trouve [A] et l'instance par unification du type de [x]. *)
Definition allimpl {{ Foo A }} (x : A) : A := x.

(** Trouve l'instance à partir de l'index explicite *)

Class SomeStruct (a : nat) := non_zero : a <> 0.

Definition instimpl ({ SomeStruct a }) : nat := a + a.

(** Donne l'instance explicitement (façon foncteur). *)

Definition foo_prod {( Foo A, Foo B )} : Foo (A * B) :=
  fun x => let (l, r) := x in foo l + foo r.

(** *** Questions:
   - Gardez les crochets [ ] pour {{ }} ?
   - Quelle syntaxe pour la généralisation ?
   - Veut-on toutes les combinaisons de statut pour les variables généralisées et la variable liée ?
   *)

(** ** Constructeur de généralisation implicite

   Permet de faire une généralisation n'importe où dans le terme: on
   utilise un produit ou un lambda suivant le scope (fragile ?).
   *)

Goal `(x + y + z = x + (y + z)).
Admitted.

(** La généralisation donne un statut implicite aux variables si l'on utilise
   `{ }. *)

Definition baz := `{x + y + z = x + (y + z)}.
Print baz.

(** Proposition d'Arthur C.: déclarer les noms de variables généralisables à la [Implicit Types]
   pour plus de robustesse (cela vaudrait aussi pour les lieurs). Les typos du genre de l'exemple suivant
   ne sont plus silencieuses: *)

Check `(foob 0 + x).

(** Utilisé pour généraliser l'implémentation de la généralisation implicite dans
   les déclarations d'instances (i.e. les deux defs suivantes sont équivalentes). *)

Instance fooa : Foo A.
Admitted.
Definition fooa' : `(Foo A).
Admitted.

(** Un peu différent de la généralisation des lieurs qui "explosent" les variables
   libres en les liant au même niveau que l'objet. Dans la deuxième defs [a] n'est pas lié dans
   la définition mais [F : Π a, SomeStruct a]. *)

Definition qux {( F : SomeStruct a )} : nat := a.
Definition qux₁ {( F : `(SomeStruct a) )} : nat := 0.

(** *** Questions
   - Autres propositions de syntaxe ?
   - Réactions sur la construction ?
   *)
