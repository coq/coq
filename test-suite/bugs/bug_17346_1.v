Require Import Setoid.

Import Corelib.Classes.Morphisms.
Import Corelib.Relations.Relation_Definitions.

Lemma interp  (base_interp : nat -> Type)  : Type.
Admitted.

Lemma related  {base_interp : nat -> Type} (R : forall t, relation (base_interp t))
  : relation (interp base_interp).
Admitted.

Axiom Forall : forall [A : Type], (A -> Prop) -> list A -> Prop.
Axiom Forall2 : forall [A B : Type], (A -> B -> Prop) -> list A -> list B -> Prop.

Lemma Forall2_Forall {A R ls}
  : @Forall2 A A R ls ls
    <-> @Forall A (Proper R) ls.
Admitted.

Axiom base_interp : nat -> Type.

Lemma foo
  (l' : list (interp base_interp))
  (H : Forall (fun v : interp base_interp => related (fun t : nat => eq) v v) l')
  : True.
  erewrite <- (Forall2_Forall (R:=related (fun _ => eq))) in H.
  exact I.
Qed.
(*
unmodified:
  ((Forall2_Forall (interp ?X22@{__:=?M0; __:=?M0})
      (related ?X22@{__:=?M0; __:=?M0}
         (fun t : nat => eq (?X22@{__:=?M0; __:=?M0} t)))
      ?X25@{__:=?M0; __:=?M0}),
   NoBindings)

in unify_app for the first time
l1 = [|(interp ?X22@{__:=?M0; __:=?M0});
    (Proper (interp ?X22@{__:=?M0; __:=?M0})
       (related ?X22@{__:=?M0; __:=?M0}
          (fun t : nat => eq (?X22@{__:=?M0; __:=?M0} t))));
    ?X25@{__:=?M0; __:=?M0}|]
l2 = [|(interp base_interp);
    (fun v : interp base_interp =>
     related base_interp (fun t : nat => eq (base_interp t)) v v);
    l'|]


modified
((Forall2_Forall ?X21@{__:=?M0; __:=?M0}
      (related ?X22@{__:=?M0; __:=?M0}
         (fun t : nat => eq ?X24@{__:=?M0; __:=?M0; __:=t}))
      ?X25@{__:=?M0; __:=?M0}),
   NoBindings)

unify_app
l1 = [|?X21@{__:=?M0; __:=?M0};
    (Proper ?X21@{__:=?M0; __:=?M0}
       (related ?X22@{__:=?M0; __:=?M0}
          (fun t : nat => eq ?X24@{__:=?M0; __:=?M0; __:=t})));
    ?X25@{__:=?M0; __:=?M0}|]
l2 = [|(interp base_interp);
    (fun v : interp base_interp =>
     related base_interp (fun t : nat => eq (base_interp t)) v v);
    l'|]

   ?X21==[l' H |-  => interp ?base_interp@{l':=l'; H:=H}] (parameter A of
           Forall2_Forall)
   ?X22==[l' H |- ] (parameter base_interp of related) {?base_interp}

(?X22, SList.Default (2, SList.Nil)), base_interp goes into the evarsubst

 *)
