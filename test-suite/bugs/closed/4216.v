Generalizable Variables T A.

Inductive path `(a: A): A -> Type := idpath: path a a.

Class TMonad (T: Type -> Type) := {
  bind: forall {A B: Type}, (T A) -> (A -> T B) -> T B;
  ret: forall {A: Type}, A -> T A;
  ret_unit_left: forall {A B: Type} (k: A -> T B) (a: A),
                 path (bind (ret a) k) (k a)
  }.

Let T_fzip `{TMonad T} := fun (A B: Type) (f: T (A -> B)) (t: T A)
                  => bind t (fun a => bind f (fun g => ret (g a) )).
Let T_pure `{TMonad T} := @ret _ _.

Let T_pure_id `{TMonad T} {A: Type} (t: A -> A) (x: T A): 
        path (T_fzip A A (T_pure (A -> A) t) x) x.
  unfold T_fzip, T_pure.
  Fail rewrite (ret_unit_left (fun g a => ret (g a)) (fun x => x)).

