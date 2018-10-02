(* Examples matching fix/cofix in Ltac pattern-matching *)

Goal True.
lazymatch (eval cbv delta [Nat.add] in Nat.add) with
| (fix F (n : nat) (v : ?A) {struct n} : @?P n v
     := match n with
        | O => @?O_case v
        | S n' => @?S_case n' v F
        end)
    =>
         unify A nat;
         unify P (fun _ _ : nat => nat);
         unify O_case (fun v : nat => v);
         unify S_case (fun (p : nat) (m : nat) (add : nat -> nat -> nat)
                       => S (add p m))
  end.
Abort.

Fixpoint f l n := match n with 0 => 0 | S n => g n (cons n l) end
with g n l := match n with 0 => 1 | S n => f (cons 0 l) n end.

Goal True.

lazymatch (eval cbv delta [f] in f) with
| fix myf (l : ?L) (n : ?N) {struct n} : nat :=
    match n as _ with
    | 0 => ?Z
    | S n0 => @?S myf myg n0 l
    end
  with myg (n' : ?N') (l' : ?L') {struct n'} : nat :=
    match n' as _ with
    | 0 => ?Z'
    | S n0' => @?S' myf myg n0' l'
    end
  for myf =>
    unify L (list nat);
    unify L' (list nat);
    unify N nat;
    unify N' nat;
    unify Z 0;
    unify Z' 1;
    unify S (fun (f : L -> N -> nat) (g : N -> L -> nat) n l => g n (cons n l));
    unify S' (fun (f : L -> N -> nat) (g : N -> L -> nat) (n:N) l => f (cons 0 l) n)
end.

Abort.

CoInductive S1 := C1 : nat -> S2 -> S1 with S2 := C2 : bool -> S1 -> S2.

CoFixpoint f' n l := C1 n (g' (cons n l) n n)
with g' l n p := C2 true (f' (S n) l).

Goal True.

lazymatch (eval cbv delta [f'] in f') with
| cofix myf (n : ?N) (l : ?L) : ?T := @?X n g l
  with g (l' : ?L') (n' : ?N') (p' : ?N'') : ?T' := @?X' n' myf l'
  for myf =>
    unify L (list nat);
    unify L' (list nat);
    unify N nat;
    unify N' nat;
    unify N'' nat;
    unify T S1;
    unify T' S2;
    unify X (fun n g l => C1 n (g (cons n l) n n));
    unify X' (fun n f (l : list nat) => C2 true (f (S n) l))
end.

Abort.
