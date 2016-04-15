Fixpoint demo_recursion(n:nat) := match n with
                                    |0 => Type
                                    |S k => (demo_recursion k) -> Type
                                    end.

Record Demonstration := mkDemo
{
    demo_law : forall n:nat, demo_recursion n;
    demo_stuff : forall n:nat, forall q:(fix demo_recursion (n : nat) : Type :=
     match n with
     | 0 => Type
     | S k => demo_recursion k -> Type
     end) n, (demo_law (S n)) q
}.

Theorem DemoError : Demonstration.
Fail apply mkDemo. (*Anomaly: Uncaught exception Not_found. Please report.*)
