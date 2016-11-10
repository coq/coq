Module Backtracking.

  Class A := { foo : nat }.
  
  Instance A_1 : A | 2 := { foo := 42 }.
  Instance A_0 : A | 1 := { foo := 0 }.
  Lemma aeq (a : A) : foo = foo.
    reflexivity.
  Qed.
  (** Declare [eq] as a class so that typeclass resolution considers it *)
  Existing Class eq.
  
  (** A_0 has priority, but its foo field is not equal to 42 *)
  Arguments foo A : clear implicits.
  Example find42 : exists n, n = 42.
  Proof.
    eexists. etransitivity.
    (** [notypeclasses refine] does not run typeclass resolution, so we can 
          see what typeclass constraints are necessary. 
          ?[a] declares an evar a of type A *)
    notypeclasses refine (@aeq ?[a]).
    (** We find A_0 *)
    typeclasses eauto.
    (** This can't work as [foo A_0 = 0] *)
    Fail reflexivity. 
    Undo 2.
    (* Without multiple successes it fails as it finds A_0 again but cannot backtrack on it
         ([once] prevents backtracking) *)
    Set Typeclasses Debug.
    Fail all:((once (typeclasses eauto))
              + apply eq_refl).
    (* It does backtrack if other goals fail *)
    all:[> typeclasses eauto + reflexivity .. ].
    Show Proof.  
  Qed.
  
  Hint Extern 0 (_ = _) => reflexivity : equality.
  
  Goal exists n, n = 42.
    eexists. etransitivity.
    notypeclasses refine (@aeq ?[a]).
    typeclasses eauto.
    Fail reflexivity.
    Undo 2.
    
    (* Does backtrack between individual goals *)
    Set Typeclasses Debug.
    all:(typeclasses eauto with typeclass_instances equality).
  Qed.
  
  Unset Typeclasses Debug.
  
End Backtracking.

Module HintCut.
  (** Hint Cuts *)
  
  Hint Resolve 100 eq_sym eq_trans : core.
  Goal forall x y z : nat, x = y -> z = y -> x = z.
  Proof.
    intros.
    Fail Timeout 1 typeclasses eauto with core.
  Abort.
  
  (** These proof search paths are automatically discarded *)
  Hint Cut [(_)* eq_sym eq_sym] : core.
  Hint Cut [_* eq_trans eq_trans] : core.
  Hint Cut [_* eq_trans eq_sym eq_trans] : core.
  
  Goal forall x y z : nat, x = y -> z = y -> x = z.
  Proof.
    intros.
    typeclasses eauto with core.
  Qed.
  
  (** Useful for hierarchies *)
  Module Hierarchies.
    
    Class A := mkA { data : nat }.
    Class B := mkB { aofb :> A }.
    
    Existing Instance mkB.
    
    Definition makeB (a : A) : B := _.
    Definition makeA (a : B) : A := _.
    
    Fail Timeout 1 Definition makeA' : A := _.
    
    (** Both the constructor and the projections can be declared as instances
          without leading to divergence *)
    Hint Cut [_* mkB aofb] : typeclass_instances.
    Fail Definition makeA' : A := _.
    Fail Definition makeB' : B := _.
  End Hierarchies.
End HintCut.

Module HintModes.
  (** Hint modes *)
  
  Class Equality (A : Type) := { eqp : A -> A -> Prop }.
  
  Check (eqp 0%nat 0).
  
  Instance nat_equality : Equality nat := { eqp := eq }.
  
  Instance default_equality A : Equality A | 1000 :=
    { eqp := eq }.
  
  Check (eqp 0%nat 0).
  
  (* Defaulting *)
  Check (fun x y => eqp x y).
  (* No more defaulting, reduce "trigger-happiness" *)
  Definition ambiguous x y := eqp x y.
  
  (** This says that to start resolution for an Equality t constraint,
        t's head must _not_ be an evar *)
  Hint Mode Equality ! : typeclass_instances.
  Fail Definition ambiguous' x y := eqp x y.
  Definition nonambiguous (x y : nat) := eqp x y.
  
  (** Typical looping instances with defaulting: *)
  Definition flip {A B C} (f : A -> B -> C) := fun x y => f y x.
  
  Class SomeProp {A : Type} (f : A -> A -> A) :=
    { prf : forall x y, f x y = f x y }.
  
  (** This is dangerous as [flip f] is unifiable with an evar or even
      a term with a deep evar. *)
  Instance propflip (A : Type) (f : A -> A -> A) :
    SomeProp f -> SomeProp (flip f).
  Proof.
    intros []. constructor. reflexivity.
  Qed.
  
  (** This applies propflip indefinitely *)
  Fail Timeout 1 Check prf.
  
  (** Now we ask for the indexes of the typeclass to be evar free to
      trigger resolution *)
  Hint Mode SomeProp + + : typeclass_instances.
  
  (** No resolution done *)
  Check prf.
  (** We have enough info to trigger propflip *)
  Check (fun H : SomeProp plus => _ : SomeProp (flip plus)).
End HintModes.

(** Iterative deepening / breadth-first search *)

Module IterativeDeepening.
  
  Class A := {}.
  Class B := {}.
  Class C := {}.
  
  Instance: B -> A | 0 := {}.
  Instance: C -> A | 0 := {}.
  Instance: C -> B -> A | 0 := {}.
  Instance: A -> A | 0 := {}.
  
  Goal C -> A.
    intros.
    (** This diverges in depth-first search *)
    Fail Timeout 1 typeclasses eauto.
    (** In breadth-first search (implemented by iterative deepening) *)
    (** It fails at depth 1 *)
    Fail typeclasses eauto bfs 1 with typeclass_instances.
    (** Succeeds at depth 2 *)
    typeclasses eauto bfs 2 with typeclass_instances.
    Undo.
    (** Or any other depth *)
    typeclasses eauto bfs with typeclass_instances.
  Qed.
  
End IterativeDeepening.

Module FilteredUnification.

  (* No conversion on let-bound variables and constants in pred (the default) *)
  
  Parameter pred : nat -> Prop.
  Parameter pred0 : pred 0.
  Parameter f : nat -> nat.
  Parameter predf : forall n, pred n -> pred (f n).
  
  Hint Resolve pred0 | 1 (pred _) : pred.
  Hint Resolve predf | 0 : pred.
  
  (* Allow full conversion on let-bound variables and constants *)
  Create HintDb predconv discriminated.
  Hint Resolve pred0 | 1 (pred _) : predconv.
  Hint Resolve predf | 0 : predconv.
  
  Goal exists n, pred n.
    eexists.
    Fail Timeout 1 typeclasses eauto with pred.
    Set Typeclasses Filtered Unification.
    Set Typeclasses Debug Verbosity 2.
    (* predf is not tried as it doesn't match the goal *)
    typeclasses eauto with pred.
  Qed.
  
  Parameter predconv : forall n, pred n -> pred (0 + S n).
  
  (* The inferred pattern contains 0 + ?n, syntactic match will fail to see convertible
     terms *)
  Hint Resolve pred0 : pred2.
  Hint Resolve predconv : pred2.
  
  (** In this database we allow predconv to apply to pred (S _) goals, more generally
    than the inferred pattern (pred (0 + S _)). *)
  Create HintDb pred2conv discriminated.
  Hint Resolve pred0 : pred2conv.
  Hint Resolve predconv | 1 (pred (S _)) : pred2conv.
  
  Goal pred 3.
    Fail typeclasses eauto with pred2.
    typeclasses eauto with pred2conv.
  Abort.
  
  Set Typeclasses Filtered Unification.
  Set Typeclasses Debug Verbosity 2.
  Hint Resolve predconv | 1 (pred _) : pred.
  Hint Resolve predconv | 1 (pred (S _)) : predconv.
  Test Typeclasses Limit Intros.
  Goal pred 3.
    (* predf is not tried as it doesn't match the goal *)
    (* predconv is tried but fails as the transparent state doesn't allow
     unfolding + *)
    Fail typeclasses eauto with pred.
    (* Here predconv succeeds as it matches (pred (S _)) and then
       full unification is allowed *)
    typeclasses eauto with predconv.
  Qed.
  
  (** The other way around: goal contains redexes instead of instances *)
  Goal exists n, pred (0 + n).
    eexists.
    (* predf is applied indefinitely *)
    Fail Timeout 1 typeclasses eauto with pred.
    (* pred0 (pred _) matches the goal *)
    typeclasses eauto with predconv.
  Qed.
  
End FilteredUnification.
