Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 2073 lines to 358 lines, then from 359 lines to 218 lines, then from 107 lines to 92 lines *)
(* coqc version trunk (October 2014) compiled on Oct 11 2014 1:13:41 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (d65496f09c4b68fa318783e53f9cd6d5c18e1eb7) *)
Require Coq.Lists.List.

Import Coq.Lists.List.

Set Implicit Arguments.
Global Set Asymmetric Patterns.

Section machine.
  Variables pc state : Type.

  Inductive propX (i := pc) (j := state) : list Type -> Type :=
  | Inj : forall G, Prop -> propX G
  | ExistsX : forall G A, propX (A :: G) -> propX G.

  Arguments Inj [G].

  Definition PropX := propX nil.
  Fixpoint last (G : list Type) : Type.
    exact (match G with
             | nil => unit
             | T :: nil => T
             | _ :: G' => last G'
           end).
  Defined.
  Fixpoint eatLast (G : list Type) : list Type.
    exact (match G with
             | nil => nil
             | _ :: nil => nil
             | x :: G' => x :: eatLast G'
           end).
  Defined.

  Fixpoint subst G (p : propX G) : (last G -> PropX) -> propX (eatLast G) :=
    match p with
      | Inj _ P => fun _ => Inj P
      | ExistsX G A p1 => fun p' =>
                            match G return propX (A :: G) -> propX (eatLast (A :: G)) -> propX (eatLast G) with
                              | nil => fun p1 _ => ExistsX p1
                              | _ :: _ => fun _ rc => ExistsX rc
                            end p1 (subst p1 (match G return (last G -> PropX) -> last (A :: G) -> PropX with
                                                | nil => fun _ _ => Inj True
                                                | _ => fun p' => p'
                                              end p'))
    end.

  Definition spec := state -> PropX.
  Definition codeSpec := pc -> option spec.

  Inductive valid (specs : codeSpec) (G : list PropX) : PropX -> Prop := Env : forall P, In P G -> valid specs G P.
  Definition interp specs := valid specs nil.
End machine.
Notation "'ExX' : A , P" := (ExistsX (A := A) P) (at level 89) : PropX_scope.
Bind Scope PropX_scope with PropX propX.
Variables pc state : Type.

Inductive subs : list Type -> Type :=
| SNil : subs nil
| SCons : forall T Ts, (last (T :: Ts) -> PropX pc state) -> subs (eatLast (T :: Ts)) -> subs (T :: Ts).

Fixpoint SPush G T (s : subs G) (f : T -> PropX pc state) : subs (T :: G) :=
  match s in subs G return subs (T :: G) with
    | SNil => SCons _ nil f SNil
    | SCons T' Ts f' s' => SCons T (T' :: Ts) f' (SPush s' f)
  end.

Fixpoint Substs G (s : subs G) : propX pc state G -> PropX pc state :=
  match s in subs G return propX pc state G -> PropX pc state with
    | SNil => fun p => p
    | SCons _ _ f s' => fun p => Substs s' (subst p f)
  end.
Variable specs : codeSpec pc state.

Lemma simplify_fwd_ExistsX : forall G A s (p : propX pc state (A :: G)),
                               interp specs (Substs s (ExX  : A, p))
                               -> exists a, interp specs (Substs (SPush s a) p).
admit.
Defined.

Goal    forall (G : list Type) (A : Type) (p : propX pc state (@cons Type A G))
               (s : subs G)
               (_ : @interp pc state specs (@Substs G s (@ExistsX pc state G A p)))
               (P : forall _ : subs (@cons Type A G), Prop)
               (_ : forall (s0 : subs (@cons Type A G))
                           (_ : @interp pc state specs (@Substs (@cons Type A G) s0 p)),
                      P s0),
          @ex (forall _ : A, PropX pc state)
              (fun a : forall _ : A, PropX pc state => P (@SPush G A s a)).
  intros ? ? ? ? H ? H'.
  apply simplify_fwd_ExistsX in H.
  firstorder. 
Qed.
 (* Toplevel input, characters 15-19:
Error: Illegal application:
The term "cons" of type "forall A : Type, A -> list A -> list A"
cannot be applied to the terms
 "Type" : "Type"
 "T" : "Type"
 "G0" : "list Type"
The 2nd term has type "Type@{Top.53}" which should be coercible to
 "Type@{Top.12}".
 *)
