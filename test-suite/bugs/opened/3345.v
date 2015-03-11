Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 1972 lines to 136 lines, then from 119 lines to 105 lines *)
Global Set Implicit Arguments.
Require Import Coq.Lists.List Program.
Section IndexBound.
  Context {A : Set}.
  Class IndexBound (a : A) (Bound : list A) :=
    { ibound :> nat;
      boundi : nth_error Bound ibound = Some a}.
  Global Arguments ibound [a Bound] _ .
  Global Arguments boundi [a Bound] _.
  Record BoundedIndex (Bound : list A) := { bindex :> A; indexb :> IndexBound bindex Bound }.
End IndexBound.
Context {A : Type} {C : Set}.
Variable (projAC : A -> C).
Lemma None_neq_Some
: forall (AnyT AnyT' : Type) (a : AnyT),
    None = Some a -> AnyT'.
  admit.
Defined.
Program Definition nth_Bounded'
           (Bound : list A)
           (c : C)
           (a_opt : option A)
           (nth_n : option_map projAC a_opt = Some c)
: A := match a_opt as x
             return (option_map projAC x = Some c) -> A with
         | Some a => fun _ => a
         | None => fun f : None = Some _ => !
       end nth_n.
Lemma nth_error_map :
  forall n As c_opt,
    nth_error (map projAC As) n = c_opt
    -> option_map projAC (nth_error As n) = c_opt.
  admit.
Defined.
Definition nth_Bounded
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
: A := nth_Bounded' Bound (nth_error Bound (ibound idx))
                    (nth_error_map _ _ (boundi idx)).
Program Definition nth_Bounded_ind2
        (P : forall As, BoundedIndex (map projAC As)
                        -> BoundedIndex (map projAC As)
                        -> A -> A -> Prop)
: forall (Bound : list A)
         (idx : BoundedIndex (map projAC Bound))
         (idx' : BoundedIndex (map projAC Bound)),
    match nth_error Bound (ibound idx), nth_error Bound (ibound idx') with
      | Some a, Some a' => P Bound idx idx' a a'
      | _, _ => True
    end
    -> P Bound idx idx' (nth_Bounded _ idx) (nth_Bounded _ idx'):=
  fun Bound idx idx' =>
    match (nth_error Bound (ibound idx)) as e, (nth_error Bound (ibound idx')) as e'
          return
          (forall (f : option_map _ e = Some (bindex idx))
                  (f' : option_map _ e' = Some (bindex idx')),
             (match e, e' with
                | Some a, Some a' => P Bound idx idx' a a'
                | _, _ => True
              end)
             -> P Bound idx idx'
                  (match e as e'' return
                         option_map _ e'' = Some (bindex idx)
                         -> A
                   with
                     | Some a => fun _ => a
                     | _ => fun f => _
                   end f)
                  (match e' as e'' return
                         option_map _ e'' = Some (bindex idx')
                         -> A
                   with
                     | Some a => fun _ => a
                     | _ => fun f => _
                   end f')) with
      | Some a, Some a' => fun _ _ H => _
      | _, _ => fun f => _
    end (nth_error_map _ _ (boundi idx))
        (nth_error_map _ _ (boundi idx')).

Lemma nth_Bounded_eq
: forall (Bound : list A)
         (idx idx' : BoundedIndex (map projAC Bound)),
    ibound idx = ibound idx'
    -> nth_Bounded Bound idx = nth_Bounded Bound idx'.
Proof.
  intros.
  eapply nth_Bounded_ind2 with (idx := idx) (idx' := idx').
  simpl.
  (* The [case_eq] should not Fail.  More importantly, [Fail case_eq ...] should succeed if [case_eq ...] fails.  It doesn't!!!  So I resort to [Fail Fail try (case_eq ...)]. *)
  Fail Fail try (case_eq (nth_error Bound (ibound idx'))).
(* Toplevel input, characters 15-54:
In nested Ltac calls to "case_eq" and "pattern x at - 1", last call failed.
Error: The abstracted term
"fun e : Exc A =>
 forall e0 : nth_error Bound (ibound idx') = e,
 match
   nth_error Bound (ibound idx) as anonymous'0
   return (anonymous'0 = nth_error Bound (ibound idx) -> e = e -> Prop)
 with
 | Some a =>
     match
       e as anonymous'
       return
         (Some a = nth_error Bound (ibound idx) -> anonymous' = e -> Prop)
     with
     | Some a' =>
         fun (_ : Some a = nth_error Bound (ibound idx)) (_ : Some a' = e) =>
         a = a'
     | None =>
         fun (_ : Some a = nth_error Bound (ibound idx)) (_ : None = e) =>
         True
     end
 | None => fun (_ : None = nth_error Bound (ibound idx)) (_ : e = e) => True
 end eq_refl e0" is not well typed.
Illegal application:
The term
 "match
    nth_error Bound (ibound idx) as anonymous'0
    return (anonymous'0 = nth_error Bound (ibound idx) -> e = e -> Prop)
  with
  | Some a =>
      match
        e as anonymous'
        return
          (Some a = nth_error Bound (ibound idx) -> anonymous' = e -> Prop)
      with
      | Some a' =>
          fun (_ : Some a = nth_error Bound (ibound idx)) (_ : Some a' = e) =>
          a = a'
      | None =>
          fun (_ : Some a = nth_error Bound (ibound idx)) (_ : None = e) =>
          True
      end
  | None => fun (_ : None = nth_error Bound (ibound idx)) (_ : e = e) => True
  end" of type
 "nth_error Bound (ibound idx) = nth_error Bound (ibound idx) ->
  e = e -> Prop"
cannot be applied to the terms
 "eq_refl" : "nth_error Bound (ibound idx) = nth_error Bound (ibound idx)"
 "e0" : "nth_error Bound (ibound idx') = e"
The 2nd term has type "nth_error Bound (ibound idx') = e"
which should be coercible to "e = e". *)
