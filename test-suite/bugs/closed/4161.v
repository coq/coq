
    (* Inductive t : Type -> Type := *)
    (* | Just : forall (A : Type), t A -> t A. *)

    (* Fixpoint test {A : Type} (x : t A) : t (A + unit) := *)
    (*   match x in t A return t (A + unit) with *)
    (*   | Just T x => @test T x *)
    (*   end. *)


    Definition Type1 := Type.
Definition Type2 := Type.
Definition cast (x:Type2) := x:Type1.
Axiom f: Type2 -> Prop.
Definition A :=
 let T := fun A:Type1 => _ in
 fun A':Type2 =>
 eq_refl : T A' = f A' :> Prop.
(* Type2 <= Type1... f A -> Type1 <= Type2 *)

Inductive t : Type -> Type :=
    | Just : forall (A : Type), t A -> t A.

Fixpoint test {A : Type} (x : t A) : t (A + unit) :=
  match x in t A with
  | Just B x => @test B x
  end.
