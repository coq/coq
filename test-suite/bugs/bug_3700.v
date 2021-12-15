
Set Implicit Arguments.
Module NonPrim.
  Unset Primitive Projections.
  Record prod A B := pair { fst : A ; snd : B }.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Record prod A B := pair { fst : A ; snd : B }.
End Prim.
Goal (forall x : NonPrim.prod Set Set, let (a, b) := x in a = a)
/\ (forall x : Prim.prod Set Set, let (a, b) := x in a = a).
  Show. (* (forall x : NonPrim.prod Set Set, let (a, _) := x in a = a) /\
   (forall x : Prim.prod Set Set,
    let a := Prim.fst x in let b := Prim.snd x in a = a) *)
  Set Printing All.
  Show. (* and
     (forall x : NonPrim.prod Set Set,
      match x return Prop with
      | NonPrim.pair a _ => @eq Set a a
      end)
     (forall x : Prim.prod Set Set,
      let a := @Prim.fst Set Set x in
      let b := @Prim.snd Set Set x in @eq Set a a) *)
  Unset Printing All.
Abort.
Goal (forall x : NonPrim.prod Set Set, match x with NonPrim.pair a b => a = a end)
/\ (forall x : Prim.prod Set Set, match x with Prim.pair a b => a = a end).
  Show. (* (forall x : NonPrim.prod Set Set,
    match x with
    | {| NonPrim.fst := a |} => a = a
    end) /\ (forall x : Prim.prod Set Set, Prim.fst x = Prim.fst x) *)
  (** Wrong: [match] should generate unfolded things *)
  Set Printing All.
  Show. (* and
     (forall x : NonPrim.prod Set Set,
      match x return Prop with
      | NonPrim.pair a _ => @eq Set a a
      end)
     (forall x : Prim.prod Set Set,
      @eq Set (@Prim.fst Set Set x) (@Prim.fst Set Set x)) *)
  Unset Printing All.
Abort.
Goal (forall x : NonPrim.prod Set Set, let (a, b) := x in a = a /\ b = b)
/\ (forall x : Prim.prod Set Set, let (a, b) := x in a = a /\ b = b).
  Show. (* (forall x : NonPrim.prod Set Set, let (a, b) := x in a = a /\ b = b) /\
   (forall x : Prim.prod Set Set,
    let a := Prim.fst x in let b := Prim.snd x in a = a /\ b = b) *)
  (** Understandably different, maybe, but should still be unfolded *)
  Set Printing All.
  Show. (* and
     (forall x : NonPrim.prod Set Set,
      match x return Prop with
      | NonPrim.pair a b => and (@eq Set a a) (@eq Set b b)
      end)
     (forall x : Prim.prod Set Set,
      let a := @Prim.fst Set Set x in
      let b := @Prim.snd Set Set x in and (@eq Set a a) (@eq Set b b)) *)
  Unset Printing All.
Abort.
Goal (forall x : NonPrim.prod Set Set, match x with NonPrim.pair a b => a = a /\ b = b end)
/\ (forall x : Prim.prod Set Set, match x with Prim.pair a b => a = a /\ b = b end).
  Show. (* (forall x : NonPrim.prod Set Set,
    match x with
    | {| NonPrim.fst := a; NonPrim.snd := b |} => a = a /\ b = b
    end) /\
   (forall x : Prim.prod Set Set,
    Prim.fst x = Prim.fst x /\ Prim.snd x = Prim.snd x) *)
  Set Printing All.
  Show.

  set(foo:=forall x : Prim.prod Set Set, match x return Set with
                 | Prim.pair fst _ => fst
                 end).
  (* and
     (forall x : NonPrim.prod Set Set,
      match x return Prop with
      | NonPrim.pair a b => and (@eq Set a a) (@eq Set b b)
      end)
     (forall x : Prim.prod Set Set,
      and (@eq Set (@Prim.fst Set Set x) (@Prim.fst Set Set x))
        (@eq Set (@Prim.snd Set Set x) (@Prim.snd Set Set x))) *)
  Unset Printing All.
Abort.
