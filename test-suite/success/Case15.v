(* Check compilation of multiple pattern-matching on terms non
   apparently of inductive type *)

(* Check that the non dependency in y is OK both in V7 and V8 *)
Check
  (fun x (y : Prop) z =>
   match x, y, z return (x = x \/ z = z) with
   | O, y, z' => or_introl (z' = z') (refl_equal 0)
   | _, y, O => or_intror _ (refl_equal 0)
   | x, y, _ => or_introl _ (refl_equal x)
   end).

(* Suggested by Pierre Letouzey (PR#207) *)
Inductive Boite : Set :=
    boite : forall b : bool, (if b then nat else (nat * nat)%type) -> Boite.

Definition test (B : Boite) :=
  match B return nat with
  | boite true n => n
  | boite false (n, m) => n + m
  end.

(* Check lazyness of compilation ... future work
Inductive I : Set := c : (b:bool)(if b then bool else nat)->I.

Check [x]
  Cases x of
    (c (true as y) (true as x)) => (if x then y else true)
  | (c false O) => true | _ => false
  end.

Check [x]
  Cases x of
    (c true true) => true
  | (c false O) => true
  | _ => false
  end.

(* Devrait produire ceci mais trouver le type intermediaire est coton ! *)
Check
  [x:I]
   Cases x of
     (c b y) =>
      (<[b:bool](if b then bool else nat)->bool>if b
       then [y](if y then true else false)
       else [y]Cases y of
              O => true
            | (S _) => false
            end y)
   end.
*)
