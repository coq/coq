(* Check compilation of multiple pattern-matching on terms non
   apparently of inductive type *)

(* Check that the non dependency in y is OK both in V7 and V8 *)
Check ([x;y:Prop;z]<[x][z]x=x \/ z=z>Cases x y z of
           | O y z' => (or_introl ? (z'=z') (refl_equal ? O))
           | _ y O => (or_intror ?? (refl_equal ? O))
           | x y _ => (or_introl ?? (refl_equal ? x))
           end).

(* Suggested by Pierre Letouzey (PR#207) *)
Inductive Boite : Set := 
  boite : (b:bool)(if b then nat else nat*nat)->Boite. 

Definition test := [B:Boite]<nat>Cases B of 
  (boite true n) => n 
| (boite false (n,m)) => (plus n m)
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
