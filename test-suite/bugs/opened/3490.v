Inductive T : Type :=                                                                                        
| Var : nat -> T                                                                                                 
| Arr : T -> T -> T.                                                                                             

Inductive Tele : list T -> Type :=                                                                               
| Tnil  : @Tele nil                                                                                              
| Tcons : forall ls, forall (t : @Tele ls) (l : T), @Tele (l :: ls). 

Fail Fixpoint TeleD (ls : list T) (t : Tele ls) {struct t}
   : { x : Type & x -> nat -> Type } :=
     match t return { x : Type & x -> nat -> Type } with
       | Tnil => @existT Type (fun x => x -> nat -> Type) unit (fun (_ : unit) (_ : nat) => unit)
       | Tcons ls t' l =>
         let (result, get) := TeleD ls t' in
         @existT Type (fun x => x -> nat -> Type)
                 { v : result & (fix TD (t : T) {struct t} :=
                                   match  t with
                                     | Var n =>
                                       get v n
                                     | Arr a b => TD a -> TD b
                                   end) l }
                 (fun x n =>
                    match n return Type with
                      | 0 => projT2 x
                      | S n => get (projT1 x) n
                    end)
     end.
