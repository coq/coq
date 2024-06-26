From Ltac2 Require Import Ltac2 Constr.
Import Constr.Unsafe.

Goal True.
  let t := open_constr:(_ :> False) in
  match kind t with
  | Evar e _ => Control.new_goal e > [refine 'I|]
  | _ => Control.throw Not_found
  end.
  Show Existentials. (* Existential 1 = ?Goal : [ |- False] (shelved) *)
Abort.

Goal True.
  let t := unshelve open_constr:(_ :> False) in
  Control.extend [Control.shelve] (fun () => ()) [];
  match kind t with
  | Evar e _ => Control.new_goal e > [refine 'I|]
  | _ => Control.throw Not_found
  end.
  Show Existentials.
Abort.
