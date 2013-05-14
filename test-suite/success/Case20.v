(* Example taken from RelationAlgebra *)
(* Was failing from r16205 up to now *)

Require Import BinNums.

Section A.

Context (A:Type) {X: A} (tst:A->Type) (top:forall X, X).

Inductive v: (positive -> A) -> Type :=
| v_L: forall f', v f'
| v_N: forall f', 
  v (fun n => f' (xO n)) -> 
  (positive -> tst (f' xH)) -> 
  v (fun n => f' (xI n)) -> v f'.

Fixpoint v_add f' (t: v f') n: (positive -> tst (f' n)) -> v f' :=
  match t in (v o) return ((positive -> (tst (o n))) -> v o) with
    | v_L f' => 
        match n return ((positive ->  (tst (f' n))) -> v f') with
        | xH => fun x => v_N _ (v_L _) x (v_L _)
        | xO n => fun x => v_N _ 
          (v_add (fun n => f' (xO n)) (v_L _) n x) (fun _ => top _) (v_L _)
        | xI n => fun x => v_N _ 
          (v_L _) (fun _ => top _) (v_add (fun n => f' (xI n)) (v_L _) n x)
        end
    | v_N f' l y r => 
        match n with
        | xH => fun x => v_N _ l x r
        | xO n => fun x => v_N _ (v_add (fun n => f' (xO n)) l n x) y r
        | xI n => fun x => v_N _ l y (v_add (fun n => f' (xI n)) r n x)
        end
    end.

End A.
