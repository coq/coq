(* This used to fail in Coq version 8.1 beta due to a non variable
   universe (issued by template polymorphism) being sent by
   pretyping to the kernel (bug #1182) *)

Variable T : Type.
Variable x : nat*nat.

Check let (_, _) := x in sigT (fun _ : T => nat).

(* This used to raise an anomaly in V8.4, up to pl2 *)

Goal {x: nat & x=x}.
Fail exists (fun x =>
        match
          projT2 (projT2 x) as e in (_ = y)
          return _ = existT _ (projT1 x) (existT _ y e)
        with
        | eq_refl => eq_refl
        end).
