(* A slight shortening of bug 6078 *)

(* This bug exposed a different behavior of unshelve_unifiable
   depending on which projection is found in the unification
   heuristics *)

Axiom flat_type : Type.
Axiom interp_flat_type : flat_type -> Type.
Inductive type := Arrow (_ _ : flat_type).
Definition interp_type (t : type)
  := interp_flat_type (match t with Arrow s d => s end)
     -> interp_flat_type (match t with Arrow s d => d end).
Axiom Expr : type -> Type.
Axiom Interp : forall {t : type}, Expr t -> interp_type t.
Axiom Wf : forall {t}, Expr t -> Prop.
Axiom a : forall f, interp_flat_type f.

Definition packaged_expr_functionP A :=
  (fun F : Expr A -> Expr A
   => forall e' v, Interp (F e') v = a (let (_,f) := A in f)).
Goal forall (f f0 : flat_type)
            (e : forall _ : Expr (@Arrow f f0),
                Expr (@Arrow f f0)),
    @packaged_expr_functionP (@Arrow f f0) e.
  intros.
  refine (fun (e0 : Expr (Arrow f f0))
   => (fun zHwf':True =>
   (fun v : interp_flat_type f =>
      ?[G] : ?[U] = ?[V] :> interp_flat_type ?[v])) ?[H]);
   [ | ].
   (* Was: Error: Tactic failure: Incorrect number of goals (expected 3 tactics). *)
Abort.
