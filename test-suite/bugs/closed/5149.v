Goal forall x x' : nat, x = x' -> S x = S x -> exists y, S y = S x.
intros.
eexists.
rewrite <- H.
eassumption.
Qed.

Goal forall (base_type_code : Type) (t : base_type_code) (flat_type : Type) 
            (t' : flat_type) (exprf interp_flat_type0 interp_flat_type1 : 
flat_type -> Type)
            (v v' : interp_flat_type1 t'),
    v = v' ->
    forall (interpf : forall t0 : flat_type, exprf t0 -> interp_flat_type1 t0)
           (SmartVarVar : forall t0 : flat_type, interp_flat_type1 t0 -> 
interp_flat_type0 t0)
           (Tbase : base_type_code -> flat_type) (x : exprf (Tbase t))
           (x' : interp_flat_type1 (Tbase t)) (T : Type)
           (flatten_binding_list : forall t0 : flat_type,
               interp_flat_type0 t0 -> interp_flat_type1 t0 -> list T)
           (P : T -> list T -> Prop) (prod : Type -> Type -> Type)
           (s : forall x0 : base_type_code, prod (exprf (Tbase x0)) 
(interp_flat_type1 (Tbase x0)) -> T)
           (pair : forall A B : Type, A -> B -> prod A B),
      P (s t (pair (exprf (Tbase t)) (interp_flat_type1 (Tbase t)) x x'))
        (flatten_binding_list t' (SmartVarVar t' v') v) ->
      (forall (t0 : base_type_code) (t'0 : flat_type) (v0 : interp_flat_type1 
t'0)
              (x0 : exprf (Tbase t0)) (x'0 : interp_flat_type1 (Tbase t0)),
          P (s t0 (pair (exprf (Tbase t0)) (interp_flat_type1 (Tbase t0)) x0 
x'0))
            (flatten_binding_list t'0 (SmartVarVar t'0 v0) v0) -> interpf 
(Tbase t0) x0 = x'0) ->
      interpf (Tbase t) x = x'.
Proof.
  intros ?????????????????????? interpf_SmartVarVar.
  solve [ unshelve (subst; eapply interpf_SmartVarVar; eassumption) ] || fail 
"too early".
  Undo.
  (** Implicitely at the dot. The first fails because unshelve adds a goal, and solve hence fails. The second has an ambiant unification problem that is solved after solve *)
  Fail solve [ unshelve (eapply interpf_SmartVarVar; subst; eassumption) ].
  solve [eapply interpf_SmartVarVar; subst; eassumption].
  Undo.
  Unset Solve Unification Constraints.
  (* User control of when constraints are solved *)
  solve [ unshelve (eapply interpf_SmartVarVar; subst; eassumption); solve_constraints ].
Qed.

