(* Check that "inversion as" manages names as expected *)
Inductive type: Set
   := | int: type
      | pointer: type -> type.
Print type.

Parameter value_set
   : type -> Set.

Parameter string : Set.

Parameter Z : Set.

Inductive lvalue (t: type): Set
   := | var: string -> lvalue t (* name of the variable *)
      | lvalue_loc: Z -> lvalue t (* address of the variable *)
      | deref_l: lvalue (pointer t) -> lvalue t (* deref an lvalue ptr *)
      | deref_r: rvalue (pointer t) -> lvalue t (* deref an rvalue ptr *)
with rvalue (t: type): Set
   := | value_of: lvalue t -> rvalue t (* variable as value *)
      | mk_rvalue: value_set t -> rvalue t. (* literal value *)
Print lvalue.

Inductive statement: Set
   := | void_stat: statement
      | var_loc: (* to be destucted at end of scope *)
           forall (t: type) (n: string) (loc: Z), statement
      | var_ref: (* not to be destructed *)
           forall (t: type) (n: string) (loc: Z), statement
      | var_def: (* var def as typed in code *)
           forall (t:type) (n: string) (val: rvalue t), statement
      | assign:
           forall (t: type) (var: lvalue t) (val: rvalue t), statement
      | group:
           forall (l: list statement), statement
      | fun_def:
           forall (s: string) (l: list statement), statement
      | param_decl:
           forall (t: type) (n: string), statement
      | delete:
           forall a: Z, statement.

Inductive expr: Set
:= | statement_to_expr: statement -> expr
   | lvalue_to_expr: forall t: type, lvalue t -> expr
   | rvalue_to_expr: forall t: type, rvalue t -> expr.

Inductive executable_prim_expr: expr -> Set
:=
(* statements *)
   | var_def_primitive:
        forall (t: type) (n: string) (loc: Z),
        executable_prim_expr
           (statement_to_expr
               (var_def t n
                   (value_of t (lvalue_loc t loc))))
   | assign_primitive:
        forall (t: type) (loc1 loc2: Z),
        executable_prim_expr
           (statement_to_expr
               (assign t (lvalue_loc t loc1)
                   (value_of t (lvalue_loc t loc2))))
(* rvalue *)
   | mk_rvalue_primitive:
        forall (t: type) (v: value_set t),
        executable_prim_expr
           (rvalue_to_expr t (mk_rvalue t v))
(* lvalue *)
   (* var *)
   | var_primitive:
        forall (t: type) (n: string),
        executable_prim_expr (lvalue_to_expr t (var t n))
   (* deref_l *)
   | deref_l_primitive:
        forall (t: type) (loc: Z),
        executable_prim_expr
           (lvalue_to_expr t
               (deref_l t (lvalue_loc (pointer t) loc)))
   (* deref_r *)
   | deref_r_primitive:
        forall (t: type) (loc: Z),
        executable_prim_expr
           (lvalue_to_expr t
               (deref_r t
                   (value_of (pointer t)
                       (lvalue_loc (pointer t) loc)))).

Inductive executable_sub_expr: expr -> Set
:= | executable_sub_expr_prim:
        forall e: expr,
        executable_prim_expr e ->
        executable_sub_expr e
(* statements *)
   | var_def_sub_rvalue:
        forall (t: type) (n: string) (rv: rvalue t),
        executable_sub_expr (rvalue_to_expr t rv) ->
        executable_sub_expr (statement_to_expr (var_def t n rv))
   | assign_sub_lvalue:
        forall (t: type) (lv: lvalue t) (rv: rvalue t),
        executable_sub_expr (lvalue_to_expr t lv) ->
        executable_sub_expr (statement_to_expr (assign t lv rv))
   | assign_sub_rvalue:
        forall (t: type) (lv: lvalue t) (rv: rvalue t),
        executable_sub_expr (rvalue_to_expr t rv) ->
        executable_sub_expr (statement_to_expr (assign t lv rv))
(* rvalue *)
   | value_of_sub_lvalue:
        forall (t: type) (lv: lvalue t),
        executable_sub_expr (lvalue_to_expr t lv) ->
        executable_sub_expr (rvalue_to_expr t (value_of t lv))
(* lvalue *)
   | deref_l_sub_lvalue:
        forall (t: type) (lv: lvalue (pointer t)),
        executable_sub_expr (lvalue_to_expr (pointer t) lv) ->
        executable_sub_expr (lvalue_to_expr t (deref_l t lv))
   | deref_r_sub_rvalue:
        forall (t: type) (rv: rvalue (pointer t)),
        executable_sub_expr (rvalue_to_expr (pointer t) rv) ->
        executable_sub_expr (lvalue_to_expr t (deref_r t rv)).

Inductive expr_kind: Set
:= | statement_kind: expr_kind
   | lvalue_kind: type -> expr_kind
   | rvalue_kind: type -> expr_kind.

Definition expr_to_kind: expr -> expr_kind.
intro e.
destruct e.
exact statement_kind.
exact (lvalue_kind t).
exact (rvalue_kind t).
Defined.

Inductive def_sub_expr_subs:
   forall e: expr,
   forall ee: executable_sub_expr e,
   forall ee': expr,
   forall e': expr,
   Prop
:= | def_sub_expr_subs_prim:
        forall e: expr,
        forall p: executable_prim_expr e,
        forall ee': expr,
        expr_to_kind e = expr_to_kind ee' ->
        def_sub_expr_subs e (executable_sub_expr_prim e p) ee' ee'
   | def_sub_expr_subs_var_def_sub_rvalue:
        forall (t: type) (n: string),
        forall rv rv': rvalue t,
        forall ee': expr,
        forall se_rv: executable_sub_expr (rvalue_to_expr t rv),
        def_sub_expr_subs (rvalue_to_expr t rv) se_rv ee'
           (rvalue_to_expr t rv') ->
        def_sub_expr_subs
           (statement_to_expr (var_def t n rv))
           (var_def_sub_rvalue t n rv se_rv)
           ee'
           (statement_to_expr (var_def t n rv'))
   | def_sub_expr_subs_assign_sub_lvalue:
        forall t: type,
        forall lv lv': lvalue t,
        forall rv: rvalue t,
        forall ee': expr,
        forall se_lv: executable_sub_expr (lvalue_to_expr t lv),
        def_sub_expr_subs (lvalue_to_expr t lv) se_lv ee'
           (lvalue_to_expr t lv') ->
        def_sub_expr_subs
           (statement_to_expr (assign t lv rv))
           (assign_sub_lvalue t lv rv se_lv)
           ee'
           (statement_to_expr (assign t lv' rv))
   | def_sub_expr_subs_assign_sub_rvalue:
        forall t: type,
        forall lv: lvalue t,
        forall rv rv': rvalue t,
        forall ee': expr,
        forall se_rv: executable_sub_expr (rvalue_to_expr t rv),
        def_sub_expr_subs (rvalue_to_expr t rv) se_rv ee'
           (rvalue_to_expr t rv') ->
        def_sub_expr_subs
           (statement_to_expr (assign t lv rv))
           (assign_sub_rvalue t lv rv se_rv)
           ee'
           (statement_to_expr (assign t lv rv'))
   | def_sub_expr_subs_value_of_sub_lvalue:
        forall t: type,
        forall lv lv': lvalue t,
        forall ee': expr,
        forall se_lv: executable_sub_expr (lvalue_to_expr t lv),
        def_sub_expr_subs (lvalue_to_expr t lv) se_lv ee'
           (lvalue_to_expr t lv') ->
        def_sub_expr_subs
           (rvalue_to_expr t (value_of t lv))
           (value_of_sub_lvalue t lv se_lv)
           ee'
           (rvalue_to_expr t (value_of t lv'))
   | def_sub_expr_subs_deref_l_sub_lvalue:
        forall t: type,
        forall lv lv': lvalue (pointer t),
        forall ee': expr,
        forall se_lv: executable_sub_expr (lvalue_to_expr (pointer t) lv),
        def_sub_expr_subs (lvalue_to_expr (pointer t) lv) se_lv ee'
           (lvalue_to_expr (pointer t) lv') ->
        def_sub_expr_subs
           (lvalue_to_expr t (deref_l t lv))
           (deref_l_sub_lvalue t lv se_lv)
           ee'
           (lvalue_to_expr t (deref_l t lv'))
   | def_sub_expr_subs_deref_r_sub_rvalue:
        forall t: type,
        forall rv rv': rvalue (pointer t),
        forall ee': expr,
        forall se_rv: executable_sub_expr (rvalue_to_expr (pointer t) rv),
        def_sub_expr_subs (rvalue_to_expr (pointer t) rv) se_rv ee'
           (rvalue_to_expr (pointer t) rv') ->
        def_sub_expr_subs
           (lvalue_to_expr t (deref_r t rv))
           (deref_r_sub_rvalue t rv se_rv)
           ee'
           (lvalue_to_expr t (deref_r t rv')).

Lemma type_dec: forall t t': type, {t = t'} + {t <> t'}.
Proof.
intros t.
induction t as [|t IH].
destruct t'.
tauto.
right.
discriminate.
destruct t'.
right.
discriminate.
destruct (IH t') as [H|H].
left.
f_equal.
tauto.
right.
injection.
tauto.
Qed.
Check type_dec.

Definition sigT_get_proof:
   forall T: Type,
   forall eq_dec_T: forall t t': T, {t = t'} + {~ t = t'},
   forall P: T -> Type,
   forall t: T,
   P t ->
   sigT P ->
      P t.
intros T eq_dec_T P t H1 H2.
destruct H2 as [t' H2].
destruct (eq_dec_T t t') as [H3|H3].
rewrite H3.
exact H2.
exact H1.
Defined.

Axiom sigT_get_proof_existT_same:
   forall T: Type,
   forall eq_dec_T: forall t t': T, {t = t'} + {~ t = t'},
   forall P: T -> Type,
   forall t: T,
   forall H1 H2: P t,
   sigT_get_proof T eq_dec_T P t H1 (existT P t H2) = H2.

Theorem existT_injective:
   forall T,
   (forall t1 t2: T, { t1 = t2 } + { t1 <> t2 }) ->
   forall P: T -> Type,
   forall t: T,
   forall pt1 pt2: P t,
   existT P t pt1 = existT P t pt2 ->
   pt1 = pt2.
Proof.
intros T T_dec P t pt1 pt2 H1.
pose (H2 := f_equal (sigT_get_proof T T_dec P t pt1) H1).
repeat rewrite sigT_get_proof_existT_same in H2.
assumption.
Qed.

Ltac decide_equality_sub dec x x' H :=
   destruct (dec x x') as [H|H];
   [subst x'; try tauto|try(right; injection; tauto; fail)].

Axiom value_set_dec:
   forall t: type,
   forall v v': value_set t,
      {v = v'} + {v <> v'}.

Theorem lvalue_dec:
   forall (t: type) (l l': lvalue t), {l = l'} + {l <> l'}
with rvalue_dec:
   forall (t: type) (r r': rvalue t), {r = r'} + {r <> r'}.
Admitted.

Theorem sub_expr_subs_same_kind:
   forall e: expr,
   forall ee: executable_sub_expr e,
   forall ee': expr,
   forall e': expr,
   def_sub_expr_subs e ee ee' e' ->
   expr_to_kind e = expr_to_kind e'.
Proof.
intros e ee ee' e' H1.
case H1; try (intros; tauto; fail).
Qed.

Theorem def_sub_expr_subs_assign_sub_lvalue_inversion:
   forall t: type,
   forall lv: lvalue t,
   forall rv: rvalue t,
   forall ee' e': expr,
   forall ee_sub: executable_sub_expr (lvalue_to_expr t lv),
   def_sub_expr_subs (statement_to_expr (assign t lv rv))
      (assign_sub_lvalue t lv rv ee_sub) ee' e' ->
   { lv': lvalue t
   | def_sub_expr_subs (lvalue_to_expr t lv) ee_sub ee'
        (lvalue_to_expr t lv')
   & e' = statement_to_expr (assign t lv' rv) }.
Proof.
intros t lv rv ee' [s'|t' lv''|t' rv''] ee_sub H1;
   try discriminate (sub_expr_subs_same_kind _ _ _ _ H1).
destruct s' as [| | | |t' lv'' rv''| | | |];
   try(assert (H2: False); [inversion H1|elim H2]; fail).
destruct (type_dec t t') as [H2|H2];
   [|assert (H3: False);
     [|elim H3; fail]].
2: inversion H1 as [];tauto.
subst t'.
exists lv''.
 inversion H1 as
   [| |t' lv''' lv'''' rv''' ee'' ee_sub' H2 (H3_1,H3_2,H3_3) (H4_1,H4_2,H4_3,H4_4,H4_5) H5 (H6_1,H6_2)| | | |].
(* Check that all names are the given ones: *)
clear t' lv''' lv'''' rv''' ee'' ee_sub' H2 H3_1 H3_2 H3_3 H4_1 H4_2 H4_3 H4_4 H4_5 H5 H6_1 H6_2.
