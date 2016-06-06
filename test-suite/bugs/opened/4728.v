(*I'd like the final [Check] in the following to work:*)

Ltac fin_eta_expand :=
  [ > lazymatch goal with
      | [ H : _ |- _ ] => clear H
      end..
  | lazymatch goal with
    | [ H : ?T |- ?T ]
      => exact H
    | [ |- ?G ]
      => fail 0 "No hypothesis matching" G
    end ];
  let n := numgoals in
  tryif constr_eq numgoals 0
  then idtac
  else fin_eta_expand.

Ltac pre_eta_expand x :=
  let T := type of x in
  let G := match goal with |- ?G => G end in
  unify T G;
  unshelve econstructor;
  destruct x;
  fin_eta_expand.

Ltac eta_expand x :=
  let v := constr:(ltac:(pre_eta_expand x)) in
  idtac v;
  let v := (eval cbv beta iota zeta in v) in
  exact v.

Notation eta_expand x := (ltac:(eta_expand x)) (only parsing).

Ltac partial_unify eqn :=
  lazymatch eqn with
  | ?x = ?x => idtac
  | ?f ?x = ?g ?y
    => partial_unify (f = g);
       (tryif unify x y then
           idtac
         else tryif has_evar x then
             unify x y
           else tryif has_evar y then
               unify x y
             else
               idtac)
  | ?x = ?y
    => idtac;
       (tryif unify x y then
           idtac
         else tryif has_evar x then
             unify x y
           else tryif has_evar y then
               unify x y
             else
               idtac)
  end.

Tactic Notation "{" open_constr(old_record) "with" open_constr(new_record) "}" :=
  let old_record' := eta_expand old_record in
  partial_unify (old_record = new_record);
  eexact new_record.

Set Implicit Arguments.
Record prod A B := pair { fst : A ; snd : B }.
Infix "*" := prod : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Notation "{ old 'with' new }" := (ltac:({ old with new })) (only parsing).

Check ltac:({ (1, 1) with {| snd := 2 |} }).
Fail Check { (1, 1) with {| snd := 2 |} }. (* Error: Cannot infer this placeholder of type "Type"; should succeed *)
