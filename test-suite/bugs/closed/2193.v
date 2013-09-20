(* Computation of dependencies in the "match" return predicate was incomplete *)
(* Submitted by R. O'Connor, Nov 2009 *)

Inductive Symbol : Set :=
 | VAR : Symbol.

Inductive SExpression :=
 | atomic : Symbol -> SExpression.

Inductive ProperExpr : SExpression -> SExpression -> Type :=
 | pe_3 : forall (x : Symbol) (alpha : SExpression),
    ProperExpr alpha (atomic VAR) ->
    ProperExpr (atomic x) alpha.

Definition A (P : forall s : SExpression, Type)
 (x alpha alpha1 : SExpression)
 (t : ProperExpr (x) alpha1) : option (x = atomic VAR) :=
 match t as pe in ProperExpr a b return option (a = atomic VAR) with
 | pe_3 x0 alpha3 tye' => 
      (fun (x:Symbol) (alpha : SExpression) => @None (atomic x = atomic VAR))
       x0 alpha3
 end.

Definition B (P : forall s : SExpression, Type)
 (x alpha alpha1 : SExpression)
 (t : ProperExpr (x) alpha1) : option (x = atomic VAR) :=
 match t as pe in ProperExpr a b return option (a = atomic VAR) with
 | pe_3 x0 alpha3 tye' => 
      (fun (x:Symbol) (alpha : SExpression) (t:ProperExpr alpha (atomic VAR)) => @None (atomic x = atomic VAR))
       x0 alpha3 tye'
 end.
