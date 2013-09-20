Inductive IFExpr : Set :=
  | Var : nat -> IFExpr
  | Tr : IFExpr
  | Fa : IFExpr
  | IfE : IFExpr -> IFExpr -> IFExpr -> IFExpr.

Fail Type
  (fun F : IFExpr =>
   match F return Prop with
   | IfE (Var _) H I => True
   | IfE _ _ _ => False
   | _ => True
   end).
