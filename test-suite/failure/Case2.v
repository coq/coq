Inductive IFExpr : Set := 
          Var  : nat -> IFExpr
        | Tr   : IFExpr
        | Fa   : IFExpr
        | IfE   : IFExpr -> IFExpr -> IFExpr -> IFExpr.

Type [F:IFExpr]
    <Prop>Cases F of
       (IfE (Var _) H I) => True
     | (IfE _ _ _)   => False
     |  _          => True
     end.

