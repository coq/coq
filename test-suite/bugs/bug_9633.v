Declare Custom Entry expr.

Check fun expr => expr.
Check fun constr => constr.
Goal True.
  let x := open_constr:(1+1) in pose x.
  let x := constr:(1+1) in pose x.
Abort.

Module A.
  Notation "'constr' : ( e )" := e (in custom expr, e constr).
  Notation "'expr' : ( e )" := e (e custom expr).

  Check expr:( constr:( 1 )).

  Check fun expr => expr.
  Check fun constr => constr.
  Goal True.
    let x := open_constr:(1+1) in pose x.
    let x := constr:(1+1) in pose x.
  Abort.
End A.

Module B.
  Notation "'expr' : ( e )" := e (e custom expr).
  Notation "'constr' : ( e )" := e (in custom expr, e constr).

  Check expr:( constr:( 1 )).

  Check fun expr => expr.
  Check fun constr => constr.
  Goal True.
    let x := open_constr:(1+1) in pose x.
    let x := constr:(1+1) in pose x.
  Abort.
End B.
