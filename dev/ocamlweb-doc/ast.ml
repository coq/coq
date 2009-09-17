
type constr_ast =
  Pair of constr_ast * constr_ast
| Prod of binder list * constr_ast
| Lambda of binder list * constr_ast
| Let of string * constr_ast * constr_ast
| LetCase of binder list * constr_ast * constr_ast
| IfCase of constr_ast * constr_ast * constr_ast
| Eval of red_fun * constr_ast
| Infix of string * constr_ast * constr_ast
| Prefix of string * constr_ast
| Postfix of string * constr_ast
| Appl of constr_ast * constr_arg list
| ApplExpl of string list * constr_ast list
| Scope of string * constr_ast
| Qualid of string list
| Prop | Set | Type
| Int of string
| Hole
| Meta of string
| Fixp of fix_kind *
      (string * binder list * constr_ast * string option * constr_ast) list *
      string
| Match of case_item list * constr_ast option *
           (pattern list * constr_ast) list

and red_fun = Simpl

and binder = string * constr_ast

and constr_arg = string option * constr_ast

and fix_kind = Fix | CoFix

and case_item = constr_ast * (string option * constr_ast option)

and pattern =
  PatAs of pattern * string
| PatType of pattern * constr_ast
| PatConstr of string * pattern list
| PatVar of string

let mk_cast c t =
  if t=Hole then c else Infix(":",c,t)

let mk_lambda bl t =
  if bl=[] then t else Lambda(bl,t)
