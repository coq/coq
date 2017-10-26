Reserved Notation "'slet' x .. y := A 'in' b"
  (at level 200, x binder, y binder, b at level 200, format "'slet'  x .. y  :=  A  'in' '//' b").
Reserved Notation "T x [1] = { A } ; 'return' ( b0 , b1 , .. , b2 )"
  (at level 200, format "T  x [1]  =  { A } ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").

Delimit Scope ctype_scope with ctype.
Local Open Scope ctype_scope.
Delimit Scope expr_scope with expr.
Inductive base_type := TZ | TWord (logsz : nat).
Inductive flat_type := Tbase (T : base_type) | Prod (A B : flat_type).
Context {var : base_type -> Type}.
Fixpoint interp_flat_type (interp_base_type : base_type -> Type) (t : 
flat_type) :=
  match t with
  | Tbase t => interp_base_type t
  | Prod x y => prod (interp_flat_type interp_base_type x) (interp_flat_type 
interp_base_type y)
  end.
Inductive exprf : flat_type -> Type :=
| Var {t} (v : var t) : exprf (Tbase t)
| LetIn {tx} (ex : exprf tx) {tC} (eC : interp_flat_type var tx -> exprf tC) : 
exprf tC
| Pair {tx} (ex : exprf tx) {ty} (ey : exprf ty) : exprf (Prod tx ty).
Global Arguments Var {_} _.
Global Arguments LetIn {_} _ {_} _.
Global Arguments Pair {_} _ {_} _.
Notation "T x [1] = { A } ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A 
(fun x => Pair .. (Pair b0%expr b1%expr) .. b2%expr)) : expr_scope.
Definition foo :=
  (fun x3 =>
     (LetIn (Var x3) (fun x18 : var TZ
                      => (Pair (Var x18) (Var x18))))).
Print foo.
