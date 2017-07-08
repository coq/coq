(**********************************************************************)
(* Check precedence, spacing, etc. in printing with curly brackets    *)

Check {x|x=0}+{True/\False}+{forall x, x=0}.

(**********************************************************************)
(* Check printing of notations with several instances of a recursive pattern *)
(* Was wrong but I could not trigger a problem due to the collision between *)
(* different instances of ".." *)

Notation "[< x , y , .. , z >]" := (pair (.. (pair x y) ..) z,pair y ( .. (pair z x) ..)).
Check [<0,2>].
Check ((0,2),(2,0)).
Check ((0,2),(2,2)).
Unset Printing Notations.
Check [<0,2>].
Set Printing Notations.

Notation "<< x , y , .. , z >>" := ((.. (x,y) .., z),(z, .. (y,x) ..)).
Check <<0,2,4>>.
Check (((0,2),4),(4,(2,0))).
Check (((0,2),4),(2,(2,0))).
Check (((0,2),4),(0,(2,4))).
Unset Printing Notations.
Check <<0,2,4>>.
Set Printing Notations.

(**********************************************************************)
(* Check notations with recursive notations both in binders and terms *)

Notation "'ETA' x .. y , f" :=
  (fun x => .. (fun y => (.. (f x) ..) y ) ..)
  (at level 200, x binder, y binder).
Check ETA (x:nat) (y:nat), Nat.add.
Check ETA (x y:nat), Nat.add.
Check ETA x y, Nat.add.
Unset Printing Notations.
Check ETA (x:nat) (y:nat), Nat.add.
Set Printing Notations.
Check ETA x y, le_S.

Notation "'CURRY' x .. y , f" := (fun x => .. (fun y => f (x, .. (y,tt) ..)) ..)
  (at level 200, x binder, y binder).
Check fun f => CURRY (x:nat) (y:bool), f.

Notation "'CURRYINV' x .. y , f" := (fun x => .. (fun y => f (y, .. (x,tt) ..)) ..)
  (at level 200, x binder, y binder).
Check fun f => CURRYINV (x:nat) (y:bool), f.

Notation "'CURRYLEFT' x .. y , f" := (fun x => .. (fun y => f (.. (tt,x) .., y)) ..)
  (at level 200, x binder, y binder).
Check fun f => CURRYLEFT (x:nat) (y:bool), f.

Notation "'CURRYINVLEFT' x .. y , f" := (fun x => .. (fun y => f (.. (tt,y) .., x)) ..)
  (at level 200, x binder, y binder).
Check fun f => CURRYINVLEFT (x:nat) (y:bool), f.

(**********************************************************************)
(* Notations with variables bound both as a term and as a binder      *)
(* This is #4592 *)

Notation "{# x | P }" := (ex2 (fun y => x = y) (fun x => P)) : type_scope.
Check forall n:nat, {# n | 1 > n}.

Parameter foo : forall {T}(x : T)(P : T -> Prop), Prop.
Notation "{| x | P |}" := (foo x (fun x => P)).
Check forall x:nat, {| x | x > 0 |}.

Check ex2 (fun x => x=1) (fun x0 => x0=2).

(* Other tests about alpha-conversions: the following notation
   contains all three kinds of bindings:

   - x is bound in the lhs as a term and a binder: its name is forced
     by its position as a term; it can bind variables in P
   - y is bound in the lhs as a binder only: its name is given by its
     name as a binder in the term to display; it can bind variables in P
   - z is a binder local to the rhs; it cannot bind a variable in P
*)

Parameter foo2 : forall {T}(x : T)(P : T -> T -> T -> Prop), Prop.
Notation "{| x , y | P |}_2" := (foo2 x (fun x y z => P z y x)).

(* Not printable: z (resp c, n) occurs in P *)
Check fun n => foo2 n (fun x y z => (fun _ _ _ => x+y+z=0) z y x).
Check fun n => foo2 n (fun a b c => (fun _ _ _ => a+b+c=0) c b a).
Check fun n => foo2 n (fun n y z => (fun _ _ _ => n+y+z=0) z y n).
Check fun n => foo2 n (fun x n z => (fun _ _ _ => x+n+z=0) z n x).
Check fun n => foo2 n (fun x y n => (fun _ _ _ => x+y+n=0) n y x).

(* Printable *)
Check fun n => foo2 n (fun x y z => (fun _ _ _ => x+y=0) z y x).
Check fun n => foo2 n (fun n y z => (fun _ _ _ => n+y=0) z y n).
Check fun n => foo2 n (fun x n z => (fun _ _ _ => x+n=0) z n x).

(* Not printable: renaming x into n would bind the 2nd occurrence of n *)
Check fun n => foo2 n (fun x y z => (fun _ _ _ => x+y+n=0) z y x).
Check fun n => foo2 n (fun x y z => (fun _ _ _ => x+y+n=0) z y x).

(* Other tests *)
Parameter foo3 : forall {T}(x : T)(P : T -> T -> T -> Prop), Prop.
Notation "{| x , P |}_3" := (foo3 x (fun x x x => P x)).

(* Printable *)
Check fun n : nat => foo3 n (fun x y z => (fun _ => 0=0) z).
Check fun n => foo3 n (fun x y z => (fun _ => z=0) z).

(* Not printable: renaming z in n would hide the renaming of x into n *)
Check fun n => foo3 n (fun x y z => (fun _ => x=0) z).

(* Other tests *)
Parameter foo4 : forall {T}(x : T)(P : T -> T -> T -> Prop), Prop.
Notation "{| x , P |}_4" := (foo4 x (fun x _ z => P z)).

(* Printable *)
Check fun n : nat => foo4 n (fun x y z => (fun _ => 0=0) z).
Check fun n => foo4 n (fun x y z => (fun _ => x=0) z).

(* Not printable: y, z not allowed to occur in P *)
Check fun n => foo4 n (fun x y z => (fun _ => z=0) z).
Check fun n => foo4 n (fun x y z => (fun _ => y=0) z).

(**********************************************************************)
(* Test printing of #4932                                             *)

Inductive ftele : Type :=
| fb {T:Type} : T -> ftele
| fr {T} : (T -> ftele) -> ftele.

Fixpoint args ftele : Type :=
  match ftele with
    | fb _ => unit
    | fr f => sigT (fun t => args (f t))
  end.

Definition fpack := sigT args.
Definition pack fp fa : fpack := existT _ fp fa.

Notation "'tele' x .. z := b" :=
  (fun x => .. (fun z =>
     pack (fr (fun x => .. ( fr (fun z => fb b) ) .. ) )
          (existT _ x .. (existT _ z tt) .. )
                ) ..)
  (at level 85, x binder, z binder).

Check tele (t:Type) '((y,z):nat*nat) (x:t) := tt.

(* Checking that "fun" in a notation does not mixed up with the
   detection of a recursive binder *)

Notation "[ x ;; .. ;; y ]" := ((x,((fun u => S u), .. (y,(fun u => S u,fun v:nat => v)) ..))).
Check [ fun x => x+0 ;; fun x => x+1 ;; fun x => x+2 ].

(* Cyprien's part of bug #4765 *)

Section Bug4765.

Notation foo5 x T y := (fun x : T => y).
Check foo5 x nat x.

End Bug4765.

(**********************************************************************)
(* Test printing of #5526                                             *)

Notation "x === x" := (eq_refl x) (only printing, at level 10).
Check (fun x => eq_refl x).

(* Test recursive notations with the recursive pattern repeated on the right *)

Notation "{{ x , .. , y , z }}" := (pair x .. (pair y z) ..).
Check {{0,1}}.
Check {{0,1,2}}.
Check {{0,1,2,3}}.

(* Test printing of #5608                                             *)

Reserved Notation "'letpair' x [1] = { A } ; 'return' ( b0 , b1 , .. , b2 )"
  (at level 200, format "'letpair'  x  [1]  =  { A } ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Notation "'letpair' x [1] = { a } ; 'return' ( b0 , b1 , .. , b2 )" :=
  (let x:=a in ( .. (b0,b1) .., b2)).
Check letpair x [1] = {0}; return (1,2,3,4).

(* Test spacing in #5569 *)

Section S1.
Variable plus : nat -> nat -> nat.
Infix "+" := plus.
Notation "{ { xL | xR // xcut } }" := (xL+xR+xcut)
  (at level 0, xR at level 39, format "{ {  xL  |  xR  //  xcut  } }").
Check 1+1+1.
End S1.

(* Test presence of notation variables in the recursive parts (introduced in dfdaf4de) *)
Notation "!!! x .. y , b" := ((fun x => b), .. ((fun y => b), True) ..) (at level 200, x binder).
Check !!! (x y:nat), True.

(* Allow level for leftmost nonterminal when printing-only, BZ#5739 *)

Section S2.
Notation "* x" := (id x) (only printing, at level 15, format "* x") : nat_scope.
Notation "x . y" := (x + y) (only printing, at level 20, x at level 14, left associativity, format "x . y") : nat_scope.
Check (((id 1) + 2) + 3).
Check (id (1 + 2)).
End S2.

(* Test printing of notations guided by scope *)

Module A.

Delimit Scope line_scope with line.
Notation "{ }" := nil (format "{ }") : line_scope.
Notation "{ x }" := (cons x nil) : line_scope.
Notation "{ x ; y ; .. ; z }" :=  (cons x (cons y .. (cons z nil) ..)) : line_scope.
Notation "[ ]" := nil (format "[ ]") : matx_scope.
Notation "[ l ]" := (cons l%line nil) : matx_scope.
Notation "[ l ; l' ; .. ; l'' ]" :=  (cons l%line (cons l'%line .. (cons l''%line nil) ..))
  (format "[ '[v' l ; '/' l' ; '/' .. ; '/' l'' ']' ]") : matx_scope.

Open Scope matx_scope.
Check [[0;0]].
Check [[1;2;3];[4;5;6];[7;8;9]].

End A.

(* Example by Beta Ziliani *)

Require Import Lists.List.

Module B.

Import ListNotations.

Delimit Scope pattern_scope with pattern.
Delimit Scope patterns_scope with patterns.

Notation "a => b" := (a, b) (at level 201) : pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((cons p1%pattern (.. (cons pn%pattern nil) ..)))
    (at level 91, p1 at level 210, pn at level 210) : patterns_scope.

Definition mymatch (n:nat) (l : list (nat * nat)) := tt.
Arguments mymatch _ _%patterns.
Notation "'mmatch' n ls" := (mymatch n ls) (at level 0).

Close Scope patterns_scope.
Close Scope pattern_scope.

Definition amatch := mmatch 0 with 0 => 1 | 1 => 2 end.
Print amatch. (* Good: amatch = mmatch 0 (with 0 => 1| 1 => 2 end) *)

Definition alist := [0;1;2].
Print alist.

End B.
