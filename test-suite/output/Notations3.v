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

Notation "{# x | P }" := (ex2 (fun y => x = y) (fun x => P)).
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

(* Cyprien's part of bug #4765 *)

Notation foo5 x T y := (fun x : T => y).
Check foo5 x nat x.
