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

Notation "{ { xL | xR // xcut } }" := (xL+xR+xcut)
  (at level 0, xR at level 39, format "{ {  xL  |  xR  //  xcut  } }").
Check 1+1+1.

(* Test presence of notation variables in the recursive parts (introduced in dfdaf4de) *)
Notation "!!! x .. y , b" := ((fun x => b), .. ((fun y => b), True) ..) (at level 200, x binder).
Check !!! (x y:nat), True.

(* Allow level for leftmost nonterminal when printing-only, BZ#5739 *)

Notation "* x" := (id x) (only printing, at level 15, format "* x").
Notation "x . y" := (x + y) (only printing, at level 20, x at level 14, left associativity, format "x . y").
Check (((id 1) + 2) + 3).
Check (id (1 + 2)).

(* Test contraction of "forall x, let 'pat := x in ..." into "forall 'pat, ..." *)
(* for isolated "forall" (was not working already in 8.6) *)
Notation "! x .. y , A" := (id (forall x, .. (id (forall y, A)) .. )) (at level 200, x binder).
Check ! '(x,y), x+y=0.

(* Check that the terminator of a recursive pattern is interpreted in
   the correct environment of bindings *)
Notation "'exists_mixed' x .. y , P" := (ex (fun x => forall z:nat, .. (ex (fun y => forall z:nat, z=0 /\ P)) ..)) (at level 200, x binder).
Check exists_mixed x y '(u,t), x+y=0/\u+t=0.
Check exists_mixed x y '(z,t), x+y=0/\z+t=0.

(* Check that intermediary let-in are inserted inbetween instances of
   the repeated pattern *)
Notation "'exists_true' x .. y , P" := (exists x, True /\ .. (exists y, True /\ P) ..) (at level 200, x binder).
Check exists_true '(x,y) (u:=0) '(z,t), x+y=0/\z+t=0.

(* Check that generalized binders are correctly interpreted *)

Module G.
Generalizable Variables A R.
Class Reflexive {A:Type} (R : A->A->Prop) := reflexivity : forall x : A, R x x.
Check exists_true `{Reflexive A R}, forall x, R x x.
Check exists_true x `{Reflexive A R} y, x+y=0 -> forall z, R z z.
End G.

(* Allows recursive patterns for binders to be associative on the left *)
Notation "!! x .. y # A #" := (.. (A,(forall x, True)) ..,(forall y, True)) (at level 200, x binder).
Check !! a b : nat # True #.

(* Examples where the recursive pattern refer several times to the recursive variable *)

Notation "{{D  x , .. , y }}" := ((x,x), .. ((y,y),(0,0)) ..).
Check {{D 1, 2 }}.

Notation "! x .. y # A #" :=
  ((forall x, x=x), .. ((forall y, y=y), A) ..)
  (at level 200, x binder).
Check ! a b : nat # True #.

Notation "!!!! x .. y # A #" :=
  (((forall x, x=x),(forall x, x=0)), .. (((forall y, y=y),(forall y, y=0)), A) ..)
  (at level 200, x binder).
Check !!!! a b : nat # True #.

Notation "@@ x .. y # A # B #" :=
  ((forall x, .. (forall y, A) ..), (forall x, .. (forall y, B) ..))
  (at level 200, x binder).
Check @@ a b : nat # a=b # b=a #.

Notation "'exists_non_null' x .. y  , P" :=
  (ex (fun x => x <> 0 /\ .. (ex (fun y => y <> 0 /\ P)) ..))
  (at level 200, x binder).
Check exists_non_null x y z t , x=y/\z=t.

Notation "'forall_non_null' x .. y  , P" :=
  (forall x, x <> 0 -> .. (forall y, y <> 0 -> P) ..)
  (at level 200, x binder).
Check forall_non_null x y z t , x=y/\z=t.

(* Examples where the recursive pattern is in reverse order *)

Notation "{{RL  c , .. , d }}" := (pair d .. (pair c 0) ..).
Check {{RL 1 , 2}}.

Notation "{{RR  c , .. , d }}" := (pair .. (pair 0 d) .. c).
Check {{RR 1 , 2}}.

Set Printing All.
Check {{RL 1 , 2}}.
Check {{RR 1 , 2}}.
Unset Printing All.

Notation "{{RLRR  c , .. , d }}" := (pair d .. (pair c 0) .., pair .. (pair 0 d) .. c, pair c .. (pair d 0) .., pair .. (pair 0 c) .. d).
Check {{RLRR 1 , 2}}.
Unset Printing Notations.
Check {{RLRR 1 , 2}}.
Set Printing Notations.

(* Check insensitivity of "match" clauses to order *)

Module IfPat.
Notation "'if' t 'is' n .+ 1 'then' p 'else' q" :=
  (match t with S n => p | 0 => q end)
  (at level 200).
Check fun x => if x is n.+1 then n else 1.
End IfPat.

(* Examples with binding patterns *)

Check {'(x,y)|x+y=0}.

Module D.
Notation "'exists2'' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x pattern, p at level 200, right associativity,
    format "'[' 'exists2''  '/  ' x ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

Check exists2' (x,y), x=0 & y=0.
End D.

(* Ensuring for reparsability that printer of notations does not use a
   pattern where only an ident could be reparsed *)

Module E.
Inductive myex2 {A:Type} (P Q:A -> Prop) : Prop :=
  myex_intro2 : forall x:A, P x -> Q x -> myex2 P Q.
Notation "'myexists2' x : A , p & q" := (myex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x ident, A at level 200, p at level 200, right associativity,
    format "'[' 'myexists2'  '/  ' x  :  A ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.
Check myex2 (fun x => let '(y,z) := x in y>z) (fun x => let '(y,z) := x in z>y).
End E.

(* A canonical example of a notation with a non-recursive binder *)

Parameter myex : forall {A}, (A -> Prop) -> Prop.
Notation "'myexists' x , p" := (myex (fun x => p))
  (at level 200, x pattern, p at level 200, right associativity).

(* A canonical example of a notation with recursive binders *)

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

(* Check that printing 'pat uses an "as" when the variable bound to
   the pattern is dependent. We check it for the three kinds of
   notations involving bindings of patterns *)

Check fun '((x,y) as z) => x+y=0/\z=z.    (* Primitive fun/forall *)
Check myexists ((x,y) as z), x+y=0/\z=z.  (* Isolated binding pattern *)
Check exists '((x,y) as z), x+y=0/\z=z.   (* Applicative recursive binder *)
Check ∀ '((x,y) as z), x+y=0/\z=z.        (* Other example of recursive binder, now treated as the exists case *)

(* Check parsability and printability of irrefutable disjunctive patterns *)

Check fun '(((x,y),true)|((x,y),false)) => x+y.
Check myexists (((x,y),true)|((x,y),false)), x>y.
Check exists '(((x,y),true)|((x,y),false)), x>y.
Check ∀ '(((x,y),true)|((x,y),false)), x>y.

(* Check Georges' printability of a "if is then else" notation *)

Module IfPat2.
Notation "'if' c 'is' p 'then' u 'else' v" :=
  (match c with p => u | _ => v end)
  (at level 200, p pattern at level 100).
Check fun p => if p is S n then n else 0.
Check fun p => if p is Lt then 1 else 0.
End IfPat2.

(* Check that mixed binders and terms defaults to ident and not pattern *)
Module F.
  (* First without an indirection *)
Notation "[ n | t ]" := (n, (fun n : nat => t)).
Check fun S : nat => [ S | S+S ].
Check fun N : nat => (N, (fun n => n+0)). (* another test in passing *)
  (* Then with an indirection *)
Notation "[[ n | p | t ]]" := (n, (fun p : nat => t)).
Notation "[[ n | t ]]" := [[ n | n | t ]].
Check fun S : nat => [[ S | S+S ]].
End F.

(* Check parsability/printability of {x|P} and variants *)

Check {I:nat|I=I}.
Check {'I:True|I=I}.
Check {'(x,y)|x+y=0}.

(* Check exists2 with a pattern *)
Check ex2 (fun x => let '(y,z) := x in y>z) (fun x => let '(y,z) := x in z>y).

Module Issue7110.
Open Scope list_scope.
Notation "[ :: x1 , x2 , .. , xn & s ]" := (x1 :: x2 :: .. (xn :: s) ..)
  (at level 0).
Definition foo (l : list nat) :=
  match l with
  | a :: (b :: l) as l1 => l1
  | _ => l
end.
Print foo.
End Issue7110.

Module LocateNotations.
Locate "exists".
Locate "( _ , _ , .. , _ )".
End LocateNotations.

Module Issue7731.

Axiom (P : nat -> Prop).
Parameter (X : nat).
Notation "## @ E ^^^" := (P E) (at level 20, E at level 1, format "'[ ' ## '/' @ E '/' ^^^ ']'").
Notation "%" := X.

Set Printing Width 7.
Goal ## @ % ^^^.
Show.
Abort.

End Issue7731.

Module Issue8126.

Definition myfoo (x : nat) (y : nat) (z : unit) := y.
Notation myfoo0 := (@myfoo 0).
Notation myfoo01 := (@myfoo0 1).
Check myfoo 0 1 tt. (* was printing [myfoo0 1 HI], but should print [myfoo01 HI]  *)
Check myfoo0 1 tt. (* was printing [myfoo0 1 HI], but should print [myfoo01 HI]  *)
Check myfoo01 tt. (* was printing [myfoo0 1 HI], but should print [myfoo01 HI]  *)

End Issue8126.
