(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 11678 lines to 11330 lines, then from 10721 lines to 9544 lines, then from 9549 lines to 794 lines, then from 810 lines to 785 lines, then from 628 lines to 246 lines, then from 220 lines to 89 lines, then from 80 lines to 47 lines *)
(* coqc version trunk (August 2014) compiled on Aug 22 2014 4:17:28 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (a67cc6941434124465f20b14a1256f2ede31a60e) *)

Set Implicit Arguments.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Local Set Primitive Projections.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Axiom path_prod : forall {A B : Type} (z z' : A * B), (fst z = fst z') -> (snd z = snd z') -> (z = z').
Axiom transport_path_prod : forall A B (P : A * B -> Type) (x y : A * B) (HA : fst x = fst y) (HB : snd x = snd y) Px,
                              transport P (path_prod _ _ HA HB) Px
                              = transport (fun x => P (x, snd y)) HA (transport (fun y => P (fst x, y)) HB Px).
Goal forall (T0 : Type) (snd1 snd0 f : T0) (p : @paths T0 f snd0)
            (f0 : T0) (p1 : @paths T0 f0 snd1) (T1 : Type)
            (fst1 fst0 : T1) (p0 : @paths T1 fst0 fst0) (p2 : @paths T1 fst1 fst1)
            (T : Type) (x2 : T) (T2 : Type) (T3 : forall (_ : T2) (_ : T2), Type)
            (x' : forall (_ : T1) (_ : T), T2) (m : T3 (x' fst1 x2) (x' fst0 x2)),
       @paths (T3 (x' fst1 x2) (x' fst0 x2))
              (@transport (prod T1 T0)
                          (fun x : prod T1 T0 =>
                             T3 (x' fst1 x2) (x' (fst x) x2))
                          (@pair T1 T0 fst0 f) (@pair T1 T0 fst0 snd0)
                          (@path_prod T1 T0 (@pair T1 T0 fst0 f)
                                      (@pair T1 T0 fst0 snd0) p0 p)
                          (@transport (prod T1 T0)
                                      (fun x : prod T1 T0 =>
                                         T3 (x' (fst x) x2) (x' fst0 x2))
                                      (@pair T1 T0 fst1 f0) (@pair T1 T0 fst1 snd1)
                                      (@path_prod T1 T0 (@pair T1 T0 fst1 f0)
                                                  (@pair T1 T0 fst1 snd1) p2 p1) m)) m.
  intros.
  match goal with
    | [ |- context[transport ?P (path_prod ?x ?y ?HA ?HB) ?Px] ]
      => rewrite (transport_path_prod P x y HA HB Px)
  end || fail "bad".
  Undo.
  Set Printing All.
  rewrite transport_path_prod. (* Toplevel input, characters 15-43:
Error:
In environment
T0 : Type
snd1 : T0
snd0 : T0
f : T0
p : @paths T0 f snd0
f0 : T0
p1 : @paths T0 f0 snd1
T1 : Type
fst1 : T1
fst0 : T1
p0 : @paths T1 fst0 fst0
p2 : @paths T1 fst1 fst1
T : Type
x2 : T
T2 : Type
T3 : forall (_ : T2) (_ : T2), Type
x' : forall (_ : T1) (_ : T), T2
m : T3 (x' fst1 x2) (x' fst0 x2)
Unable to unify "?25 (@pair ?23 ?24 (fst ?27) (snd ?27))" with
"?25 ?27".
 *)
