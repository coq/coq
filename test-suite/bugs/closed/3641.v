(* File reduced by coq-bug-finder from original input, then from 7593 lines to 243 lines, then from 256 lines to 102 lines, then from\
 104 lines to 28 lines *)
(* coqc version trunk (September 2014) compiled on Sep 17 2014 0:22:30 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (d34e1eed232c84590ddb80d70db9f7f7cf13584a) *)
Set Implicit Arguments.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Class UnitSubuniverse := { O : Type -> Type ; O_unit : forall T, T -> O T }.
Class ReflectiveSubuniverse := { rsubu_usubu : UnitSubuniverse ; O_rectnd : forall {P Q : Type} (f : P -> Q), O P -> Q }.
Global Existing Instance rsubu_usubu.
Context {subU : ReflectiveSubuniverse}.
Goal forall (A B : Type) (x : O A * O B) (x0 : B),
       { g : _ & O_rectnd (fun z : A * B => (O_unit (fst z), O_unit (snd z)))
                          (O_rectnd (fun a : A => O_unit (a, x0)) (fst x)) =
                 g x0 }.
  eexists.
  match goal with
    | [ |- context[?e] ] => is_evar e; let e' := fresh "e'" in pose (e' := e)
  end.
  Fail change ?g with e'. (* Stack overflow *)
