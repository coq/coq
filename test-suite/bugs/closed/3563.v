(* File reduced by coq-bug-finder from original input, then from 11716 lines to 11295 lines, then from 10518 lines to 21 lines, then \
from 37 lines to 21 lines *)
(* coqc version trunk (August 2014) compiled on Aug 31 2014 10:12:32 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (437b91a3ffd7327975a129b95b24d3f66ad7f3e4) *)
Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.
Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Goal forall (H H0 H1 : Type) (H2 : H1) (H3 : H1 -> H * H0)
            (H4 : (fun c : H1 => (fst (H3 c), snd (H3 c))%core) =
                  H3) (H5 : H -> Type) (H6 H7 : H5 (fst (H3 H2))),
       transport (fun y : H1 -> H * H0 => H5 (fst (y H2))) H4 H6 = H7.
  intros.
  match goal with
    | [ |- context ctx [transport (fun y => (?g (@fst ?C ?h (y H2)))) H4 H6] ]
      => set(foo:=h); idtac
  end.
  match goal with
    | [ |- context ctx [transport (fun y => (?g (fst (y H2))))] ]
      => idtac
  end.
Abort.
Goal forall (H H0 H1 : Type) (H2 : H1) (H3 : H1 -> (H1 -> H) * H0)
            (H4 : (fun c : H1 => (fst (H3 c), snd (H3 c))%core) =
                  H3) (H5 : H -> Type) (H6 H7 : H5 (fst (H3 H2) H2)),
       transport (fun y : H1 -> (H1 -> H) * H0 => H5 (fst (y H2) H2)) H4 H6 = H7.
  intros.
  match goal with
    | [ |- context ctx [transport (fun y => (?g (@fst ?C ?D (y H2) ?X)))] ]
      => set(foo:=X)
  end.
(* Anomaly: Uncaught exception Not_found(_). Please report. *)

(* Anomaly: Uncaught exception Not_found(_). Please report. *)
