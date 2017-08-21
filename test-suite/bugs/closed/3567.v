
(* File reduced by coq-bug-finder from original input, then from 2901 lines to 69 lines, then from 80 lines to 63 lines *)
(* coqc version trunk (September 2014) compiled on Sep 2 2014 2:7:1 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (3c5daf4e23ee20f0788c0deab688af452e83ccf0) *)

Set Primitive Projections.
Set Implicit Arguments.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .
Add Printing Let prod.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Unset Implicit Arguments.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with idpath => idpath end.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) :=
  { equiv_inv : B -> A ;
    eisretr : Sect equiv_inv f;
    eissect : Sect f equiv_inv;
    eisadj : forall x : A, eisretr (f x) = ap f (eissect x) }.
Definition path_prod_uncurried {A B : Type} (z z' : A * B) (pq : (fst z = fst z') * (snd z = snd z'))
: (z = z')
  := match fst pq in (_ = z'1), snd pq in (_ = z'2) return z = (z'1, z'2) with
       | idpath, idpath => idpath
     end.
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).
Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
: (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.
Axiom ap_fst_path_prod : forall {A B : Type} {z z' : A * B}
                                (p : fst z = fst z') (q : snd z = snd z'),
                           ap fst (path_prod _ _ p q) = p.
Axiom ap_snd_path_prod : forall {A B : Type} {z z' : A * B}
                                (p : fst z = fst z') (q : snd z = snd z'),
                           ap snd (path_prod _ _ p q) = q.
Axiom eta_path_prod : forall {A B : Type} {z z' : A * B} (p : z = z'),
                        path_prod _ _(ap fst p) (ap snd p) = p.
Definition isequiv_path_prod {A B : Type} {z z' : A * B} : IsEquiv (path_prod_uncurried z z').
Proof.
  refine (Build_IsEquiv
            _ _ _
            (fun r => (ap fst r, ap snd r))
            eta_path_prod
            (fun pq => match pq with
                         | (p,q) => path_prod'
                                      (ap_fst_path_prod p q) (ap_snd_path_prod p q)
                       end) _).
  destruct z as [x y], z' as [x' y']. simpl.
(* Toplevel input, characters 15-50:
Error: Abstracting over the term "z" leads to a term
fun z0 : A * B =>
forall x : (fst z0 = fst z') * (snd z0 = snd z'),
eta_path_prod (path_prod_uncurried z0 z' x) =
ap (path_prod_uncurried z0 z')
  (let (p, q) as pq
       return
         ((ap (fst) (path_prod_uncurried z0 z' pq),
          ap (snd) (path_prod_uncurried z0 z' pq)) = pq) := x in
   path_prod' (ap_fst_path_prod p q) (ap_snd_path_prod p q))
which is ill-typed.
Reason is: Pattern-matching expression on an object of inductive type prod
has invalid information.
 *)
