Section group_morphism.

(* An example with default canonical structures *)

Variable A B : Type.
Variable plusA : A -> A -> A.
Variable plusB : B -> B -> B.
Variable zeroA : A.
Variable zeroB : B.
Variable eqA : A -> A -> Prop.
Variable eqB : B -> B -> Prop.
Variable phi : A -> B.

Record img := {
  ia : A;
  ib :> B;
  prf : phi ia = ib
}.

Parameter eq_img : forall (i1:img) (i2:img),
  eqB (ib i1) (ib i2) -> eqA (ia i1) (ia i2).

Lemma phi_img (a:A) : img.
  intro a.
  exists  a (phi a).
  refine ( refl_equal _).
Defined.
Canonical Structure phi_img.

Lemma zero_img : img.
  exists zeroA zeroB.
  admit.
Defined.
Canonical Structure zero_img.

Lemma plus_img : img -> img -> img.
intros i1 i2.
exists (plusA (ia i1) (ia i2)) (plusB (ib i1) (ib i2)).
admit.
Defined.
Canonical Structure plus_img.

(* Print Canonical Projections. *)

Goal forall a1 a2, eqA (plusA a1 zeroA) a2.
  intros a1 a2.
  refine  (eq_img _ _  _).
change (eqB (plusB (phi a1) zeroB) (phi a2)).
Admitted.

End group_morphism.

Open Scope type_scope.

Section type_reification.

Inductive term :Type := 
   Fun : term -> term -> term
 | Prod : term -> term -> term
 | Bool : term
 | SET :term
 | PROP :term
 | TYPE :term
 | Var : Type -> term.

Fixpoint interp (t:term) := 
  match t with 
    Bool => bool
  | SET => Set
  | PROP => Prop
  | TYPE => Type   
  | Fun a b => interp a -> interp b
  | Prod a b => interp a * interp b
  | Var x => x
end.

Record interp_pair :Type := 
  { repr:>term;
    abs:>Type;
    link: abs = interp repr }.

Lemma prod_interp :forall (a b:interp_pair),a * b = interp (Prod a b) .
proof.
let a:interp_pair,b:interp_pair.
reconsider thesis as (a * b = interp a * interp b).
thus thesis by (link a),(link b).
end proof.
Qed.

Lemma fun_interp :forall (a b:interp_pair), (a -> b) = interp (Fun a b).
proof.
let a:interp_pair,b:interp_pair.
reconsider thesis as ((a -> b) = (interp a -> interp b)).
thus thesis using rewrite (link a);rewrite (link b);reflexivity.
end proof.
Qed.

Canonical Structure ProdCan (a b:interp_pair) := 
  Build_interp_pair (Prod a b) (a * b) (prod_interp a b).

Canonical Structure FunCan (a b:interp_pair) := 
  Build_interp_pair (Fun a b) (a -> b) (fun_interp a b).

Canonical Structure BoolCan := 
  Build_interp_pair Bool bool (refl_equal _).

Canonical Structure VarCan (x:Type) := 
  Build_interp_pair (Var x) x (refl_equal _).

Canonical Structure SetCan := 
  Build_interp_pair SET Set (refl_equal _).

Canonical Structure PropCan := 
  Build_interp_pair PROP Prop (refl_equal _).

Canonical Structure TypeCan := 
  Build_interp_pair TYPE Type (refl_equal _).

(* Print Canonical Projections. *)

Variable A:Type.

Variable Inhabited: term -> Prop.

Variable Inhabited_correct: forall p, Inhabited (repr p)  -> abs p.

Lemma L : Prop * A -> bool * (Type -> Set) .
refine (Inhabited_correct _ _).
change (Inhabited (Fun (Prod PROP (Var A)) (Prod Bool (Fun TYPE SET)))).
Admitted.

Check L : abs _ .

End type_reification.








 

