(*
   Implementing reals a la Stolzenberg

   Danko Ilik, March 2007

   XField.v -- (unfinished) axiomatisation of the theories of real and
               rational intervals.
*)

Definition associative (A:Type)(op:A->A->A) :=
  forall x y z:A, op (op x y) z = op x (op y z).

Definition commutative (A:Type)(op:A->A->A) :=
  forall x y:A, op x y = op y x.

Definition trichotomous (A:Type)(R:A->A->Prop) :=
  forall x y:A, R x y \/ x=y \/ R y x.

Definition relation (A:Type) := A -> A -> Prop.
Definition reflexive (A:Type)(R:relation A) := forall x:A, R x x.
Definition transitive (A:Type)(R:relation A) :=
  forall x y z:A, R x y -> R y z -> R x z.
Definition symmetric (A:Type)(R:relation A) := forall x y:A, R x y -> R y x.

Record interval (X:Set)(le:X->X->Prop) : Set :=
  interval_make {
    interval_left : X;
    interval_right : X;
    interval_nonempty : le interval_left interval_right
  }.

Record I (grnd:Set)(le:grnd->grnd->Prop) : Type := Imake {
  Icar    := interval grnd le;
  Iplus   : Icar -> Icar -> Icar;
  Imult   : Icar -> Icar -> Icar;
  Izero   : Icar;
  Ione    : Icar;
  Iopp    : Icar -> Icar;
  Iinv    : Icar -> Icar;
  Ic      : Icar -> Icar -> Prop; (* consistency *)
  (* monoids *)
  Iplus_assoc    : associative Icar Iplus;
  Imult_assoc    : associative Icar Imult;
  (* abelian groups *)
  Iplus_comm     : commutative Icar Iplus;
  Imult_comm     : commutative Icar Imult;
  Iplus_0_l      : forall x:Icar, Ic (Iplus Izero x) x;
  Iplus_0_r      : forall x:Icar, Ic (Iplus x Izero) x;
  Imult_0_l      : forall x:Icar, Ic (Imult Ione x) x;
  Imult_0_r      : forall x:Icar, Ic (Imult x Ione) x;
  Iplus_opp_r    : forall x:Icar, Ic (Iplus x (Iopp x)) (Izero);
  Imult_inv_r    : forall x:Icar, ~(Ic x Izero) -> Ic (Imult x (Iinv x)) Ione;
  (* distributive laws *)
  Imult_plus_distr_l : forall x x' y y' z z' z'',
    Ic x x' -> Ic y y' -> Ic z z' -> Ic z z'' ->
    Ic (Imult (Iplus x y) z) (Iplus (Imult x' z') (Imult y' z''));
  (* order and lattice structure *)
  Ilt          : Icar -> Icar -> Prop;
  Ilc          := fun (x y:Icar) => Ilt x y \/ Ic x y;
  Isup         : Icar -> Icar -> Icar;
  Iinf         : Icar -> Icar -> Icar;
  Ilt_trans    : transitive _ lt;
  Ilt_trich    : forall x y:Icar, Ilt x y \/ Ic x y \/ Ilt y x;
  Isup_lub     : forall x y z:Icar, Ilc x z -> Ilc y z -> Ilc (Isup x y) z;
  Iinf_glb     : forall x y z:Icar, Ilc x y -> Ilc x z -> Ilc x (Iinf y z);
  (* order preserves operations? *)
  (* properties of Ic *)
  Ic_refl   : reflexive _ Ic;
  Ic_sym    : symmetric _ Ic
}.

Definition interval_set (X:Set)(le:X->X->Prop) :=
  (interval X le) -> Prop. (* can be Set as well *)
Check interval_set.
Check Ic.
Definition consistent (X:Set)(le:X->X->Prop)(TI:I X le)(p:interval_set X le) :=
  forall I J:interval X le, p I -> p J -> (Ic X le TI) I J.
Check consistent.
(* define 'fine' *)

Record N (grnd:Set)(le:grnd->grnd->Prop)(grndI:I grnd le) : Type := Nmake {
  Ncar    := interval_set grnd le;
  Nplus   : Ncar -> Ncar -> Ncar;
  Nmult   : Ncar -> Ncar -> Ncar;
  Nzero   : Ncar;
  None    : Ncar;
  Nopp    : Ncar -> Ncar;
  Ninv    : Ncar -> Ncar;
  Nc      : Ncar -> Ncar -> Prop; (* Ncistency *)
  (* monoids *)
  Nplus_assoc    : associative Ncar Nplus;
  Nmult_assoc    : associative Ncar Nmult;
  (* abelian groups *)
  Nplus_comm     : commutative Ncar Nplus;
  Nmult_comm     : commutative Ncar Nmult;
  Nplus_0_l      : forall x:Ncar, Nc (Nplus Nzero x) x;
  Nplus_0_r      : forall x:Ncar, Nc (Nplus x Nzero) x;
  Nmult_0_l      : forall x:Ncar, Nc (Nmult None x) x;
  Nmult_0_r      : forall x:Ncar, Nc (Nmult x None) x;
  Nplus_opp_r    : forall x:Ncar, Nc (Nplus x (Nopp x)) (Nzero);
  Nmult_inv_r    : forall x:Ncar, ~(Nc x Nzero) -> Nc (Nmult x (Ninv x)) None;
  (* distributive laws *)
  Nmult_plus_distr_l : forall x x' y y' z z' z'',
    Nc x x' -> Nc y y' -> Nc z z' -> Nc z z'' ->
    Nc (Nmult (Nplus x y) z) (Nplus (Nmult x' z') (Nmult y' z''));
  (* order and lattice structure *)
  Nlt          : Ncar -> Ncar -> Prop;
  Nlc          := fun (x y:Ncar) => Nlt x y \/ Nc x y;
  Nsup         : Ncar -> Ncar -> Ncar;
  Ninf         : Ncar -> Ncar -> Ncar;
  Nlt_trans    : transitive _ lt;
  Nlt_trich    : forall x y:Ncar, Nlt x y \/ Nc x y \/ Nlt y x;
  Nsup_lub     : forall x y z:Ncar, Nlc x z -> Nlc y z -> Nlc (Nsup x y) z;
  Ninf_glb     : forall x y z:Ncar, Nlc x y -> Nlc x z -> Nlc x (Ninf y z);
  (* order preserves operations? *)
  (* properties of Nc *)
  Nc_refl   : reflexive _ Nc;
  Nc_sym    : symmetric _ Nc
}.

