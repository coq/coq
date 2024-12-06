From Corelib Require Extraction.

Record mixin_of T0 (b : unit) (T := T0) := Mixin { _ : T0 -> let U:=T0 in U }.
Definition d := Mixin nat tt (fun x => x).

Extraction TestCompile d.

(* Extra tests *)

Record R T0 (b:nat) (c:=b) (T:=T0) (e:nat) (d:c=e) := Build
  { g : T0 -> let U:=T0 in U ; h : d = d ; x : nat ; y := x+x }.

Definition r := {| g := (fun x : nat => x) ; h := eq_refl (eq_refl 0) ; x := 0 |}.

Extraction TestCompile r.
(*
(** val r0 : nat r **)

let r0 =
  { g = (fun x0 -> x0); x = O }
*)

Inductive I T (a:T) (U:=T) (b:T) (c:=(a,b)) : forall d (e:=S d) (h : S d = e), Type :=
| C : I T a b 0 eq_refl
| D : J T a b true eq_refl -> I T a b 1 eq_refl
with J T (a:T) (U:=T) (b:T) (c:=(a,b)) : forall (d:bool) (h:d = true), Type :=
| E : I T a b 0 eq_refl -> J T a b true eq_refl.

Definition c := D _ _ _ (E _ _ _ (C nat 0 0)).

Extraction TestCompile c.

(*
(** val c : nat i **)

let c =
  D (E C)
*)

CoInductive V T0 (b:nat) (c:=b) (T:=T0) (e:nat) (d:c=e) :=
  { k : T; b := c+e ; m : nat; z : option (W nat 0 0 eq_refl) }
with W T0 (b:nat) (c:=b) (T:=T0) (e:nat) (d:c=e) :=
  { l : V nat 0 0 eq_refl }.

CoFixpoint v :=
  {| k := 0 ; m := 0 ; z := Some w ; |}
with w := {| l := v |}.

Extraction TestCompile v.
(*
(** val v0 : nat v **)

let rec v0 =
  lazy (Build_V (O, O, (Some w0)))

(** val w0 : nat w **)

and w0 =
  lazy (Build_W v0)
*)
