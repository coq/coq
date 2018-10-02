Require Import FunctionalExtensionality.

Ltac make_apply_under_binders_in lem H :=
  let tac := make_apply_under_binders_in in
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              ltac:(let ret' := tac lem Hx in
                                exact ret')) in
         match eval cbv zeta in ret with
           | fun x => Some (@?P x) => let P' := (eval cbv zeta in P) in
                                      constr:(Some P')
         end
    | _ => let ret := constr:(ltac:(match goal with
                                  | _ => (let H' := fresh in
                                          pose H as H';
                                          apply lem in H';
                                          exact (Some H'))
                                  | _ => exact (@None nat)
                                end
                               )) in
           let ret' := (eval cbv beta zeta in ret) in
           constr:(ret')
    | _ => constr:(@None nat)
  end.

Ltac apply_under_binders_in lem H :=
  let H' := make_apply_under_binders_in lem H in
  let H'0 := match H' with Some ?H'0 => constr:(H'0) end in
  let H'' := fresh in
  pose proof H'0 as H'';
    clear H;
    rename H'' into H.

Goal forall A B C (f g : forall (x : A) (y : B x), C x y), (forall x y, f x y = g x y) -> True.
Proof.
  intros A B C f g H.
  let lem := constr:(@functional_extensionality_dep) in
  apply_under_binders_in lem H.
(* Anomaly: Uncaught exception Not_found(_). Please report. *)
