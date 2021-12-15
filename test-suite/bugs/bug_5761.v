Set Primitive Projections.
Record mix := { a : nat ; b : a = a ; c : nat ; d : a = c ; e : nat ; f : nat }.
Ltac strip_args T ctor :=
  lazymatch type of ctor with
  | context[T]
    => match eval cbv beta in ctor with
       | ?ctor _ => strip_args T ctor
       | _ => ctor
       end
  end.
Ltac get_ctor T :=
  let full_ctor := constr:(ltac:(let x := fresh in intro x; econstructor; apply
x) : T -> T) in
  let ctor := constr:(fun x : T => ltac:(let v := strip_args T (full_ctor x) in
exact v)) in
  lazymatch ctor with
  | fun _ => ?ctor => ctor
  end.
Ltac uncurry_domain f :=
  lazymatch type of f with
  | forall (a : ?A) (b : @ ?B a), _
    => uncurry_domain (fun ab : { a : A & B a } => f (projT1 ab) (projT2 ab))
  | _ => eval cbv beta in f
  end.
Ltac get_of_sigma T :=
  let ctor := get_ctor T in
  uncurry_domain ctor.
Ltac repeat_existT :=
  lazymatch goal with
  | [ |- sigT _ ] => simple refine (existT _ _ _); [ repeat_existT | shelve ]
  | _ => shelve
  end.
 Ltac prove_to_of_sigma_goal of_sigma :=
  let v := fresh "v" in
  simple refine (exist _ _ (fun v => _ : id _ (of_sigma v) = v));
  try unfold of_sigma;
  [ intro v; destruct v; repeat_existT
  | cbv beta;
    repeat match goal with
           | [ |- context[projT2 ?k] ]
             => let x := fresh "x" in
                is_var k;
                destruct k as [k x]; cbn [projT1 projT2]
           end;
    unfold id; reflexivity ].
Ltac prove_to_of_sigma of_sigma :=
  constr:(
    ltac:(prove_to_of_sigma_goal of_sigma)
    : { to_sigma : _ | forall v, id to_sigma (of_sigma v) = v }).
Ltac get_to_sigma_gen of_sigma :=
  let v := prove_to_of_sigma of_sigma in
  eval hnf in (proj1_sig v).
Ltac get_to_sigma T :=
  let of_sigma := get_of_sigma T in
  get_to_sigma_gen of_sigma.
Definition to_sigma := ltac:(let v := get_to_sigma mix in exact v).
(* Error:
In nested Ltac calls to "get_to_sigma", "get_to_sigma_gen",
"prove_to_of_sigma",
"(_ : {to_sigma : _ | forall v, id to_sigma (of_sigma v) = v})" (with
of_sigma:=fun
            ab : {_
                 : {_
                   : {ab : {_ : {a : nat & a = a} & nat} &
                     projT1 (projT1 ab) = projT2 ab} & nat} & nat} =>
          {|
          a := projT1 (projT1 (projT1 (projT1 (projT1 ab))));
          b := projT2 (projT1 (projT1 (projT1 (projT1 ab))));
          c := projT2 (projT1 (projT1 (projT1 ab)));
          d := projT2 (projT1 (projT1 ab));
          e := projT2 (projT1 ab);
          f := projT2 ab |}) and "prove_to_of_sigma_goal", last call failed.
Anomaly "Uncaught exception Not_found." Please report at
http://coq.inria.fr/bugs/.
frame @  file "toplevel/coqtop.ml", line 640, characters 6-22
frame @  file "list.ml", line 73, characters 12-15
frame @  file "toplevel/vernac.ml", line 344, characters 2-13
frame @  file "toplevel/vernac.ml", line 308, characters 14-75
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "lib/flags.ml", line 141, characters 19-40
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "lib/flags.ml", line 11, characters 15-18
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "toplevel/vernac.ml", line 167, characters 6-16
frame @  file "toplevel/vernac.ml", line 151, characters 26-39
frame @  file "stm/stm.ml", line 2365, characters 2-35
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "stm/stm.ml", line 2355, characters 4-48
frame @  file "stm/stm.ml", line 2321, characters 4-100
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "stm/stm.ml", line 832, characters 6-10
frame @  file "stm/stm.ml", line 2206, characters 10-32
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "stm/stm.ml", line 975, characters 8-81
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "vernac/vernacentries.ml", line 2216, characters 10-389
frame @  file "lib/flags.ml", line 141, characters 19-40
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "lib/flags.ml", line 11, characters 15-18
frame @  file "vernac/command.ml", line 150, characters 4-56
frame @  file "interp/constrintern.ml", line 2046, characters 2-73
frame @  file "pretyping/pretyping.ml", line 1194, characters 19-77
frame @  file "pretyping/pretyping.ml", line 1155, characters 8-72
frame @  file "pretyping/pretyping.ml", line 628, characters 23-65
frame @  file "plugins/ltac/tacinterp.ml", line 2095, characters 21-61
frame @  file "proofs/pfedit.ml", line 178, characters 6-22
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "proofs/pfedit.ml", line 174, characters 8-36
frame @  file "proofs/proof.ml", line 351, characters 4-30
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "engine/proofview.ml", line 1222, characters 8-12
frame @  file "plugins/ltac/tacinterp.ml", line 2020, characters 19-36
frame @  file "plugins/ltac/tacinterp.ml", line 618, characters 4-70
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "plugins/ltac/tacinterp.ml", line 214, characters 6-9
frame @  file "pretyping/pretyping.ml", line 1198, characters 19-62
frame @  file "pretyping/pretyping.ml", line 1155, characters 8-72
raise @  unknown
frame @  file "pretyping/pretyping.ml", line 628, characters 23-65
frame @  file "plugins/ltac/tacinterp.ml", line 2095, characters 21-61
frame @  file "proofs/pfedit.ml", line 178, characters 6-22
raise @  file "lib/exninfo.ml", line 63, characters 8-15
frame @  file "proofs/pfedit.ml", line 174, characters 8-36
frame @  file "proofs/proof.ml", line 351, characters 4-30
raise @  file "lib/exninfo.ml", line 63, characters 8-15
 *)
