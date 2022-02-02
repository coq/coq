Set Primitive Projections.
Record Box {T} := box { unbox : T }.
Arguments Box : clear implicits.
Definition indirect := @unbox.
Goal forall T : @Box Set, unbox T -> False.
  intros T x.
  let Tindirect := constr:(indirect _ T) in
  let Tdefined := eval cbv [indirect] in Tindirect in
  let Tfolded := type of x in
  cbv [unbox] in x;
  let Tunfolded := type of x in
  match Tdefined with Tdefined => idtac end;
  match Tfolded with Tfolded => idtac end;
  match Tfolded with Tunfolded => idtac end;
  match Tdefined with Tfolded => idtac end;
  match Tdefined with Tunfolded => idtac end;
  match Tfolded with Tdefined => idtac end;
  (* matches above have passed for a while
     matches below used to fail with "Error: No matching clauses for match." *)
  match Tunfolded with Tunfolded => idtac end;
  match Tunfolded with Tfolded => idtac end;
  match Tunfolded with Tdefined => idtac end;
  assert_fails (constr_eq Tdefined Tfolded);
  assert_fails (constr_eq Tdefined Tunfolded);
  assert_fails (constr_eq Tfolded Tunfolded);
  idtac Tdefined Tfolded Tunfolded.
Abort.
