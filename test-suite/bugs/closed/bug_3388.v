Inductive test : bool -> bool -> Type :=
| test00 : test false false
| test01 : test false true
| test10 : test true false
.

(* This does not work *)
Definition test_a (t : test true false) : test true false :=
  match t with
    | test10 => test10
  end.

(* The following definition shows that test_a SHOULD work *)
Definition test_a_workaround (t : test true false) : test true false :=
  match t with
    | test10 => test10
    | _ => tt
  end.

(* Surprisingly, this works *)
Definition test_b (t : test false true) : test false true :=
  match t with
    | test01 => test01
  end.


(* This, too, works *)
Definition test_c x (t : test false x) : test false x :=
  match t with
    | test00 => test00
    | test01 => test01
  end.

Inductive test2 : bool -> bool -> Type :=
| test201 : test2 false true
| test210 : test2 true false
| test211 : test2 true true
.

(* Now this works *)
Definition test2_a (t : test2 true false) : test2 true false :=
  match t with
    | test210 => test210
  end.

(* Accordingly, this now fails *)
Definition test2_b (t : test2 false true) : test2 false true :=
  match t with
    | test201 => test201
  end.


(* This, too, fails *)
Definition test2_c x (t : test2 false x) : test2 false x :=
  match t with
    | test201 => test201
  end.
