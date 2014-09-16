(* \sqrt 2 is irrationnal, (c) 2006 Pierre Corbineau *)

Set Firstorder Depth 1.
Require Import ArithRing Wf_nat Peano_dec Div2 Even Lt.

Lemma double_div2: forall n, div2 (double n) = n.
proof.
  assume n:nat.
  per induction on n.
    suppose it is 0.
     suffices (0=0) to show thesis.
     thus thesis.
    suppose it is (S m) and Hrec:thesis for m.
      have (div2 (double (S m))= div2 (S (S (double m)))).
           ~= (S (div2 (double m))).
      thus ~= (S m) by Hrec.
  end induction.
end proof.
Show Script.
Qed.

Lemma double_inv : forall n m, double n = double m -> n = m .
proof.
  let n, m be such that H:(double n = double m).
have (n = div2 (double n)) by double_div2,H.
       ~= (div2 (double m)) by H.
  thus ~= m by double_div2.
end proof.
Qed.

Lemma double_mult_l : forall n m, (double (n * m)=n * double m).
proof.
  assume n:nat and m:nat.
  have (double (n * m) = n*m + n * m).
       ~= (n * (m+m)) by * using ring.
  thus ~= (n * double m).
end proof.
Qed.

Lemma double_mult_r : forall n m, (double (n * m)=double n * m).
proof.
  assume n:nat and m:nat.
  have (double (n * m) = n*m + n * m).
       ~= ((n + n) * m) by * using ring.
  thus ~= (double n * m).
end proof.
Qed.

Lemma even_is_even_times_even: forall n, even (n*n) -> even n.
proof.
  let n be such that H:(even (n*n)).
  per cases of (even n \/ odd n) by even_or_odd.
    suppose (odd n).
      hence thesis by H,even_mult_inv_r.
  end cases.
end proof.
Qed.

Lemma main_thm_aux: forall n,even n ->
double (double (div2 n *div2 n))=n*n.
proof.
  given n such that H:(even n).
 *** have (double (double (div2 n * div2 n))
        = double (div2 n) * double (div2 n))
        by double_mult_l,double_mult_r.
  thus ~= (n*n) by H,even_double.
end proof.
Qed.

Require Import Omega.

Lemma even_double_n: (forall m, even (double m)).
proof.
  assume m:nat.
  per induction on m.
    suppose it is 0.
      thus thesis.
    suppose it is (S mm) and thesis for mm.
      then H:(even (S (S (mm+mm)))).
      have (S (S (mm + mm)) = S mm + S mm)  using omega.
      hence (even (S mm +S mm)) by H.
  end induction.
end proof.
Qed.

Theorem main_theorem: forall n p, n*n=double (p*p) -> p=0.
proof.
  assume n0:nat.
  define P n as (forall p, n*n=double (p*p) -> p=0).
  claim rec_step: (forall n, (forall m,m<n-> P m) -> P n).
    let n be such that H:(forall m : nat, m < n -> P m) and p:nat .
    per cases of ({n=0}+{n<>0}) by eq_nat_dec.
      suppose H1:(n=0).
        per cases on p.
          suppose it is (S p').
            assume (n * n = double (S p' * S p')).
              =~ 0 by H1,mult_n_O.
              ~= (S (  p' + p' * S p' + S p'* S p'))
                by plus_n_Sm.
            hence thesis .
          suppose it is 0.
            thus thesis.
        end cases.
      suppose H1:(n<>0).
        assume H0:(n*n=double (p*p)).
        have (even (double (p*p))) by even_double_n .
        then (even (n*n)) by H0.
        then H2:(even n) by even_is_even_times_even.
        then (double (double (div2 n *div2 n))=n*n)
          by main_thm_aux.
          ~= (double (p*p)) by H0.
        then H':(double (div2 n *div2 n)= p*p) by double_inv.
        have (even (double (div2 n *div2 n))) by even_double_n.
        then (even (p*p)) by even_double_n,H'.
        then H3:(even p) by even_is_even_times_even.
        have (double(double (div2 n * div2 n)) = n*n)
          by H2,main_thm_aux.
          ~= (double (p*p)) by H0.
          ~= (double(double (double (div2 p * div2 p))))
            by H3,main_thm_aux.
        then H'':(div2 n * div2 n = double (div2 p * div2 p))
          by double_inv.
        then (div2 n < n) by lt_div2,neq_O_lt,H1.
        then H4:(div2 p=0) by  (H (div2 n)),H''.
        then (double (div2 p) = double 0).
             =~ p by even_double,H3.
        thus ~= 0.
    end cases.
  end claim.
  hence thesis by (lt_wf_ind n0 P).
end proof.
Qed.

Require Import Reals Field.
(*Coercion INR: nat >->R.
Coercion IZR: Z >->R.*)

Open Scope R_scope.

Lemma square_abs_square:
  forall p,(INR (Z.abs_nat p) * INR (Z.abs_nat p)) = (IZR p * IZR p).
proof.
  assume p:Z.
  per cases on p.
    suppose it is (0%Z).
      thus thesis.
    suppose it is (Zpos z).
      thus thesis.
    suppose it is (Zneg z).
      have ((INR (Z.abs_nat (Zneg z)) * INR (Z.abs_nat (Zneg z))) =
      (IZR (Zpos z) * IZR (Zpos z))).
           ~= ((- IZR (Zpos z)) * (- IZR (Zpos z))).
      thus ~= (IZR (Zneg z) * IZR (Zneg z)).
  end cases.
end proof.
Qed.

Definition irrational (x:R):Prop :=
  forall (p:Z) (q:nat),q<>0%nat -> x<> (IZR p/INR q).

Theorem irrationnal_sqrt_2: irrational (sqrt (INR 2%nat)).
proof.
  let p:Z,q:nat be such that H:(q<>0%nat)
                         and H0:(sqrt (INR 2%nat)=(IZR p/INR q)).
  have H_in_R:(INR q<>0:>R) by H.
  have triv:((IZR p/INR q* INR q) =IZR p :>R) by * using field.
  have sqrt2:((sqrt (INR 2%nat) * sqrt (INR 2%nat))= INR 2%nat:>R) by sqrt_def.
  have (INR (Z.abs_nat p * Z.abs_nat p)
     = (INR (Z.abs_nat p) * INR (Z.abs_nat p)))
    by mult_INR.
    ~=  (IZR p* IZR p) by square_abs_square.
    ~=  ((IZR p/INR q*INR q)*(IZR p/INR q*INR q)) by triv. (* we have to factor because field is too weak *)
    ~=  ((IZR p/INR q)*(IZR p/INR q)*(INR q*INR q)) using ring.
    ~=  (sqrt (INR 2%nat) * sqrt (INR 2%nat)*(INR q*INR q)) by H0.
    ~= (INR (2%nat * (q*q)))  by sqrt2,mult_INR.
  then  (Z.abs_nat p * Z.abs_nat p = 2* (q * q))%nat.
    ~= ((q*q)+(q*q))%nat.
    ~= (Div2.double (q*q)).
  then (q=0%nat) by main_theorem.
  hence thesis by H.
end proof.
Qed.
