Theorem this_is_trivial: True.
proof.
  thus thesis.
end proof.
Qed.

Theorem T: (True /\ True) /\ True.
  split. split.
proof. (* first subgoal *)
  thus thesis.
end proof.
trivial. (* second subgoal *)
proof. (* third subgoal *)
  thus thesis.
end proof.
Abort.

Theorem this_is_not_so_trivial: False.
proof.
end proof. (* here a warning is issued *)
Fail Qed. (* fails: the proof in incomplete *)
Admitted. (* Oops! *)

Theorem T: True.
proof.
escape.
auto.
return.
Abort.

Theorem T: let a:=false in let b:= true in ( if a then True else False -> if b then True else False).
intros a b.
proof.
assume H:(if a then True else False).
reconsider H as False.
reconsider thesis as True.
Abort.

Theorem T: forall x, x=2 -> 2+x=4.
proof.
let x be such that H:(x=2).
have H':(2+x=2+2) by H.
Abort.

Theorem T: forall x, x=2 -> 2+x=4.
proof.
let x be such that H:(x=2).
then (2+x=2+2).
Abort.

Theorem T: forall x, x=2 -> x + x = x * x.
proof.
let x be such that H:(x=2).
have (4 = 4).
        ~= (2 * 2).
        ~= (x * x) by H.
        =~ (2 + 2).
        =~ H':(x + x) by H.
Abort.

Theorem T: forall x, x + x = x * x -> x = 0 \/ x = 2.
proof.
let x be such that H:(x + x = x * x).
claim H':((x - 2) * x = 0).
thus thesis. 
end claim.
Abort.

Theorem T: forall (A B:Prop), A -> B -> A /\ B.
intros A B HA HB.
proof.
hence B.
Abort.

Theorem T: forall (A B C:Prop), A -> B -> C -> A /\ B /\ C.
intros A B C HA HB HC.
proof.
thus B by HB.
Abort.

Theorem T: forall (A B C:Prop), A -> B -> C -> A /\ B.
intros A B C HA HB HC.
proof.
hence C. (* fails *)
Abort.

Theorem T: forall (A B:Prop), B -> A \/ B.
intros A B HB.
proof.
hence B.
Abort.

Theorem T: forall (A B C D:Prop), C -> D -> (A /\ B) \/ (C /\ D).
intros A B C D HC HD.
proof.
thus C by HC.
Abort.

Theorem T: forall (P:nat -> Prop), P 2 -> exists x,P x.
intros P HP.
proof.
take 2.
Abort.

Theorem T: forall (P:nat -> Prop), P 2 -> exists x,P x.
intros P HP.
proof.
hence (P 2).
Abort.

Theorem T: forall (P:nat -> Prop) (R:nat -> nat -> Prop), P 2 -> R 0 2 -> exists x, exists y, P y /\ R x y.
intros P R HP HR.
proof.
thus (P 2) by HP.
Abort.

Theorem T: forall (A B:Prop) (P:nat -> Prop), (forall x, P x -> B) -> A -> A /\ B.
intros A B P HP HA.
proof.
suffices to have x such that HP':(P x) to show B by HP,HP'.
Abort.

Theorem T: forall (A:Prop) (P:nat -> Prop), P 2 -> A -> A /\ (forall x, x = 2 -> P x).
intros A P HP HA.
proof.
focus on (forall x, x = 2 -> P x).
let x be such that (x = 2).
hence thesis by HP.
end focus.
Abort.

Theorem T: forall x, x = 0 -> x + x = x * x.
proof.
let x be such that H:(x = 0).
define sqr x as (x * x).
reconsider thesis as (x + x = sqr x).
Abort.

Theorem T: forall (P:nat -> Prop), forall x, P x -> P x.
proof.
let P:(nat -> Prop).
let x:nat.
assume HP:(P x).
Abort.

Theorem T: forall (P:nat -> Prop), forall x, P x -> P x.
proof.
let P:(nat -> Prop).
let x. (* fails because x's type is not clear *) 
let x be such that HP:(P x). (* here x's type is inferred from (P x) *)
Abort.

Theorem T: forall (P:nat -> Prop), forall x, P x -> P x -> P x.
proof.
let P:(nat -> Prop).
let x:nat.
assume (P x). (* temporary name created *)
Abort.

Theorem T: forall (P:nat -> Prop), forall x, P x -> P x.
proof.
let P:(nat -> Prop).
let x be such that (P x). (* temporary name created *)
Abort.

Theorem T: forall (P:nat -> Prop) (A:Prop), (exists x, (P x /\ A)) -> A.
proof.
let P:(nat -> Prop),A:Prop be such that H:(exists x, P x /\ A).
consider x such that HP:(P x) and HA:A from H.
Abort.

Here is an example with pairs:

Theorem T: forall p:(nat * nat)%type, (fst p >= snd p) \/ (fst p < snd p).
proof.
let p:(nat * nat)%type.
consider x:nat,y:nat from p.
reconsider thesis as (x >= y \/ x < y). 
Abort.

Theorem T: forall P:(nat -> Prop), (forall n, P n -> P (n - 1)) -> 
(exists m, P m) -> P 0.
proof.
let P:(nat -> Prop) be such that HP:(forall n, P n -> P (n - 1)).
given m such that Hm:(P m).  
Abort.

Theorem T: forall (A B C:Prop), (A -> C) -> (B -> C) -> (A \/ B) -> C.
proof.
let A:Prop,B:Prop,C:Prop be such that HAC:(A -> C) and HBC:(B -> C).
assume HAB:(A \/ B).
per cases on HAB.
suppose A.
  hence thesis by HAC.
suppose HB:B.
  thus thesis by HB,HBC.
end cases.
Abort.

Section Coq.

Hypothesis EM : forall P:Prop, P \/ ~ P.

Theorem T: forall (A C:Prop), (A -> C) -> (~A -> C) -> C.
proof.
let A:Prop,C:Prop be such that HAC:(A -> C) and HNAC:(~A -> C).
per cases of (A \/ ~A) by EM.
suppose (~A).
  hence thesis by HNAC.
suppose A.
  hence thesis by HAC.
end cases.
Abort.

Theorem T: forall (A C:Prop), (A -> C) -> (~A -> C) -> C.
proof.
let A:Prop,C:Prop be such that HAC:(A -> C) and HNAC:(~A -> C).
per cases on (EM A).
suppose (~A).
Abort.
End Coq.

Theorem T: forall (A B:Prop) (x:bool), (if x then A else B) -> A \/ B.
proof.
let A:Prop,B:Prop,x:bool.
per cases on x.
suppose it is true.
  assume A.
  hence A.
suppose it is false.
  assume B.
  hence B.
end cases.
Abort.

Theorem T: forall (n:nat), n + 0 = n.
proof.
let n:nat.
per induction on n.
suppose it is 0.
  thus (0 + 0 = 0).
suppose it is (S m) and H:thesis for m.
  then (S (m + 0) = S m).
  thus =~ (S m + 0).
end induction.
Abort.
