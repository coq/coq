(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Some programs and results about lists following CAML Manual *)

Require Export PolyList.
Set Implicit Arguments.
Chapter Lists.

Variable  A : Set.

(**********************)
(** The null function *)
(**********************)

Definition Isnil : (list A) -> Prop := [l:(list A)](nil A)=l.

Lemma Isnil_nil : (Isnil (nil A)).
Red; Auto.
Qed.
Hints Resolve Isnil_nil.

Lemma not_Isnil_cons : (a:A)(l:(list A))~(Isnil (cons a l)).
Unfold Isnil.
Intros; Discriminate.
Qed.

Hints Resolve Isnil_nil not_Isnil_cons.

Lemma Isnil_dec : (l:(list A)){(Isnil l)}+{~(Isnil l)}.
Intro l; Case l;Auto.
(*
Realizer (fun l => match l with
  | nil => true
  | _ => false
  end).
*)
Qed.

(************************)
(** The Uncons function *)
(************************)

Lemma Uncons : (l:(list A)){a : A & { m: (list A) | (cons a m)=l}}+{Isnil l}.
Intro l; Case l.
Auto.
Intros a m; Intros; Left; Exists a; Exists m; Reflexivity.
(*
Realizer (fun l => match l with
  | nil => error
  | (cons a m) => value (a,m)
  end).
*)
Qed.

(********************************)
(** The head function           *)
(********************************)

Lemma Hd : (l:(list A)){a : A | (EX m:(list A) |(cons a m)=l)}+{Isnil l}.
Intro l; Case l.
Auto.
Intros a m; Intros; Left; Exists a; Exists m; Reflexivity.
(*
Realizer (fun l => match l with
  | nil => error
  | (cons a m) => value a
  end).
*)
Qed.

Lemma Tl : (l:(list A)){m:(list A)| (EX a:A |(cons a m)=l)
                         \/ ((Isnil l) /\ (Isnil m)) }.
Intro l; Case l.
Exists (nil A); Auto.
Intros a m; Intros; Exists m; Left; Exists a; Reflexivity.
(*
Realizer (fun l => match l with
  | nil => nil
  | (cons a m) => m
  end).
*)
Qed.

(****************************************)
(** Length of lists                     *)
(****************************************)

(* length is defined in List *)
Fixpoint Length_l [l:(list A)] : nat -> nat 
  :=  [n:nat] Cases l of
                  nil => n
              | (cons _ m) => (Length_l m (S n))
	     end.

(* A tail recursive version *)
Lemma Length_l_pf : (l:(list A))(n:nat){m:nat|(plus n (length l))=m}.
NewInduction l as [|a m lrec].
Intro n; Exists n; Simpl; Auto.
Intro n; Elim (lrec (S n)); Simpl; Intros.
Exists x; Transitivity (S (plus n (length m))); Auto.
(*
Realizer Length_l.
*)
Qed.

Lemma Length : (l:(list A)){m:nat|(length l)=m}.
Intro l. Apply (Length_l_pf l O).
(*
Realizer (fun l -> Length_l_pf l O).
*)
Qed.

(*******************************)
(** Members of lists           *)
(*******************************)
Inductive In_spec [a:A] : (list A) -> Prop := 
   | in_hd : (l:(list A))(In_spec a (cons a l))
   | in_tl : (l:(list A))(b:A)(In a l)->(In_spec a (cons b l)).
Hints Resolve in_hd in_tl.
Hints Unfold  In.
Hints Resolve in_cons.

Theorem In_In_spec : (a:A)(l:(list A))(In a l) <-> (In_spec a l).
Split.
Elim l; [ Intros; Contradiction 
      	| Intros; Elim H0; 
	  [ Intros; Rewrite H1; Auto
	  | Auto ]].
Intros; Elim H; Auto.
Qed.

Inductive AllS [P:A->Prop] : (list A) -> Prop 
   := allS_nil : (AllS P (nil A))
   | allS_cons : (a:A)(l:(list A))(P a)->(AllS P l)->(AllS P (cons a l)).
Hints Resolve allS_nil allS_cons.

Hypothesis eqA_dec : (a,b:A){a=b}+{~a=b}.

Fixpoint mem [a:A; l:(list A)] : bool :=
  Cases l of
    nil => false
  | (cons b m) => if (eqA_dec a b) then [H]true else [H](mem a m)
  end.

Hints Unfold  In.
Lemma Mem : (a:A)(l:(list A)){(In a l)}+{(AllS [b:A]~b=a l)}.
Intros a l.
NewInduction l.
Auto.
Elim (eqA_dec a a0).
Auto.
Simpl. Elim IHl; Auto.
(*
Realizer mem.
*)
Qed.

(*********************************)
(** Index of elements            *)
(*********************************)

Require Le.
Require Lt.

Inductive nth_spec : (list A)->nat->A->Prop :=
  nth_spec_O : (a:A)(l:(list A))(nth_spec (cons a l) (S O) a)
| nth_spec_S : (n:nat)(a,b:A)(l:(list A))
           (nth_spec l n a)->(nth_spec (cons b l) (S n) a).
Hints Resolve nth_spec_O nth_spec_S.

Inductive fst_nth_spec : (list A)->nat->A->Prop :=
  fst_nth_O : (a:A)(l:(list A))(fst_nth_spec (cons a l) (S O) a)
| fst_nth_S : (n:nat)(a,b:A)(l:(list A))(~a=b)->
           (fst_nth_spec l n a)->(fst_nth_spec (cons b l) (S n) a).
Hints Resolve fst_nth_O fst_nth_S.

Lemma fst_nth_nth : (l:(list A))(n:nat)(a:A)(fst_nth_spec l n a)->(nth_spec l n a).
NewInduction 1; Auto.
Qed.
Hints Immediate fst_nth_nth.

Lemma nth_lt_O : (l:(list A))(n:nat)(a:A)(nth_spec l n a)->(lt O n).
NewInduction 1; Auto.
Qed.

Lemma nth_le_length : (l:(list A))(n:nat)(a:A)(nth_spec l n a)->(le n (length l)).
NewInduction 1; Simpl; Auto with arith.
Qed.

Fixpoint Nth_func [l:(list A)] : nat -> (Exc A) 
  := [n:nat] Cases  l  n  of 
               (cons a _)  (S O)       => (value A a) 
             | (cons _ l') (S (S p)) => (Nth_func l' (S p))
             |  _ _      => Error
            end.

Lemma Nth : (l:(list A))(n:nat)
            {a:A|(nth_spec l n a)}+{(n=O)\/(lt (length l) n)}.
NewInduction l as [|a l IHl].
Intro n; Case n; Simpl; Auto with arith.
Intro n; NewDestruct n as [|[|n1]]; Simpl; Auto.
Left; Exists a; Auto.
NewDestruct (IHl (S n1)) as [[b]|o].
Left; Exists b; Auto.
Right; NewDestruct o.
Absurd (S n1)=O; Auto.
Auto with arith.
(*
Realizer Nth_func.
*)
Qed.

Lemma Item : (l:(list A))(n:nat){a:A|(nth_spec l (S n) a)}+{(le (length l) n)}.
Intros l n; Case (Nth l (S n)); Intro.
Case s; Intro a; Left; Exists a; Auto.
Right; Case o; Intro.
Absurd (S n)=O; Auto.
Auto with arith.
Qed.

Require Minus.
Require DecBool.

Fixpoint index_p [a:A;l:(list A)] : nat -> (Exc nat) := 
   Cases l of nil => [p]Error
     | (cons b m) => [p](ifdec (eqA_dec a b) (Value p) (index_p a m (S p)))
   end.

Lemma Index_p : (a:A)(l:(list A))(p:nat)
     {n:nat|(fst_nth_spec l (minus (S n) p) a)}+{(AllS [b:A]~a=b l)}.
NewInduction l as [|b m irec].
Auto.
Intro p.
NewDestruct (eqA_dec a b) as [e|e].
Left; Exists p.
NewDestruct e; Elim minus_Sn_m; Trivial; Elim minus_n_n; Auto with arith.
NewDestruct (irec (S p)) as [[n H]|].
Left; Exists n; Auto with arith.
Elim minus_Sn_m; Auto with arith.
Apply lt_le_weak; Apply lt_O_minus_lt; Apply nth_lt_O with m a; Auto with arith.
Auto.
Qed.

Lemma Index : (a:A)(l:(list A))
     {n:nat|(fst_nth_spec l n a)}+{(AllS [b:A]~a=b l)}.

Intros a l; Case (Index_p a l (S O)); Auto.
Intros (n,P); Left; Exists n; Auto.
Rewrite (minus_n_O n); Trivial.
(*
Realizer (fun a l -> Index_p a l (S O)).
*)
Qed.

Section Find_sec.
Variable R,P : A -> Prop.

Inductive InR : (list A) -> Prop 
   := inR_hd : (a:A)(l:(list A))(R a)->(InR (cons a l))
   | inR_tl : (a:A)(l:(list A))(InR l)->(InR (cons a l)).
Hints Resolve inR_hd inR_tl.

Definition InR_inv := 
       [l:(list A)]Cases l of 
                   nil => False 
                | (cons b m) => (R b)\/(InR m) 
               end.

Lemma InR_INV : (l:(list A))(InR l)->(InR_inv l).
NewInduction 1; Simpl; Auto.
Qed.

Lemma InR_cons_inv : (a:A)(l:(list A))(InR (cons a l))->((R a)\/(InR l)).
Intros a l H; Exact (InR_INV H).
Qed.

Lemma InR_or_app : (l,m:(list A))((InR l)\/(InR m))->(InR (app l m)).
Intros l m [|].
NewInduction 1; Simpl; Auto.
Intro. NewInduction l; Simpl; Auto.
Qed.

Lemma InR_app_or : (l,m:(list A))(InR (app l m))->((InR l)\/(InR m)).
Intros l m; Elim l; Simpl; Auto.
Intros b l' Hrec IAc; Elim (InR_cons_inv IAc);Auto.
Intros; Elim Hrec; Auto.
Qed.

Hypothesis RS_dec : (a:A){(R a)}+{(P a)}.

Fixpoint find [l:(list A)] : (Exc A) := 
	Cases l of nil => Error
                | (cons a m) => (ifdec (RS_dec a) (Value a) (find m))
        end.

Lemma Find : (l:(list A)){a:A | (In a l) & (R a)}+{(AllS P l)}.
NewInduction l as [|a m [[b H1 H2]|H]]; Auto.
Left; Exists b; Auto.
NewDestruct (RS_dec a).
Left; Exists a; Auto.
Auto.
(*
Realizer find.
*)
Qed.

Variable B : Set.
Variable T : A -> B -> Prop.

Variable TS_dec : (a:A){c:B| (T a c)}+{(P a)}.

Fixpoint try_find [l:(list A)] : (Exc B) :=
   Cases l of
     nil => Error
   | (cons a l1) =>
	   Cases (TS_dec a) of
	     (inleft (exist c _)) => (Value c)
	   | (inright _) => (try_find l1)
	   end
   end.

Lemma Try_find : (l:(list A)){c:B|(EX a:A |(In a l) & (T a c))}+{(AllS P l)}.
NewInduction l as [|a m [[b H1]|H]].
Auto.
Left; Exists b; NewDestruct H1 as [a' H2 H3]; Exists a'; Auto.
NewDestruct (TS_dec a) as [[c H1]|].
Left; Exists c.
Exists a; Auto.
Auto.
(* 
Realizer try_find.
*)
Qed.

End Find_sec.

Section Assoc_sec.

Variable B : Set.
Fixpoint assoc [a:A;l:(list A*B)] : (Exc B) :=
    Cases l of        nil => Error
        | (cons (a',b) m) => (ifdec (eqA_dec a a') (Value b) (assoc a m))
    end.

Inductive AllS_assoc [P:A -> Prop]: (list A*B) -> Prop := 
      allS_assoc_nil : (AllS_assoc P (nil A*B))
    | allS_assoc_cons : (a:A)(b:B)(l:(list A*B))
        (P a)->(AllS_assoc P l)->(AllS_assoc P (cons (a,b) l)).

Hints Resolve allS_assoc_nil allS_assoc_cons.

(* The specification seems too weak: it is enough to return b if the
   list has at least an element (a,b); probably the intention is to have
   the specification

   (a:A)(l:(list A*B)){b:B|(In_spec (a,b) l)}+{(AllS_assoc [a':A]~(a=a') l)}.
*)

Lemma Assoc : (a:A)(l:(list A*B))(B+{(AllS_assoc [a':A]~(a=a') l)}).
NewInduction l as [|[a' b] m assrec]. Auto.
NewDestruct (eqA_dec a a').
Left; Exact b.
NewDestruct assrec as [b'|].
Left; Exact b'.
Right; Auto.
(*
Realizer assoc.
*)
Qed.

End Assoc_sec.

End Lists.

Hints Resolve Isnil_nil not_Isnil_cons in_hd in_tl in_cons allS_nil allS_cons 
 : datatypes.
Hints Immediate fst_nth_nth : datatypes.

