(* coq-prog-args: ("-impredicative-set") *)
(* Inductive mismatches *)

Module Type SA. Inductive TA : nat -> Prop := CA : nat -> TA 0. End SA.
Module MA : SA. Inductive TA : Prop := CA : bool -> TA. Fail End MA.
Reset Initial.

Module Type SA0. Inductive TA0 := CA0 : nat -> TA0. End SA0.
Module MA0 : SA0. Inductive TA0 := CA0 : bool -> TA0. Fail End MA0.
Reset Initial.

Module Type SA1. Inductive TA1 := CA1 : nat -> TA1. End SA1.
Module MA1 : SA1. Inductive TA1 := CA1 : bool -> nat -> TA1. Fail End MA1.
Reset Initial.

Module Type SA2. Inductive TA2 := CA2 : nat -> TA2. End SA2.
Module MA2 : SA2. Inductive TA2 := CA2 : nat -> TA2 | DA2 : TA2. Fail End MA2.
Reset Initial.

Module Type SA3. Inductive TA3 := CA3 : nat -> TA3. End SA3.
Module MA3 : SA3. Inductive TA3 := CA3 : nat -> TA3 with UA3 := DA3. Fail End MA3.
Reset Initial.

Module Type SA4. Inductive TA4 := CA4 : nat -> TA4 with UA4 := DA4. End SA4.
Module MA4 : SA4. Inductive TA4 := CA4 : nat -> TA4 with VA4 := DA4. Fail End MA4.
Reset Initial.

Module Type SA5. Inductive TA5 := CA5 : nat -> TA5 with UA5 := DA5. End SA5.
Module MA5 : SA5. Inductive TA5 := CA5 : nat -> TA5 with UA5 := EA5. Fail End MA5.
Reset Initial.

Module Type SA6. Inductive TA6 (A:Type) := CA6 : A -> TA6 A. End SA6.
Module MA6 : SA6. Inductive TA6 (A B:Type):= CA6 : A -> TA6 A B. Fail End MA6.
Reset Initial.

Module Type SA7. Inductive TA7 (A:Type) := CA7 : A -> TA7 A. End SA7.
Module MA7 : SA7. CoInductive TA7 (A:Type):= CA7 : A -> TA7 A. Fail End MA7.
Reset Initial.

Module Type SA8. CoInductive TA8 (A:Type) := CA8 : A -> TA8 A. End SA8.
Module MA8 : SA8. Inductive TA8 (A:Type):= CA8 : A -> TA8 A. Fail End MA8.
Reset Initial.

Module Type SA9. Record TA9 (A:Type) := { CA9 : A }. End SA9.
Module MA9 : SA9. Inductive TA9 (A:Type):= CA9 : A -> TA9 A. Fail End MA9.
Reset Initial.

Module Type SA10. Inductive TA10 (A:Type) := CA10 : A -> TA10 A. End SA10.
Module MA10 : SA10. Record TA10 (A:Type):= { CA10 : A }. Fail End MA10.
Reset Initial.

Module Type SA11. Record TA11 (A:Type):= { CA11 : A }. End SA11.
Module MA11 : SA11. Record TA11 (A:Type):= { DA11 : A }. Fail End MA11.
Reset Initial.

(* Basic mismatches *)
Module Type SB. Inductive TB := CB : nat -> TB. End SB.
Module MB : SB. Module Type TB. End TB. Fail End MB.
Inductive TB := CB : nat -> TB. End MB.

Module Type SC. Module Type TC. End TC. End SC.
Module MC : SC. Inductive TC := CC : nat -> TC. Fail End MC.
Reset Initial.

Module Type SD. Module TD. End TD. End SD.
Module MD : SD. Inductive TD := DD : nat -> TD. Fail End MD.
Reset Initial.

Module Type SE. Definition DE := nat. End SE.
Module ME : SE. Definition DE := bool. Fail End ME.
Reset Initial.

Module Type SF. Parameter DF : nat. End SF.
Module MF : SF. Definition DF := bool. Fail End MF.
Reset Initial.

(* Needs a type constraint in module type *)
Module Type SG. Definition DG := Type. End SG.
Module MG : SG. Definition DG := Type : Type. Fail End MG.
Reset Initial.

(* Should work *)
Module Type SA70. Inductive TA70 (A:Type) := CA70 : A -> TA70 A. End SA70.
Module MA70 : SA70. Inductive TA70 (B:Type):= CA70 : B -> TA70 B. End MA70.

Module Type SA12. Record TA12 (B:Type):= { CA12 : B }. End SA12.
Module MA12 : SA12. Record TA12 (A:Type):= { CA12 : A }. End MA12.

Module Type SH. Parameter DH : Type. End SH.
Module MH : SH. Definition DH := Type : Type. End MH.
