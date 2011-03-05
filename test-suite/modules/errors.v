(* Inductive mismatches *)

Module Type SA. Inductive TA : nat -> Prop := CA : nat -> TA 0. End SA.
Module MA : SA. Inductive TA : Prop := CA : bool -> TA. Fail End MA.

Module Type SA. Inductive TA := CA : nat -> TA. End SA.
Module MA : SA. Inductive TA := CA : bool -> TA. Fail End MA.

Module Type SA. Inductive TA := CA : nat -> TA. End SA.
Module MA : SA. Inductive TA := CA : bool -> nat -> TA. Fail End MA.

Module Type SA2. Inductive TA2 := CA2 : nat -> TA2. End SA2.
Module MA2 : SA2. Inductive TA2 := CA2 : nat -> TA2 | DA2 : TA2. Fail End MA2.

Module Type SA3. Inductive TA3 := CA3 : nat -> TA3. End SA3.
Module MA3 : SA3. Inductive TA3 := CA3 : nat -> TA3 with UA3 := DA3. Fail End MA3.

Module Type SA4. Inductive TA4 := CA4 : nat -> TA4 with UA4 := DA4. End SA4.
Module MA4 : SA4. Inductive TA4 := CA4 : nat -> TA4 with VA4 := DA4. Fail End MA4.

Module Type SA5. Inductive TA5 := CA5 : nat -> TA5 with UA5 := DA5. End SA5.
Module MA5 : SA5. Inductive TA5 := CA5 : nat -> TA5 with UA5 := EA5. Fail End MA5.

Module Type SA6. Inductive TA6 (A:Type) := CA6 : A -> TA6 A. End SA6.
Module MA6 : SA6. Inductive TA6 (A B:Type):= CA6 : A -> TA6 A B. Fail End MA6.

Module Type SA7. Inductive TA7 (A:Type) := CA7 : A -> TA7 A. End SA7.
Module MA7 : SA7. CoInductive TA7 (A:Type):= CA7 : A -> TA7 A. Fail End MA7.

Module Type SA8. CoInductive TA8 (A:Type) := CA8 : A -> TA8 A. End SA8.
Module MA8 : SA8. Inductive TA8 (A:Type):= CA8 : A -> TA8 A. Fail End MA8.

Module Type SA9. Record TA9 (A:Type) := { CA9 : A }. End SA9.
Module MA9 : SA9. Inductive TA9 (A:Type):= CA9 : A -> TA9 A. Fail End MA9.

Module Type SA10. Inductive TA10 (A:Type) := CA10 : A -> TA10 A. End SA10.
Module MA10 : SA10. Record TA10 (A:Type):= { CA10 : A }. Fail End MA10.

Module Type SA11. Record TA11 (A:Type):= { CA11 : A }. End SA11.
Module MA11 : SA11. Record TA11 (A:Type):= { DA11 : A }. Fail End MA11.

(* Basic mismatches *)
Module Type SB. Inductive TB := CB : nat -> TB. End SB.
Module MB : SB. Module Type TB. End TB. Fail End MB.

Module Type SC. Module Type TC. End TC. End SC.
Module MC : SC. Inductive TC := CC : nat -> TC. Fail End MC.

Module Type SD. Module TD. End TD. End SD.
Module MD : SD. Inductive TD := DD : nat -> TD. Fail End MD.

Module Type SE. Definition DE := nat. End SE.
Module ME : SE. Definition DE := bool. Fail End ME.

Module Type SF. Parameter DF : nat. End SF.
Module MF : SF. Definition DF := bool. Fail End MF.

(* Needs a type constraint in module type *)
Module Type SG. Definition DG := Type. End SG.
Module MG : SG. Definition DG := Type : Type. Fail End MG.

(* Should work *)
Module Type SA7. Inductive TA7 (A:Type) := CA7 : A -> TA7 A. End SA7.
Module MA7 : SA7. Inductive TA7 (B:Type):= CA7 : B -> TA7 B. End MA7.

Module Type SA11. Record TA11 (B:Type):= { CA11 : B }. End SA11.
Module MA11 : SA11. Record TA11 (A:Type):= { CA11 : A }. End MA11.

Module Type SE. Parameter DE : Type. End SE.
Module ME : SE. Definition DE := Type : Type. End ME.
