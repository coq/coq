Require Import ZArith.

Definition zeq := Z.eq_dec.

Definition update (A: Set) (x: Z) (v: A) (s: Z -> A) : Z -> A :=
 fun y => if zeq x y then v else s y.

Arguments update [A].

Definition ident := Z.
Parameter operator: Set.
Parameter value: Set.
Parameter is_true: value -> Prop.
Definition label := Z.

Inductive expr : Set :=
 | Evar: ident -> expr
 | Econst: value -> expr
 | Eop: operator -> expr -> expr -> expr.

Inductive stmt : Set :=
 | Sskip: stmt
 | Sassign: ident -> expr -> stmt
 | Scall: ident -> ident -> expr -> stmt (* x := f(e) *)
 | Sreturn: expr -> stmt
 | Sseq: stmt -> stmt -> stmt
 | Sifthenelse: expr -> stmt -> stmt -> stmt
 | Sloop: stmt -> stmt
 | Sblock: stmt -> stmt
 | Sexit: nat -> stmt
 | Slabel: label -> stmt -> stmt
 | Sgoto: label -> stmt.

Record function : Set := mkfunction {
 fn_param: ident;
 fn_body: stmt
}.

Parameter program: ident -> option function.

Parameter main_function: ident.

Definition store := ident -> value.

Parameter empty_store : store.

Parameter eval_op: operator -> value -> value -> option value.

Fixpoint eval_expr (st: store) (e: expr) {struct e} : option value :=
 match e with
 | Evar v => Some (st v)
 | Econst v => Some v
 | Eop op e1 e2 =>
     match eval_expr st e1, eval_expr st e2 with
     | Some v1, Some v2 => eval_op op v1 v2
     | _, _ => None
     end
 end.

Inductive outcome: Set :=
 | Onormal: outcome
 | Oexit: nat -> outcome
 | Ogoto: label -> outcome
 | Oreturn: value -> outcome.

Definition outcome_block (out: outcome) : outcome :=
 match out with
 | Onormal => Onormal
 | Oexit O => Onormal
 | Oexit (S m) => Oexit m
 | Ogoto lbl => Ogoto lbl
 | Oreturn v => Oreturn v
 end.

Fixpoint label_defined (lbl: label) (s: stmt) {struct s}: Prop :=
 match s with
 | Sskip => False
 | Sassign id e => False
 | Scall id fn e => False
 | Sreturn e => False
 | Sseq s1 s2 => label_defined lbl s1 \/ label_defined lbl s2
 | Sifthenelse e s1 s2 => label_defined lbl s1 \/ label_defined lbl s2
 | Sloop s1 => label_defined lbl s1
 | Sblock s1 => label_defined lbl s1
 | Sexit n => False
 | Slabel lbl1 s1 => lbl1 = lbl \/ label_defined lbl s1
 | Sgoto lbl => False
 end.

Inductive exec : stmt -> store -> outcome -> store -> Prop :=
 | exec_skip: forall st,
     exec Sskip st Onormal st
 | exec_assign: forall id e st v,
     eval_expr st e = Some v ->
     exec (Sassign id e) st Onormal (update id v st)
 | exec_call: forall id fn e st v1 f v2 st',
     eval_expr st e = Some v1 ->
     program fn = Some f ->
     exec_function f (update f.(fn_param) v1 empty_store) v2 st' ->
     exec (Scall id fn e) st Onormal (update id v2 st)
 | exec_return: forall e st v,
     eval_expr st e = Some v ->
     exec (Sreturn e) st (Oreturn v) st
 | exec_seq_2: forall s1 s2 st st1 out' st',
     exec s1 st Onormal st1 -> exec s2 st1 out' st' ->
     exec (Sseq s1 s2) st out' st'
 | exec_seq_1: forall s1 s2 st out st',
     exec s1 st out st' -> out <> Onormal ->
     exec (Sseq s1 s2) st out st'
 | exec_ifthenelse_true: forall e s1 s2 st out st' v,
     eval_expr st e = Some v -> is_true v -> exec s1 st out st' ->
     exec (Sifthenelse e s1 s2) st out st'
 | exec_ifthenelse_false: forall e s1 s2 st out st' v,
     eval_expr st e = Some v -> ~is_true v -> exec s2 st out st' ->
     exec (Sifthenelse e s1 s2) st out st'
 | exec_loop_loop: forall s st st1 out' st',
     exec s st Onormal st1 ->
     exec (Sloop s) st1 out' st' ->
     exec (Sloop s) st out' st'
 | exec_loop_stop: forall s st st' out,
     exec s st out st' -> out <> Onormal ->
     exec (Sloop s) st out st'
 | exec_block: forall s st out st',
     exec s st out st' ->
     exec (Sblock s) st (outcome_block out) st'
 | exec_exit: forall n st,
     exec (Sexit n) st (Oexit n) st
 | exec_label: forall s lbl st st' out,
     exec s st out st' ->
     exec (Slabel lbl s) st out st'
 | exec_goto: forall st lbl,
     exec (Sgoto lbl) st (Ogoto lbl) st

(** [execg lbl stmt st out st'] starts executing at label [lbl] within [s],
   in initial store [st].  The result of the execution is the outcome
   [out] with final store [st']. *)

with execg: label -> stmt -> store -> outcome -> store -> Prop :=
 | execg_left_seq_2: forall lbl s1 s2 st st1 out' st',
     execg lbl s1 st Onormal st1 -> exec s2 st1 out' st' ->
     execg lbl (Sseq s1 s2) st out' st'
 | execg_left_seq_1: forall lbl s1 s2 st out st',
     execg lbl s1 st out st' -> out <> Onormal ->
     execg lbl (Sseq s1 s2) st out st'
 | execg_right_seq: forall lbl s1 s2 st out st',
     ~(label_defined lbl s1) ->
     execg lbl s2 st out st' ->
     execg lbl (Sseq s1 s2) st out st'
 | execg_ifthenelse_left: forall lbl e s1 s2 st out st',
     execg lbl s1 st out st' ->
     execg lbl (Sifthenelse e s1 s2) st out st'
 | execg_ifthenelse_right: forall lbl e s1 s2 st out st',
     ~(label_defined lbl s1) ->
     execg lbl s2 st out st' ->
     execg lbl (Sifthenelse e s1 s2) st out st'
 | execg_loop_loop: forall lbl s st st1 out' st',
     execg lbl s st Onormal st1 ->
     exec (Sloop s) st1 out' st' ->
     execg lbl (Sloop s) st out' st'
 | execg_loop_stop: forall lbl s st st' out,
     execg lbl s st out st' -> out <> Onormal ->
     execg lbl (Sloop s) st out st'
 | execg_block: forall lbl s st out st',
     execg lbl s st out st' ->
     execg lbl (Sblock s) st (outcome_block out) st'
 | execg_label_found: forall lbl s st st' out,
     exec s st out st' ->
     execg lbl (Slabel lbl s) st out st'
 | execg_label_notfound: forall lbl s lbl' st st' out,
     lbl' <> lbl ->
     execg lbl s st out st' ->
     execg lbl (Slabel lbl' s) st out st'

(** [exec_finish out st st'] takes the outcome [out] and the store [st]
 at the end of the evaluation of the program.  If [out] is a [goto],
 execute again the program starting at the corresponding label.
 Iterate this way until [out] is [Onormal]. *)

with exec_finish: function -> outcome -> store -> value -> store -> Prop :=
 | exec_finish_normal: forall f st v,
     exec_finish f (Oreturn v) st v st
 | exec_finish_goto: forall f lbl st out v st1 st',
     execg lbl f.(fn_body) st out st1 ->
     exec_finish f out st1 v st' ->
     exec_finish f (Ogoto lbl) st v st'

(** Execution of a function *)

with exec_function: function -> store -> value -> store -> Prop :=
 | exec_function_intro: forall f st out st1 v st',
     exec f.(fn_body) st out st1 ->
     exec_finish f out st1 v st' ->
     exec_function f st v st'.

Scheme exec_ind4:= Minimality for exec Sort Prop
 with execg_ind4:= Minimality for execg Sort Prop
 with exec_finish_ind4 := Minimality for exec_finish Sort Prop
 with exec_function_ind4 := Minimality for exec_function Sort Prop.

Scheme exec_dind4:= Induction for exec Sort Prop
 with execg_dind4:= Minimality for execg Sort Prop
 with exec_finish_dind4 := Induction for exec_finish Sort Prop
 with exec_function_dind4 := Induction for exec_function Sort Prop.

Combined Scheme exec_inductiond from exec_dind4, execg_dind4, exec_finish_dind4,
  exec_function_dind4.

Scheme exec_dind4' := Induction for exec Sort Prop
 with execg_dind4' := Induction for execg Sort Prop
 with exec_finish_dind4' := Induction for exec_finish Sort Prop
 with exec_function_dind4' := Induction for exec_function Sort Prop.

Combined Scheme exec_induction from exec_ind4, execg_ind4, exec_finish_ind4,
  exec_function_ind4.

Combined Scheme exec_inductiond' from exec_dind4', execg_dind4', exec_finish_dind4',
  exec_function_dind4'.
