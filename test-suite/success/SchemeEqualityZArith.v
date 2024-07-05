(* An example from fiat_crypto which fails for two reasons:
   - parameters of the form [Type * Type] are not yet supported
   - Prop arguments are not supported *)
Require Import ZArith.
Module M.

Fixpoint tuple' T n : Type :=
  match n with
  | O => T
  | S n' => (tuple' T n' * T)%type
  end.

Definition tuple T n : Type :=
  match n with
  | O => unit
  | S n' => tuple' T n'
  end.

Definition reg_state := tuple Z 16.

Definition flag_state := tuple (option bool) 6.

Class parameters := {
  param_key : Type;
  param_value : Type;
  param_ltb : param_key -> param_key -> bool
}.

Axiom sorted : forall {p : parameters}, list (param_key * param_value) -> bool.

Record rep (p : parameters) := {
  value : list (param_key * param_value);
  _value_ok : sorted value = true
}.

Record word (width : Z) := {
  word_rep : Type;
  word_ltu : word_rep -> word_rep -> bool;
}.

Open Scope Z_scope.

Record naive_rep width := {
  unsigned : Z ;
  _unsigned_in_range : unsigned mod (2^width) = unsigned
}.

Definition naive width : word width := {|
  word_rep := naive_rep width;
  word_ltu x y := Z.ltb (unsigned _ x) (unsigned _ y);
|}.

Definition SortedList_parameters {width} (w:word width) value : parameters := {|
  param_value := value;
  param_key := word_rep _ w;
  param_ltb := word_ltu _ w
|}.

Definition mem_state := rep (SortedList_parameters (naive 64) Z).

Record machine_state := { machine_reg_state :> reg_state ; machine_flag_state :> flag_state ; machine_mem_state :> mem_state }.

(* Should succeed! *)
Fail Scheme Boolean Equality for machine_state.

End M.
