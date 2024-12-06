Module map.
  Class map {value} := mk {
    rep : Type;
    get: rep -> option value;
    empty : rep;
    put : rep -> value -> rep;
  }.
  Arguments map : clear implicits.
  Class ok {value : Type} {map : map value}: Prop := {
    get_put_diff : forall m v, get (put m v) = None;
  }.
  Arguments ok {_} _.

End map.

Axiom wordX : Set.
Axiom e : wordX.

Section Equiv.

Context {Registers: map.map wordX}
        {mem: map.map Corelib.Init.Byte.byte}.

Context (Registers_ok: @map.ok wordX Registers)
        (mem_ok: @map.ok Byte.byte mem).

(** Check that cleared variables are correctly handled *)
Goal map.get (map.put map.empty e) = None.
Proof.
clear -Registers_ok.
apply map.get_put_diff.
Qed.

End Equiv.
