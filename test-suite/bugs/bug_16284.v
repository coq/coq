Primitive int := #int63_type.

Primitive lsl := #int63_lsl.

Eval cbv in fun x => lsl x.
(* at some point produced anomaly List.chop *)

Eval cbn in fun x => lsl x.
Eval lazy in fun x => lsl x.
Eval vm_compute in fun x => lsl x.
Eval native_compute in fun x => lsl x.
