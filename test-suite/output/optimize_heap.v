(* optimize_heap should not affect the proof state *)

Goal True.
  idtac.
  Show.
  optimize_heap.
  Show.
