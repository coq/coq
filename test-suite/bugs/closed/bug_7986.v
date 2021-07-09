Inductive Instruction: Set := .

(* The following works: *)
Notation "'RISCV' {{ x ; y ; .. ; z }}" := (@cons Instruction x
  (@cons Instruction y .. (@cons Instruction z nil) ..))
  (format "'RISCV' {{ '[v' '//' x ; '//' y ; '//' .. ; '//' z ']' '//' }}").

(* But if I remove the semicolons, I get
Error: Anomaly "Uncaught exception Failure("List.last")."
Please report at http://coq.inria.fr/bugs/.
 *)
(* This should fail as: "The format does not match the notation." *)
Fail Notation "'RISCV' {{ x  y  ..  z }}" := (@cons Instruction x
  (@cons Instruction y .. (@cons Instruction z nil) ..))
  (format "'RISCV' {{ '[v' '//' x  '//' y  '//' ..  '//' z ']' '//' }}").
