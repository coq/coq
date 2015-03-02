
open Decl_expr
open Pptactic

val pr_gen_proof_instr : 
  ('var -> Pp.std_ppcmds) ->
  ('constr -> Pp.std_ppcmds) ->
  ('pat -> Pp.std_ppcmds) ->
  ('tac -> Pp.std_ppcmds) ->  
  ('var,'constr,'pat,'tac) gen_proof_instr -> Pp.std_ppcmds

val pr_raw_proof_instr : raw_proof_instr raw_extra_genarg_printer
val pr_glob_proof_instr : glob_proof_instr glob_extra_genarg_printer
val pr_proof_instr : proof_instr extra_genarg_printer
