
type vernac_toplevel =
    VernacBackTo of int
  | VernacDrop
  | VernacQuit
  | VernacControl of Vernacexpr.vernac_control
  | VernacShowGoal of { gid : int; sid : int; }
  | VernacShowProofDiffs of Proof_diffs.diffOpt

val err : unit -> 'a

val test_show_goal : unit Procq.Entry.t

val vernac_toplevel :
  Pvernac.proof_mode option -> vernac_toplevel option Procq.Entry.t
