(* Test pattern with dependent occurrences; Note that it does not
   behave as the succession of three generalize because each
   quantification introduces new occurrences that are automatically
   abstracted with the numbering still based on the original statement *)

Goal (id true,id false)=(id true,id true).
generalize bool at 2 4 6 8 10 as B, true at 3 as tt, false as ff.
