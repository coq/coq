type pref =
    {
      mutable cmd_coqc : string;
      mutable cmd_coqmakefile : string;
      mutable cmd_coqdoc : string;
      mutable global_auto_revert : bool;
      mutable global_auto_revert_delay : float;
      mutable auto_save : bool;
      mutable auto_save_delay : float;
      mutable automatic_tactics : string * string list;
      mutable cmd_print : string
    }
