type pref =
    {
      mutable cmd_coqc : string;
      mutable cmd_coqmakefile : string;
      mutable cmd_coqdoc : string;

      mutable global_auto_revert : bool;
      mutable global_auto_revert_delay : float;

      mutable auto_save : bool;
      mutable auto_save_delay : float;
      mutable auto_save_name : string*string;

      mutable automatic_tactics : string * string list;
      mutable cmd_print : string;

      mutable modifier_for_navigation : Gdk.Tags.modifier list;
      mutable modifier_for_templates : Gdk.Tags.modifier list;
      

    }


let (current:pref) = 
  {
    cmd_coqc = "coqc";
    cmd_coqmakefile = "coqmakefile";
    cmd_coqdoc = "coqdoc";
    cmd_print = "lpr";
    

    global_auto_revert = false;
    global_auto_revert_delay = 1.;
    
    auto_save = false;
    auto_save_delay = 1.;
    auto_save_name = "#","#";

    automatic_tactics = [];
    
    modifier_for_navigation = [`CONTROL; `MOD1];
    modifier_for_templates = [`MOD1];
  }
