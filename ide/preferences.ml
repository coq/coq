type pref =
    {
      mutable cmd_coqc : string;
      mutable cmd_make : string;
      mutable cmd_coqmakefile : string;
      mutable cmd_coqdoc : string;

      mutable global_auto_revert : bool;
      mutable global_auto_revert_delay : float;

      mutable auto_save : bool;
      mutable auto_save_delay : float;
      mutable auto_save_name : string*string;

      mutable automatic_tactics : (string * string) list;
      mutable cmd_print : string;

      mutable modifier_for_navigation : Gdk.Tags.modifier list;
      mutable modifier_for_templates : Gdk.Tags.modifier list;
      
      mutable cmd_browse : string * string;

      mutable doc_url : string;
      mutable library_url : string;
    }


let (current:pref) = 
  {
    cmd_coqc = "coqc";
    cmd_make = "make";
    cmd_coqmakefile = "coq_makefile -o Makefile *.v";
    cmd_coqdoc = "coqdoc -q -g";
    cmd_print = "lpr";
    

    global_auto_revert = false;
    global_auto_revert_delay = 1.;
    
    auto_save = false;
    auto_save_delay = 1.;
    auto_save_name = "#","#";

    automatic_tactics = [];
    
    modifier_for_navigation = [`CONTROL; `MOD1];
    modifier_for_templates = [`MOD1];
    
    cmd_browse = "netscape -remote \"OpenURL(", ")\"";

    doc_url = "http://coq.inria.fr/doc/";
    library_url = "http://coq.inria.fr/library/";
 }
