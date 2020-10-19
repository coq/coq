(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Goptions

let allow_sprop_opt_name = ["Allow";"StrictProp"]
let cumul_sprop_opt_name = ["Cumulative";"StrictProp"]

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = allow_sprop_opt_name;
      optread  = (fun () -> Global.sprop_allowed());
      optwrite = Global.set_allow_sprop }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = cumul_sprop_opt_name;
      optread  = Global.is_cumulative_sprop;
      optwrite = Global.set_cumulative_sprop }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Silent"];
      optread  = (fun () -> !Flags.quiet);
      optwrite = ((:=) Flags.quiet) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Parentheses"];
      optread  = (fun () -> !Constrextern.print_parentheses);
      optwrite = (fun b ->  Constrextern.print_parentheses := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Detyping.print_evar_arguments);
      optwrite = (:=) Detyping.print_evar_arguments }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let () =
  declare_int_option
    { optdepr  = false;
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
                   let lev = Option.default Flags.default_inline_level o in
                   Flags.set_inline_level lev) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Kernel"; "Term"; "Sharing"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.share_reduction);
      optwrite = Global.set_share_reduction }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Compact";"Contexts"];
      optread  = (fun () -> Printer.get_compact_context());
      optwrite = (fun b -> Printer.set_compact_context b) }

let () =
  declare_int_option
    { optdepr  = false;
      optkey   = ["Printing";"Depth"];
      optread  = Topfmt.get_depth_boxes;
      optwrite = Topfmt.set_depth_boxes }

let () =
  declare_int_option
    { optdepr  = false;
      optkey   = ["Printing";"Width"];
      optread  = Topfmt.get_margin;
      optwrite = Topfmt.set_margin }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Dump";"Bytecode"];
      optread  = (fun () -> !Vmbytegen.dump_bytecode);
      optwrite = (:=) Vmbytegen.dump_bytecode }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Dump";"Lambda"];
      optread  = (fun () -> !Vmlambda.dump_lambda);
      optwrite = (:=) Vmlambda.dump_lambda }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let () =
  declare_string_option ~preprocess:CWarnings.normalize_flags_string
    { optdepr  = false;
      optkey   = ["Warnings"];
      optread  = CWarnings.get_flags;
      optwrite = CWarnings.set_flags }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Guard"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_guarded);
      optwrite = (fun b -> Global.set_check_guarded b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Positivity"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_positive);
      optwrite = (fun b -> Global.set_check_positive b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Universe"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_universes);
      optwrite = (fun b -> Global.set_check_universes b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Definitional"; "UIP"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.allow_uip);
      optwrite = (fun b -> Global.set_typing_flags
                     {(Global.typing_flags ()) with Declarations.allow_uip = b})
    }
