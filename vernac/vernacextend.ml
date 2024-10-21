(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Vernactypes

type vernac_keep_as = VtKeepAxiom | VtKeepDefined | VtKeepOpaque

type vernac_qed_type = VtKeep of vernac_keep_as | VtDrop

type vernac_when =
  | VtNow
  | VtLater

type vernac_classification =
  (* Start of a proof *)
  | VtStartProof of vernac_start
  (* Command altering the global state, bad for parallel
     processing. *)
  | VtSideff of vernac_sideff_type
  (* End of a proof *)
  | VtQed of vernac_qed_type
  (* A proof step *)
  | VtProofStep of {
      proof_block_detection : proof_block_name option
    }
  (* Queries are commands assumed to be "pure", that is to say, they
     don't modify the interpretation state. *)
  | VtQuery
  (* Commands that change the current proof mode *)
  | VtProofMode of Pvernac.proof_mode
  (* To be removed *)
  | VtMeta
and vernac_start = opacity_guarantee * Names.Id.t list
and vernac_sideff_type = Names.Id.t list * vernac_when
and opacity_guarantee =
  | GuaranteesOpacity (** Only generates opaque terms at [Qed] *)
  | Doesn'tGuaranteeOpacity (** May generate transparent terms even with [Qed].*)

and solving_tac = bool (** a terminator *)

and anon_abstracting_tac = bool (** abstracting anonymously its result *)

and proof_block_name = string (** open type of delimiters *)

type vernac_command = ?loc:Loc.t -> atts:Attributes.vernac_flags -> unit -> typed_vernac

type plugin_args = Genarg.raw_generic_argument list

(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 211 :
    (Vernacexpr.extend_name, bool * (plugin_args -> vernac_command)) Hashtbl.t)

let vinterp_add depr s f = Hashtbl.replace vernac_tab s (depr, f)

let vinterp_map s =
  try
    Hashtbl.find vernac_tab s
  with Not_found ->
    user_err
      (str"Cannot find vernac command " ++ str s.ext_entry ++ str".")

let warn_deprecated_command =
  let open CWarnings in
  create ~name:"deprecated-command" ~category:CWarnings.CoreCategories.deprecated
         (fun pr -> str "Deprecated vernacular command: " ++ pr)

(* Interpretation of a vernac command *)

let type_vernac opn converted_args ?loc ~atts =
  let depr, callback = vinterp_map opn in
  let () = if depr then
      let rules = Egramml.get_extend_vernac_rule opn in
      let pr_gram = function
        | Egramml.GramTerminal s -> str s
        | Egramml.GramNonTerminal _ -> str "_"
      in
      let pr = pr_sequence pr_gram rules in
      warn_deprecated_command pr;
  in
  callback converted_args ?loc ~atts

(** VERNAC EXTEND registering *)

type classifier = Genarg.raw_generic_argument list -> vernac_classification

(** Classifiers  *)
module StringPair =
struct
  type t = string * string
  let compare (s1, s2) (t1, t2) =
    let c = String.compare s1 t1 in
    if Int.equal c 0 then String.compare s2 t2 else c
end

module StringPairMap = Map.Make(StringPair)

let classifiers : classifier array StringPairMap.t ref = ref StringPairMap.empty

let get_vernac_classifier e args =
  let open Vernacexpr in
  (StringPairMap.find (e.ext_plugin, e.ext_entry) !classifiers).(e.ext_index) args

let declare_vernac_classifier name f =
  classifiers := StringPairMap.add name f !classifiers

let classify_as_query = VtQuery
let classify_as_sideeff = VtSideff ([], VtLater)
let classify_as_proofstep = VtProofStep { proof_block_detection = None}

type (_, _) ty_sig =
| TyNil : (vernac_command, vernac_classification) ty_sig
| TyTerminal : string * ('r, 's) ty_sig -> ('r, 's) ty_sig
| TyNonTerminal : ('a, 'b, 'c) Extend.ty_user_symbol * ('r, 's) ty_sig -> ('a -> 'r, 'a -> 's) ty_sig

type ty_ml = TyML : bool * ('r, 's) ty_sig * 'r * 's option -> ty_ml

let type_error () = CErrors.anomaly (Pp.str "Ill-typed VERNAC EXTEND")

let rec untype_classifier : type r s. (r, s) ty_sig -> s -> classifier = function
| TyNil -> fun f args ->
  begin match args with
  | [] -> f
  | _ :: _ -> type_error ()
  end
| TyTerminal (_, ty) -> fun f args -> untype_classifier ty f args
| TyNonTerminal (tu, ty) -> fun f args ->
  let open Genarg in
  begin match args with
  | [] -> type_error ()
  | GenArg (Rawwit tag, v) :: args ->
    match Genarg.genarg_type_eq tag (Egramml.proj_symbol tu) with
    | None -> type_error ()
    | Some Refl -> untype_classifier ty (f v) args
  end

(** Stupid GADTs forces us to duplicate the definition just for typing *)
let rec untype_command : type r s. (r, s) ty_sig -> r -> plugin_args -> vernac_command = function
| TyNil -> fun f args ->
  begin match args with
  | [] -> f
  | _ :: _ -> type_error ()
  end
| TyTerminal (_, ty) -> fun f args -> untype_command ty f args
| TyNonTerminal (tu, ty) -> fun f args ->
  let open Genarg in
  begin match args with
  | [] -> type_error ()
  | GenArg (Rawwit tag, v) :: args ->
    match genarg_type_eq tag (Egramml.proj_symbol tu) with
    | None -> type_error ()
    | Some Refl -> untype_command ty (f v) args
  end

let rec untype_user_symbol : type s a b c. (a, b, c) Extend.ty_user_symbol -> (s, Gramlib.Grammar.norec, a) Procq.Symbol.t =
  let open Extend in function
  | TUlist1 l -> Procq.Symbol.list1 (untype_user_symbol l)
  | TUlist1sep (l, s) -> Procq.Symbol.list1sep (untype_user_symbol l) (Procq.Symbol.tokens [Procq.TPattern (Procq.terminal s)]) false
  | TUlist0 l -> Procq.Symbol.list0 (untype_user_symbol l)
  | TUlist0sep (l, s) -> Procq.Symbol.list0sep (untype_user_symbol l) (Procq.Symbol.tokens [Procq.TPattern (Procq.terminal s)]) false
  | TUopt o -> Procq.Symbol.opt (untype_user_symbol o)
  | TUentry a -> Procq.Symbol.nterm (Procq.genarg_grammar (Genarg.ExtraArg a))
  | TUentryl (a, i) -> Procq.Symbol.nterml (Procq.genarg_grammar (Genarg.ExtraArg a)) (string_of_int i)

let rec untype_grammar : type r s. (r, s) ty_sig -> 'a Egramml.grammar_prod_item list = function
| TyNil -> []
| TyTerminal (tok, ty) -> Egramml.GramTerminal tok :: untype_grammar ty
| TyNonTerminal (tu, ty) ->
  let t = Genarg.rawwit (Egramml.proj_symbol tu) in
  let symb = untype_user_symbol tu in
  Egramml.GramNonTerminal (Loc.tag (t, symb)) :: untype_grammar ty

let declare_dynamic_vernac_extend ~command ?entry ~depr cl ty f =
  let cl = untype_classifier ty cl in
  let f = untype_command ty f in
  let r = untype_grammar ty in
  let ext = { command with Vernacexpr.ext_index = 0 } in
  vinterp_add depr ext f;
  Egramml.declare_vernac_command_grammar ~allow_override:true ext entry r;
  declare_vernac_classifier (ext.ext_plugin, ext.ext_entry) [|cl|];
  ext

let is_static_linking_done = ref false

let static_linking_done () = is_static_linking_done := true

let static_vernac_extend ~plugin ~command ?classifier ?entry ext =
  let get_classifier (TyML (_, ty, _, cl)) = match cl with
  | Some cl -> untype_classifier ty cl
  | None ->
    match classifier with
    | Some cl -> fun _ -> cl command
    | None ->
      let e = match entry with
      | None -> "COMMAND"
      | Some e -> Procq.Entry.name e
      in
      let msg = Printf.sprintf "\
        Vernac entry \"%s\" misses a classifier. \
        A classifier is a function that returns an expression \
        of type vernac_classification (see Vernacexpr). You can: \n\
        - Use '... EXTEND %s CLASSIFIED AS QUERY ...' if the \
          new vernacular command does not alter the system state;\n\
        - Use '... EXTEND %s CLASSIFIED AS SIDEFF ...' if the \
          new vernacular command alters the system state but not the \
          parser nor it starts a proof or ends one;\n\
        - Use '... EXTEND %s CLASSIFIED BY f ...' to specify \
          a global function f.  The function f will be called passing\
          \"%s\" as the only argument;\n\
        - Add a specific classifier in each clause using the syntax:\n\
          '[...] => [ f ] -> [...]'.\n\
        Specific classifiers have precedence over global \
        classifiers. Only one classifier is called."
          command e e e command
      in
      CErrors.user_err (Pp.strbrk msg)
  in
  let cl = Array.map_of_list get_classifier ext in
  let ext_plugin = Option.default "__" plugin in
  let iter i (TyML (depr, ty, f, _)) =
    let f = untype_command ty f in
    let r = untype_grammar ty in
    let ext = Vernacexpr.{ ext_plugin; ext_entry = command; ext_index = i } in
    let () = vinterp_add depr ext f in
    let () = Egramml.declare_vernac_command_grammar ~allow_override:false ext entry r in
    let () = match plugin with
      | None ->
        let () =
          if !is_static_linking_done
          then CErrors.anomaly
              Pp.(str "static_vernac_extend in dynlinked code must pass non-None plugin.")
        in
        Egramml.extend_vernac_command_grammar ~undoable:false ext
      | Some plugin ->
        Mltop.add_init_function plugin (fun () ->
            Egramml.extend_vernac_command_grammar ~undoable:true ext)
    in
    ()
  in
  let () = declare_vernac_classifier (ext_plugin, command) cl in
  let () = List.iteri iter ext in
  ()

(** VERNAC ARGUMENT EXTEND registering *)

type 'a argument_rule =
| Arg_alias of 'a Procq.Entry.t
| Arg_rules of 'a Procq.Production.t list

type 'a vernac_argument = {
  arg_printer : Environ.env -> Evd.evar_map -> 'a -> Pp.t;
  arg_parsing : 'a argument_rule;
}

let vernac_argument_extend ~plugin ~name arg =
  let wit = Genarg.create_arg name in
  let entry = match arg.arg_parsing with
  | Arg_alias e ->
    let () = Procq.register_grammar wit e in
    e
  | Arg_rules rules ->
    let e = Procq.create_generic_entry2 name (Genarg.rawwit wit) in
    let plugin_uid = (plugin, "vernacargextend:"^name) in
    let () = Egramml.grammar_extend ~plugin_uid e
        (Procq.Fresh (Gramlib.Gramext.First, [None, None, rules]))
    in
    e
  in
  let pr = arg.arg_printer in
  let pr x = Genprint.PrinterBasic (fun env sigma -> pr env sigma x) in
  let () = Genprint.register_vernac_print0 wit pr in
  (wit, entry)
