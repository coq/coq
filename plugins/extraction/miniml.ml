(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Target language for extraction: a core ML called MiniML. *)

open Names

module InfvInst =
struct
  (* Is informative + memoized corresponding sort *)
  type t = (bool * Sorts.Quality.t) array
  let empty = [||]
  let compare i1 i2 = CArray.compare (fun (b1, _) (b2, _) -> compare b1 b2) i1 i2
  let equal i1 i2 = Int.equal (compare i1 i2) 0

  let generate env actx =
    let init_option_downfrom n f =
      let rec aux acc i f =
        if i < 0 then acc
        else
          match f i with
          | Some a -> aux (a :: acc) (i-1) f
          | None -> aux acc (i-1) f
      in aux [] (n - 1) f
    in
    let names = UVars.AbstractContext.names actx in
    let univs = names.UVars.univs in
    let idusubst = Array.init (Array.length univs) Univ.Level.var in
    let quals = names.UVars.quals in
    let numquals = Array.length quals in
    let init n =
      try
        let subst = Array.init numquals (fun i -> Sorts.Quality.var i) in
        let infvs = Array.make numquals true in
        let n = ref n in
        for i = numquals - 1 downto 0 do
          let try_qual q otherwise =
            subst.(i) <- q;
            let inst = UVars.Instance.of_array (subst, idusubst) in
            let pcstr = UVars.AbstractContext.instantiate inst actx in
            let (quals, _) = CArray.chop i quals in
            let uctx = UVars.UContext.make {quals; univs} (UVars.Instance.abstract_instance (i, Array.length univs), pcstr) in
            try
              let _ = Environ.push_context uctx env in ()
            with QGraph.EliminationError _ -> otherwise ()
          in
          let relevant = !n mod 2 = 0 in
          infvs.(i) <- relevant;
          if relevant then begin
              try_qual Sorts.Quality.qtype (fun () -> raise Exit)
            end
          else
            try_qual Sorts.Quality.qsprop
              (fun () -> try_qual Sorts.Quality.qprop (fun () -> raise Exit));
          n := !n / 2
        done;
        Some (Array.map2 (fun a b -> (a, b)) infvs subst)
      with Exit ->
        None
    in
    init_option_downfrom (1 lsl numquals) init

  let ground inst =
    let qvars, _ = UVars.Instance.to_array inst in
    let map q = Sorts.Quality.is_qtype q, q in
    Array.map map qvars

  let instantiate actx inst =
    let names = UVars.AbstractContext.names actx in
    let numunivs = Array.length names.UVars.univs in
    let univs = Array.init numunivs Univ.Level.var in
    let inst = Array.map snd inst in
    UVars.Instance.of_array (inst, univs)

  let encode inst =
    if Array.for_all fst inst then None
    else
      let len = Array.length inst in
      let map i =
        match fst (inst.(i)) with
        | true -> 'K'
        | false -> 'E'
      in
      Some (String.init len map)
end

type global = { glob : GlobRef.t; inst : InfvInst.t }

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)

(* We eliminate from terms:
   1) types
   2) logical parts
   3) user-declared implicit arguments of a constant of constructor
*)

type kill_reason =
  | Ktype
  | Kprop
  | Kimplicit of global * int  (* n-th arg of a cst or construct *)

type sign = Keep | Kill of kill_reason

(* Convention: outmost lambda/product gives the head of the list. *)

type signature = sign list

(*s ML type expressions. *)

type ml_type =
  | Tarr    of ml_type * ml_type
  | Tglob   of global * ml_type list
  | Tvar    of int
  | Tvar'   of int (* same as Tvar, used to avoid clash *)
  | Tmeta   of ml_meta (* used during ML type reconstruction *)
  | Tdummy  of kill_reason
  | Tunknown
  | Taxiom

and ml_meta = { id : int; mutable contents : ml_type option }

(* ML type schema.
   The integer is the number of variable in the schema. *)

type ml_schema = int * ml_type

(*s ML inductive types. *)

type inductive_kind =
  | Singleton
  | Coinductive
  | Standard
  | Record of global option list (* None for anonymous field *)

(* A [ml_ind_packet] is the miniml counterpart of a [one_inductive_body].
   If the inductive is logical ([ip_logical = false]), then all other fields
   are unused. Otherwise,
   [ip_sign] is a signature concerning the arguments of the inductive,
   [ip_vars] contains the names of the type variables surviving in ML,
   [ip_types] contains the ML types of all constructors.
*)

type ml_ind_packet = {
  ip_typename : Id.t;
  ip_typename_ref : global;
  ip_consnames : Id.t array;
  ip_consnames_ref : global array;
  ip_logical : bool;
  ip_sign : signature;
  ip_vars : Id.t list;
  ip_types : (ml_type list) array
}

(* [ip_nparams] contains the number of parameters. *)

type equiv =
  | NoEquiv
  | Equiv of KerName.t
  | RenEquiv of string

type ml_ind = {
  ind_kind : inductive_kind;
  ind_nparams : int;
  ind_packets : ml_ind_packet array;
  ind_equiv : equiv
}

(*s ML terms. *)

type ml_ident =
  | Dummy
  | Id of Id.t
  | Tmp of Id.t

(** We now store some typing information on constructors
    and cases to avoid type-unsafe optimisations. This will be
    either the type of the applied constructor or the type
    of the head of the match.
*)

(** Nota : the constructor [MLtuple] and the extension of [MLcase]
    to general patterns have been proposed by P.N. Tollitte for
    his Relation Extraction plugin. [MLtuple] is currently not
    used by the main extraction, as well as deep patterns. *)

type ml_branch = ml_ident list * ml_pattern * ml_ast

and ml_ast =
  | MLrel    of int
  | MLapp    of ml_ast * ml_ast list
  | MLlam    of ml_ident * ml_ast
  | MLletin  of ml_ident * ml_ast * ml_ast
  | MLglob   of global
  | MLcons   of ml_type * global * ml_ast list
  | MLtuple  of ml_ast list
  | MLcase   of ml_type * ml_ast * ml_branch array
  | MLfix    of int * Id.t array * ml_ast array
  | MLexn    of string
  | MLdummy  of kill_reason
  | MLaxiom  of string
  | MLmagic  of ml_ast
  | MLuint   of Uint63.t
  | MLfloat  of Float64.t
  | MLstring of Pstring.t
  | MLparray of ml_ast array * ml_ast

and ml_pattern =
  | Pcons   of global * ml_pattern list
  | Ptuple  of ml_pattern list
  | Prel    of int (** Cf. the idents in the branch. [Prel 1] is the last one. *)
  | Pwild
  | Pusual  of global (** Shortcut for Pcons (r,[Prel n;...;Prel 1]) **)

(*s ML declarations. *)

type ml_decl =
  | Dind  of ml_ind
  | Dtype of global * Id.t list * ml_type
  | Dterm of global * ml_ast * ml_type
  | Dfix  of global array * ml_ast array * ml_type array

type ml_spec =
  | Sind  of ml_ind
  | Stype of global * Id.t list * ml_type option
  | Sval  of global * ml_type

type ml_specif =
  | Spec of ml_spec
  | Smodule of ml_module_type
  | Smodtype of ml_module_type

and ml_module_type =
  | MTident of ModPath.t
  | MTfunsig of MBId.t * ml_module_type * ml_module_type
  | MTsig of ModPath.t * ml_module_sig
  | MTwith of ml_module_type * ml_with_declaration

and ml_with_declaration =
  | ML_With_type of InfvInst.t * Id.t list * Id.t list * ml_type
  | ML_With_module of Id.t list * ModPath.t

and ml_module_sig = (Id.t * ml_specif) list

type ml_structure_elem =
  | SEdecl of ml_decl
  | SEmodule of ml_module
  | SEmodtype of ml_module_type

and ml_module_expr =
  | MEident of ModPath.t
  | MEfunctor of MBId.t * ml_module_type * ml_module_expr
  | MEstruct of ModPath.t * ml_module_structure
  | MEapply of ml_module_expr * ml_module_expr

and ml_module_structure = (Id.t * ml_structure_elem) list

and ml_module =
    { ml_mod_expr : ml_module_expr;
      ml_mod_type : ml_module_type }

(* NB: we do not translate the [mod_equiv] field, since [mod_equiv = mp]
   implies that [mod_expr = MEBident mp]. Same with [msb_equiv]. *)

type ml_structure = (ModPath.t * ml_module_structure) list

type ml_signature = (ModPath.t * ml_module_sig) list

type unsafe_needs = {
  mldummy : bool;
  tdummy : bool;
  tunknown : bool;
  magic : bool
}

type 's language_descr = {
  keywords : Id.Set.t;

  (* Concerning the source file *)
  file_suffix : string;
  file_naming : 's -> DirPath.t -> string;
  (* the second argument is a comment to add to the preamble *)
  preamble :
    's -> Id.t -> Pp.t option -> DirPath.Set.t -> unsafe_needs ->
    Pp.t;
  pp_struct : 's -> ml_structure -> Pp.t;

  (* Concerning a possible interface file *)
  sig_suffix : string option;
  (* the second argument is a comment to add to the preamble *)
  sig_preamble :
    's -> Id.t -> Pp.t option -> DirPath.Set.t -> unsafe_needs ->
    Pp.t;
  pp_sig : 's -> ml_signature -> Pp.t;

  (* for an isolated declaration print *)
  pp_decl : 's -> ml_decl -> Pp.t;

  (* Lexical conventions *)
  unquote : string -> string; (* e.g. Scheme turns ['] into [~] *)
  upper_types : bool; (* capitalized type names, as in Haskell *)

  (* native types for char and string literals *)
  char_type : string option;
  string_type : string option;

  (* is modular extraction supported *)
  modular : bool;

  (* toplevel module name of a monolithic extraction, from the file basename *)
  id_of_filename : string -> Id.t;

}
