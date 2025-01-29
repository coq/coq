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
open Names
open Nameops
open Constr
open Constrexpr
open EConstr
open Libnames

let () = CErrors.register_handler begin function
| Rewrite.RewriteFailure (env, sigma, e) ->
  let e = Himsg.explain_pretype_error env sigma e in
  Some Pp.(str"setoid rewrite failed: " ++ e)
| _ -> None
end

module TC = Typeclasses

let classes_dirpath =
  Names.DirPath.make (List.map Id.of_string ["Classes";"Corelib"])

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Rocqlib.check_required_library ["Corelib";"Setoids";"Setoid"]

type rewrite_attributes = {
  polymorphic : bool;
  locality : Hints.hint_locality;
}

let rewrite_attributes =
  let open Attributes.Notations in
  Attributes.(polymorphic ++ locality) >>= fun (polymorphic, locality) ->
  let locality =
    if Locality.make_section_locality locality then Hints.Local else SuperGlobal
  in
  Attributes.Notations.return { polymorphic; locality }

(** Utility functions *)

module PropGlobal = struct

  let respectful_ref () = Rocqlib.lib_ref "rewrite.prop.respectful"

  let proper_class =
    fun () -> Option.get (TC.class_info (Rocqlib.lib_ref "rewrite.prop.Proper"))

  let proper_proj () = Rocqlib.lib_ref "rewrite.prop.proper_prf"

end

(* By default the strategy for "rewrite_db" is top-down *)

let mkappc s l = CAst.make @@ CAppExpl ((qualid_of_ident (Id.of_string s),None),l)

let declare_an_instance n s args =
  (((CAst.make @@ Name n),None),
   CAst.make @@ CAppExpl ((qualid_of_string s,None), args))

let declare_instance a aeq n s = declare_an_instance n s [a;aeq]

let anew_instance atts binders (name,t) fields =
  let _id = Classes.new_instance ~poly:atts.polymorphic
      name binders t (true, CAst.make @@ CRecord (fields))
      ~locality:atts.locality Hints.empty_hint_info
  in
  ()

let declare_instance_refl atts binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Reflexive") "Corelib.Classes.RelationClasses.Reflexive"
  in anew_instance atts binders instance
       [(qualid_of_ident (Id.of_string "reflexivity"),lemma)]

let declare_instance_sym atts binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Symmetric") "Corelib.Classes.RelationClasses.Symmetric"
  in anew_instance atts binders instance
       [(qualid_of_ident (Id.of_string "symmetry"),lemma)]

let declare_instance_trans atts binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Transitive") "Corelib.Classes.RelationClasses.Transitive"
  in anew_instance atts binders instance
       [(qualid_of_ident (Id.of_string "transitivity"),lemma)]

let declare_relation atts ?(binders=[]) a aeq n refl symm trans =
  init_setoid ();
  let instance = declare_instance a aeq (add_suffix n "_relation") "Corelib.Classes.RelationClasses.RewriteRelation" in
  let () = anew_instance atts binders instance [] in
  match (refl,symm,trans) with
    (None, None, None) -> ()
  | (Some lemma1, None, None) ->
    declare_instance_refl atts binders a aeq n lemma1
  | (None, Some lemma2, None) ->
    declare_instance_sym atts binders a aeq n lemma2
  | (None, None, Some lemma3) ->
    declare_instance_trans atts binders a aeq n lemma3
  | (Some lemma1, Some lemma2, None) ->
    let () = declare_instance_refl atts binders a aeq n lemma1 in
    declare_instance_sym atts binders a aeq n lemma2
  | (Some lemma1, None, Some lemma3) ->
    let () = declare_instance_refl atts binders a aeq n lemma1 in
    let () = declare_instance_trans atts binders a aeq n lemma3 in
    let instance = declare_instance a aeq n "Corelib.Classes.RelationClasses.PreOrder" in
    anew_instance atts binders instance
      [(qualid_of_ident (Id.of_string "PreOrder_Reflexive"), lemma1);
       (qualid_of_ident (Id.of_string "PreOrder_Transitive"),lemma3)]
  | (None, Some lemma2, Some lemma3) ->
    let () = declare_instance_sym atts binders a aeq n lemma2 in
    let () = declare_instance_trans atts binders a aeq n lemma3 in
    let instance = declare_instance a aeq n "Corelib.Classes.RelationClasses.PER" in
    anew_instance atts binders instance
      [(qualid_of_ident (Id.of_string "PER_Symmetric"), lemma2);
       (qualid_of_ident (Id.of_string "PER_Transitive"),lemma3)]
  | (Some lemma1, Some lemma2, Some lemma3) ->
    let () = declare_instance_refl atts binders a aeq n lemma1 in
    let () = declare_instance_sym atts binders a aeq n lemma2 in
    let () = declare_instance_trans atts binders a aeq n lemma3 in
    let instance = declare_instance a aeq n "Corelib.Classes.RelationClasses.Equivalence" in
    anew_instance atts binders instance
      [(qualid_of_ident (Id.of_string "Equivalence_Reflexive"), lemma1);
       (qualid_of_ident (Id.of_string "Equivalence_Symmetric"), lemma2);
       (qualid_of_ident (Id.of_string "Equivalence_Transitive"), lemma3)]

let cHole = CAst.make @@ CHole (None)

let proper_projection env sigma r ty =
  let rel_vect n m = Array.init m (fun i -> mkRel(n+m-i)) in
  let ctx, inst = decompose_prod_decls sigma ty in
  let mor, args = destApp sigma inst in
  let instarg = mkApp (r, rel_vect 0 (List.length ctx)) in
  let sigma, proj = Evd.fresh_global env sigma (PropGlobal.proper_proj ()) in
  let app = mkApp (proj,
                  Array.append args [| instarg |]) in
  sigma, it_mkLambda_or_LetIn app ctx

let declare_projection name instance_id r =
  let env = Global.env () in
  let poly = Environ.is_polymorphic env r in
  let sigma = Evd.from_env env in
  let sigma,c = Evd.fresh_global env sigma r in
  let ty = Retyping.get_type_of env sigma c in
  let sigma, body = proper_projection env sigma c ty in
  let sigma, typ = Typing.type_of env sigma body in
  let ctx, typ = decompose_prod_decls sigma typ in
  let typ =
    let n =
      let rec aux t =
        match EConstr.kind sigma t with
        | App (f, [| a ; a' ; rel; rel' |])
            when isRefX env sigma (PropGlobal.respectful_ref ()) f ->
          succ (aux rel')
        | _ -> 0
      in
      let init =
        match EConstr.kind sigma typ with
            App (f, args) when isRefX env sigma (PropGlobal.respectful_ref ()) f  ->
              mkApp (f, fst (Array.chop (Array.length args - 2) args))
          | _ -> typ
      in aux init
    in
    let ctx,ccl = Reductionops.whd_decompose_prod_n env sigma (3 * n) typ
    in it_mkProd ccl ctx
  in
  let types = Some (it_mkProd_or_LetIn typ ctx) in
  let kind = Decls.(IsDefinition Definition) in
  let impargs, udecl = [], UState.default_univ_decl in
  let cinfo = Declare.CInfo.make ~name ~impargs ~typ:types () in
  let info = Declare.Info.make ~kind ~udecl ~poly () in
  let _r : GlobRef.t =
    Declare.declare_definition ~cinfo ~info ~opaque:false ~body sigma
  in ()

let add_setoid atts binders a aeq t n =
  init_setoid ();
  let () = declare_instance_refl atts binders a aeq n (mkappc "Seq_refl" [a;aeq;t]) in
  let () = declare_instance_sym atts binders a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
  let () = declare_instance_trans atts binders a aeq n (mkappc "Seq_trans" [a;aeq;t]) in
  let instance = declare_instance a aeq n "Corelib.Classes.RelationClasses.Equivalence"
  in
  anew_instance atts binders instance
    [(qualid_of_ident (Id.of_string "Equivalence_Reflexive"), mkappc "Seq_refl" [a;aeq;t]);
     (qualid_of_ident (Id.of_string "Equivalence_Symmetric"), mkappc "Seq_sym" [a;aeq;t]);
     (qualid_of_ident (Id.of_string "Equivalence_Transitive"), mkappc "Seq_trans" [a;aeq;t])]

let add_morphism_as_parameter atts m n : unit =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let poly = atts.polymorphic in
  let kind = Decls.(IsAssumption Logical) in
  let impargs, udecl = [], UState.default_univ_decl in
  let evd, types = Rewrite.Internal.build_morphism_signature env evd m in
  let evd, pe = Declare.prepare_parameter ~poly ~udecl ~types evd in
  let cst = Declare.declare_constant ~name:instance_id ~kind (Declare.ParameterEntry pe) in
  let cst = GlobRef.ConstRef cst in
  Classes.Internal.add_instance
    (PropGlobal.proper_class ()) Hints.empty_hint_info atts.locality cst;
  declare_projection n instance_id cst

let add_morphism_interactive atts ~tactic m n : Declare.Proof.t =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, morph = Rewrite.Internal.build_morphism_signature env evd m in
  let poly = atts.polymorphic in
  let kind = Decls.(IsDefinition Instance) in
  let hook { Declare.Hook.S.dref; _ } = dref |> function
    | GlobRef.ConstRef cst ->
      Classes.Internal.add_instance (PropGlobal.proper_class ()) Hints.empty_hint_info
        atts.locality (GlobRef.ConstRef cst);
      declare_projection n instance_id (GlobRef.ConstRef cst)
    | _ -> assert false
  in
  let hook = Declare.Hook.make hook in
  Flags.silently
    (fun () ->
       let cinfo = Declare.CInfo.make ~name:instance_id ~typ:morph () in
       let info = Declare.Info.make ~poly ~hook ~kind () in
       let lemma = Declare.Proof.start ~cinfo ~info evd in
       fst (Declare.Proof.by tactic lemma)) ()

let add_morphism atts ~tactic binders m s n =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let instance_name = (CAst.make @@ Name instance_id),None in
  let instance_t =
    CAst.make @@ CAppExpl
      ((Libnames.qualid_of_string "Corelib.Classes.Morphisms.Proper",None),
       [cHole; s; m])
  in
  let _id, lemma = Classes.new_instance_interactive
      ~locality:atts.locality ~poly:atts.polymorphic
      instance_name binders instance_t
      ~tac:tactic ~hook:(declare_projection n instance_id)
      Hints.empty_hint_info None
  in
  lemma (* no instance body -> always open proof *)
