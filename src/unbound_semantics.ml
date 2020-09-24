open! Core
open! Import
open Unbound

module Sorted_name = struct
  module T = struct
    type t =
      [ `Typ | `Sigture | `Val | `Tag | `Modl ] * string
    [@@deriving sexp, compare]
  end
  include T
  include Comparable.Make (T)
end

let rec names_used_by_defn (defn : Defn.t) =
  match defn.without_positions with
  | InfixTyp _ | InfixTerm _ -> Sorted_name.Set.empty
  | TypAlias (_, _, typ) ->
    names_used_by_typ typ
  | SumTyp (_, _, fields) ->
    Sorted_name.Set.union_list
      (List.map fields
         ~f:(fun (_, typ_opt) ->
           match typ_opt with
           | None -> Sorted_name.Set.empty
           | Some typ -> names_used_by_typ typ))
  | Tag (_, typs_opt, tag) ->
    Set.union (names_used_by_tag tag)
      (match typs_opt with
       | None -> Sorted_name.Set.empty
       | Some (typ1, typ2_opt) ->
         Set.union (names_used_by_typ typ1)
           (match typ2_opt with
            | None -> Sorted_name.Set.empty
            | Some typ2 -> names_used_by_typ typ2))
  | Val (pat, term) ->
    Set.union (names_used_by_pat pat) (names_used_by_term term)
  | Fun (_, args, typ_opt, body) ->
    Set.union (Sorted_name.Set.union_list (List.map args ~f:names_used_by_pat))
      (Set.union
         (match typ_opt with
          | None -> Sorted_name.Set.empty
          | Some typ -> names_used_by_typ typ)
         (names_used_by_term body))
  | Sigture (_, sigture) ->
    names_used_by_sigture sigture
  | Modl (_, arg_opt, sigture_opt, modl) ->
    let body_names =
      Set.union (names_used_by_modl modl)
        (match sigture_opt with
         | None -> Sorted_name.Set.empty
         | Some sigture -> names_used_by_sigture sigture)
    in
    (match arg_opt with
     | None ->
       body_names
     | Some (_, arg_sigture) ->
       Set.union
         (names_used_by_sigture arg_sigture)
         body_names)
  | Include modl ->
    names_used_by_modl modl

and names_used_by_typ (typ : Typ.t) =
  match typ.without_positions with
  | Var (_, name) -> Sorted_name.Set.singleton (`Typ, name)
  | Modl_proj (modl, _) -> names_used_by_modl modl
  | Ap typs -> Sorted_name.Set.union_list (List.map typs ~f:names_used_by_typ)
  | Record fields ->
    Sorted_name.Set.union_list
      (List.map fields
         ~f:(fun (_, typ) -> names_used_by_typ typ))
  | Forall (_, result) ->
    names_used_by_typ result

and names_used_by_tag (tag : Tag.t) =
  match tag.without_positions with
  | Var (_, name) -> Sorted_name.Set.singleton (`Tag, name)
  | Modl_proj (modl, _) -> names_used_by_modl modl
  | Destr term -> names_used_by_term term

and names_used_by_pat (pat : Pat.t) =
  match pat.without_positions with
  | Wild -> Sorted_name.Set.empty
  | Var _ -> Sorted_name.Set.empty
  | Record fields ->
    Sorted_name.Set.union_list
      (List.map fields
         ~f:(fun (_, pat) -> names_used_by_pat pat))
  | Tag (tag, pat_opt) ->
    let names_used_by_tag = names_used_by_tag tag in
    (match pat_opt with
     | None -> names_used_by_tag
     | Some pat ->
       Set.union names_used_by_tag (names_used_by_pat pat))
  | Number _ -> Sorted_name.Set.empty
  | String _ -> Sorted_name.Set.empty
  | Ascribe (pat, typ) ->
    Set.union (names_used_by_pat pat) (names_used_by_typ typ)

and names_used_by_term (term : Term.t) =
  match term.without_positions with
  | Var (_, name) -> Sorted_name.Set.singleton (`Val, name)
  | Modl_proj (modl, _) ->
    names_used_by_modl modl
  | Fun (args, typ_opt, body) ->
    Set.union (Sorted_name.Set.union_list (List.map args ~f:names_used_by_pat))
      (Set.union
         (match typ_opt with
          | None -> Sorted_name.Set.empty
          | Some typ -> names_used_by_typ typ)
         (names_used_by_term body))
  | Ap terms ->
    Sorted_name.Set.union_list
      (List.map terms ~f:names_used_by_term)
  | Record fields ->
    Sorted_name.Set.union_list
      (List.map fields ~f:(fun (_, term) -> names_used_by_term term))
  | Match (term, cases) ->
    Set.union
      (names_used_by_term term)
      (Sorted_name.Set.union_list
         (List.map cases
            ~f:(fun (pat, term) ->
              Set.union (names_used_by_pat pat) (names_used_by_term term))))
  | Number _ -> Sorted_name.Set.empty
  | String _ -> Sorted_name.Set.empty
  | Built_in (_, typ) -> names_used_by_typ typ
  | Let (defns, term) ->
    Set.union
      (Sorted_name.Set.union_list (List.map defns ~f:names_used_by_defn))
      (names_used_by_term term)
  | Ascribe (term, typ) ->
    Set.union
      (names_used_by_term term)
      (names_used_by_typ typ)

and names_used_by_sigture (sigture : Sigture.t) =
  match sigture.without_positions with
  | Var (_, name) -> Sorted_name.Set.singleton (`Sigture, name)
  | Modl_proj (modl, _) -> names_used_by_modl modl
  | Arrow ((_, arg_sigture), result_sigture) ->
    Set.union
      (names_used_by_sigture arg_sigture)
      (names_used_by_sigture result_sigture)
  | Body decls ->
    Sorted_name.Set.union_list (List.map ~f:names_used_by_decl decls)
  | With_type (sigture, _, typ) ->
    Set.union
      (names_used_by_sigture sigture)
      (names_used_by_typ typ)

and names_used_by_modl (modl : Modl.t) =
  match modl.without_positions with
  | Var (_, name) -> Sorted_name.Set.singleton (`Modl, name)
  | Modl_proj (modl, _) -> names_used_by_modl modl
  | Ap (modl1, modl2) ->
    Set.union (names_used_by_modl modl1) (names_used_by_modl modl2)
  | Ascribe (modl, sigture) ->
    Set.union (names_used_by_modl modl) (names_used_by_sigture sigture)
  | Body defns -> Sorted_name.Set.union_list (List.map defns ~f:names_used_by_defn)

and names_used_by_decl (decl : Decl.t) =
  match decl.without_positions with
  | InfixTyp _ | InfixTerm _ -> Sorted_name.Set.empty
  | Typ (_, _, typ_opt) ->
    (match typ_opt with
     | None -> Sorted_name.Set.empty
     | Some typ -> names_used_by_typ typ)
  | Tag (_, typ1, typ2_opt) ->
    Set.union
      (names_used_by_typ typ1)
      (match typ2_opt with
       | None -> Sorted_name.Set.empty
       | Some typ2 -> names_used_by_typ typ2)
  | Val (_, typ) -> names_used_by_typ typ
  | Sigture (_, sigture) | Modl (_, sigture) | Include sigture ->
    names_used_by_sigture sigture
;;

let rec pat_is_elim_free (pat : Pat.t) =
  match pat.without_positions with
  | Wild | Var _ -> true
  | Record _ | Tag _ | Number _ | String _ -> false
  | Ascribe (pat, _) -> pat_is_elim_free pat
;;

let rec defn_is_value (defn : Defn.t) =
  match defn.without_positions with
  | Val (pat, term) ->
    pat_is_elim_free pat && term_is_value term
  | Tag (_, _, tag) -> tag_is_value tag
  | Fun _ -> true
  | Modl (_, arg_opt, _, modl) ->
    (match arg_opt with
     | Some _ -> true
     | None -> modl_is_value modl)
  | Include modl -> modl_is_value modl
  | Sigture _ -> true
  | InfixTyp _ | InfixTerm _ | TypAlias _ | SumTyp _ -> true

and term_is_value (term : Term.t) =
  match term.without_positions with
  | Var _ | Fun _ | Number _ | String _ | Built_in _ -> true
  | Ap _ | Match _ | Let _ -> false
  | Modl_proj (modl, _) -> modl_is_value modl
  | Record str_term_list ->
    List.for_all str_term_list ~f:(fun (_, term) -> term_is_value term)
  | Ascribe (term, _) -> term_is_value term

and tag_is_value (tag : Tag.t) =
  match tag.without_positions with
  | Var _ -> true
  | Modl_proj (modl, _) -> modl_is_value modl
  | Destr term -> term_is_value term

and modl_is_value (modl : Modl.t) =
  match modl.without_positions with
  | Var _ -> true
  | Modl_proj (modl, _) -> modl_is_value modl
  | Ap _ -> false
  | Ascribe (modl, _) -> modl_is_value modl
  | Body defn_list -> List.for_all defn_list ~f:defn_is_value
;;

let rec defn_value_has_exposed_uses (defn : Defn.t) ~of_ =
  match defn.without_positions with
  | Val (_, term) -> term_value_has_exposed_uses term ~of_
  | Tag (_, _, tag) -> tag_value_has_exposed_uses tag ~of_
  | Fun _ -> false
  | Modl (_, arg_opt, _, modl) ->
    (match arg_opt with
     | Some _ -> false
     | None -> modl_value_has_exposed_uses modl ~of_)
  | Include modl -> modl_value_has_exposed_uses modl ~of_
  (* CR wduff: It is unclear whether we should support
     recursive signatures, but right now we do not. *)
  | Sigture _sigture -> true
  | TypAlias (_, _, typ) -> typ_has_exposed_uses typ ~of_
  | InfixTyp _ | InfixTerm _ | SumTyp (_, _, _) -> false

and typ_has_exposed_uses typ ~of_ =
  match typ.without_positions with
  | Var (_, name) -> Set.mem of_ (`Typ, name)
  | Modl_proj (modl, _) -> modl_value_has_exposed_uses modl ~of_
  | Ap typs -> List.exists typs ~f:(typ_has_exposed_uses ~of_)
  | Record fields -> List.exists fields ~f:(fun (_, typ) -> typ_has_exposed_uses typ ~of_)
  | Forall (_, typ) -> typ_has_exposed_uses typ ~of_

and term_value_has_exposed_uses term ~of_ =
  match term.without_positions with
  | Var (_, name) -> Set.mem of_ (`Val, name)
  | Modl_proj (modl, _) -> modl_value_has_exposed_uses modl ~of_
  | Fun _ | Number _ | String _ | Built_in _ -> false
  | Record fields -> List.exists fields ~f:(fun (_, term) -> term_value_has_exposed_uses term ~of_)
  | Ascribe (term, _) -> term_value_has_exposed_uses term ~of_
  | Ap _ | Match (_, _) | Let (_, _) -> assert false

and tag_value_has_exposed_uses tag ~of_ =
  match tag.without_positions with
  | Var (_, name) -> Set.mem of_ (`Tag, name)
  | Modl_proj (modl, _) -> modl_value_has_exposed_uses modl ~of_
  | Destr term -> term_value_has_exposed_uses term ~of_

and modl_value_has_exposed_uses modl ~of_ =
  match modl.without_positions with
  | Var (_, name) -> Set.mem of_ (`Modl, name)
  | Modl_proj (modl, _) -> modl_value_has_exposed_uses modl ~of_
  | Ascribe (modl, _) -> modl_value_has_exposed_uses modl ~of_
  | Body defns -> List.exists defns ~f:(defn_value_has_exposed_uses ~of_)
  | Ap _ -> assert false
;;

let rec names_defined_by_pat (pat : Pat.t) =
  match pat.without_positions with
  | Wild -> String.Set.empty
  | Var (_, name) -> String.Set.singleton name
  | Record fields ->
    String.Set.union_list
      (List.map fields
         ~f:(fun (_, pat) -> names_defined_by_pat pat))
  | Tag (_, pat_opt) ->
    (match pat_opt with
     | None -> String.Set.empty
     | Some pat -> names_defined_by_pat pat)
  | Number _ -> String.Set.empty
  | String _ -> String.Set.empty
  | Ascribe (pat, _) -> names_defined_by_pat pat
;;

let names_defined_by_defn (defn : Defn.t) =
  match defn.without_positions with
  | InfixTyp _ | InfixTerm _ -> Sorted_name.Set.empty
  | TypAlias (name, _, _) ->
    Sorted_name.Set.singleton (`Typ, name)
  | SumTyp (name, _, cases) ->
    Set.add
      (Sorted_name.Set.union_list
         (List.map cases
            ~f:(fun (name, _) ->
              Sorted_name.Set.of_list [(`Val, name); (`Tag, name)])))
      (`Typ, name)
  | Tag (name, _, _) -> Sorted_name.Set.singleton (`Tag, name)
  | Val (pat, _) ->
    Set.map
      (module Sorted_name)
      (names_defined_by_pat pat)
      ~f:(fun name -> (`Val, name))
  | Fun (name, _, _, _) -> Sorted_name.Set.singleton (`Val, name)
  | Sigture (name, _) -> Sorted_name.Set.singleton (`Sigture, name)
  | Modl (name, _, _, _) -> Sorted_name.Set.singleton (`Modl, name)
  | Include _ -> Sorted_name.Set.empty
;;

let names_declared_by_decl (decl : Decl.t) =
  match decl.without_positions with
  | InfixTyp _ | InfixTerm _ -> Sorted_name.Set.empty
  | Typ (name, _, _) -> Sorted_name.Set.singleton (`Typ, name)
  | Tag (name, _, _) -> Sorted_name.Set.singleton (`Tag, name)
  | Val (name, _) -> Sorted_name.Set.singleton (`Val, name)
  | Sigture (name, _) -> Sorted_name.Set.singleton (`Sigture, name)
  | Modl (name, _) -> Sorted_name.Set.singleton (`Modl, name)
  | Include _ -> Sorted_name.Set.empty
;;
