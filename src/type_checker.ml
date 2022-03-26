open! Core
open! Import
open Typed

module Context = Context.Internal

let option_var = Typ.Var.create "option"

module Field_sort = struct
  type _ t =
    | Typ : Kind.t t
    | Val : Typ.t t
    | Tag : (Typ.t * Typ.t option) t
    | Modl : Sigture.t t

  module Untyped = struct
    type t =
      | Typ
      | Val
      | Tag
      | Modl
    [@@deriving sexp]
  end

  let to_untyped (type a) (t : a t) : Untyped.t =
    match t with
    | Typ -> Typ
    | Val -> Val
    | Tag -> Tag
    | Modl -> Modl
  ;;

  let sexp_of_t _ t = [%sexp_of: Untyped.t] (to_untyped t)
end

let rec lookup_field_in_decls' : type a. Modl.t -> Decls.t -> a Field_sort.t -> string -> a option =
  fun modl decls sort field ->
    let open Decls in
    match out decls with
    | End -> None
    | Cons ((field', decl), decls) ->
      (match decl with
       | Decl.Typ (typ_var, kind) ->
         (match sort with
          | Field_sort.Typ when String.equal field field' -> Some kind
          | _ ->
            lookup_field_in_decls' modl
              (Decls.subst Typ (Typ.modl_proj (modl, field')) typ_var decls)
              sort field)
       | Decl.Tag (typ, typ_opt) ->
         (match sort with
          | Field_sort.Tag when String.equal field field' -> Some (typ, typ_opt)
          | _ -> lookup_field_in_decls' modl decls sort field)
       | Decl.Val typ ->
         (match sort with
          | Field_sort.Val when String.equal field field' -> Some typ
          | _ -> lookup_field_in_decls' modl decls sort field)
       | Decl.Modl (modl_var, sigture) ->
         (match sort with
          | Field_sort.Modl when String.equal field field' -> Some sigture
          | _ ->
            lookup_field_in_decls' modl
              (Decls.subst Modl (Modl.modl_proj (modl, field')) modl_var decls)
              sort field))
;;

let lookup_field_in_decls modl decls sort field =
  match lookup_field_in_decls' modl decls sort field with
  | Some x -> x
  | None ->
    raise_s
      [%message
        "Could not find field in decls."
          (decls : Decls.t)
          (sort : _ Field_sort.t)
          (field : string)]
;;

let rec lookup_field_in_sigture : type a. Modl.t -> Sigture.t -> a Field_sort.t -> string -> a = fun modl sigture sort field ->
  let open Sigture in
  match out sigture with
  | Arrow _ -> failwith "???2"
  | Proj_arrow (_, sigture) ->
    (match (sort : a Field_sort.t) with
     | Field_sort.Typ ->
       lookup_field_in_sigture modl sigture (sort : a Field_sort.t) field
     | Field_sort.Modl ->
       (* CR wduff: This seems wrong. I think we need to strip the resulting signature of its
          non-type components (i.e. phase-split out the compile-time component). Otherwise we risk a
          later value or tag lookup on the returned signature giving back a type with unbound type
          variables. *)
       lookup_field_in_sigture modl sigture sort field
     | _ -> failwith "???" )
  | Body decls -> lookup_field_in_decls modl decls sort field
  | Rec (modl_var, sigture) ->
    lookup_field_in_sigture
      modl (Sigture.subst Modl modl modl_var sigture) sort field
;;

let typ_is_uvar typ =
  match Typ.out typ with
  | UVar uvar -> Some uvar
  | _ -> None
;;

let rec natural_kind (context : Context.t) path =
  match Typ.out path with
  | Var var ->
    (match Map.find context.typs var with
     | None -> failwith "???replace with legit error message."
     | Some kind -> kind)
  | Modl_proj (modl, field) ->
    lookup_field_in_sigture modl (natural_sigture context modl) Field_sort.Typ field
  | Ap (path, typ) ->
    (match Kind.out (natural_kind context path) with
     | Kind.Arrow ((var, _), kind2) ->
       Kind.subst Typ typ var kind2
     | _ -> failwithf !"???replace with legit error message. %{sexp: Typ.t} %{sexp: Typ.t}" path typ ())
  | UVar _ | Arrow _ | Forall _ | Record _ | Sum _ | Number | Char | String ->
    (* CR wduff: Check that the inner types have kind typ here? *)
    Kind.typ ()
  | Fun _ ->
    failwith "compiler bug"

and natural_sigture context modl_path =
  match Modl.out modl_path with
  | Var var ->
    (match Map.find context.modls var with
     | None -> failwith "???replace with legit error message."
     | Some sigture -> sigture)
  | Modl_proj (modl_path', field) ->
    lookup_field_in_sigture
      modl_path'
      (natural_sigture context modl_path')
      Field_sort.Modl
      field
  | _ ->
    failwithf
      !"compiler bug %{sexp: Modl.t}"
      modl_path ()
;;

let rec weak_normalize context typ =
  let rec reduce typ =
    match Typ.out typ with
    | Ap (c1, c2) ->
      (match Typ.out (reduce c1) with
       | Typ.Fun ((var, _kind), c1') -> reduce (Typ.subst Typ c2 var c1')
       | c1' -> Typ.ap (Typ.into c1', c2))
    | Modl_proj (modl, field) ->
      (match Modl.out (reduce_modl modl) with
       | Modl.Body fields ->
         List.find_map_exn fields
           ~f:(fun (field_name, modl_field) ->
             match modl_field with
             | Typ typ when String.equal field_name field -> Some (reduce typ)
             | _ -> None)
       | modl' -> Typ.modl_proj (Modl.into modl', field))
    | _ -> typ

  and reduce_modl modl =
    match Modl.out modl with
    | Modl_proj (modl', field) ->
      (match Modl.out (reduce_modl modl') with
       | Modl.Body fields ->
         List.find_map_exn fields
           ~f:(fun (field_name, modl_field) ->
             match modl_field with
             | Modl modl'' when String.equal field_name field -> Some (reduce_modl modl'')
             | _ -> None)
       | modl'' -> Modl.modl_proj (Modl.into modl'', field))
    | Proj_fun (_, modl') -> reduce_modl modl'
    | Proj_ap (modl', _) -> reduce_modl modl'
    | Rec ((_modl_var, _sigture), _modl') ->
      (* ??? sigture must be transparent, so we should be able
         to find a canonical implementation of the static part. *)
      failwith "unimpl"
    | _ -> modl
  in
  let typ' = reduce typ in
  match Kind.out (natural_kind context typ') with
  | Kind.Sing typ'' -> weak_normalize context typ''
  | _ -> typ'
  | exception exn ->
    let backtrace = Backtrace.get () in
    raise_s
      [%message
        "weak_normalize failed"
          (context : Context.t)
          (typ : Typ.t)
          (exn : exn)
          (Backtrace.to_string backtrace : string)]
;;

module Uvar_set =
  Set.Make_plain (struct
    type t = Typ.t Unification.Var.t [@@deriving sexp_of]

    let compare t1 t2 = Unification.Var.compare_tips t1 t2
  end)

let rec uvars_in_sigture sigture =
  match Sigture.out sigture with
  | Arrow ((_arg_var, arg_sigture), result_sigture)
  | Proj_arrow ((_arg_var, arg_sigture), result_sigture) ->
    Set.union (uvars_in_sigture arg_sigture) (uvars_in_sigture result_sigture)
  | Body decls -> uvars_in_decls decls
  | Rec (_modl_var, sigture) -> uvars_in_sigture sigture

and uvars_in_decls decls =
  (* We have an inner loop so that our list iteration is tail-recursive. We don't care about the
     overall process being tail recursive, because it will be proportional to the depth of the
     code, whereas this loop is proportionaly to the _length_ of the code. *)
  let rec loop decls acc =
    match Decls.out decls with
    | End -> acc
    | Cons ((_, decl), rest) ->
      let decl_uvars =
        match decl with
        | Decl.Typ (_, kind) -> uvars_in_kind kind
        | Decl.Tag (typ1, typ2_opt) ->
          let typ2_uvars =
            match typ2_opt with
            | None -> Uvar_set.empty
            | Some typ2 -> uvars_in_typ typ2
          in
          Set.union (uvars_in_typ typ1) typ2_uvars
        | Decl.Val typ -> uvars_in_typ typ
        | Decl.Modl (_, sigture) -> uvars_in_sigture sigture
      in
      loop rest (Set.union acc decl_uvars)
  in
  loop decls Uvar_set.empty

and uvars_in_kind kind =
  match Kind.out kind with
  | Typ -> Uvar_set.empty
  | Sing typ -> uvars_in_typ typ
  | Arrow ((_, kind1), kind2) -> Set.union (uvars_in_kind kind1) (uvars_in_kind kind2)

and uvars_in_typ typ =
  match Typ.out typ with
  | Var _ | Number | Char | String -> Uvar_set.empty
  | UVar uvar ->
    begin
      match
        Unification.tip_or_non_uvar_value
          ~value_of_uvar:Typ.uvar
          ~value_is_uvar:typ_is_uvar
          uvar
      with
      | `Tip uvar -> Uvar_set.singleton uvar
      | `Non_uvar_value typ -> uvars_in_typ typ
    end
  | Modl_proj (modl, _) -> uvars_in_modl modl
  | Fun ((_, kind), typ) | Forall ((_, kind), typ) ->
    Set.union (uvars_in_kind kind) (uvars_in_typ typ)
  | Ap (typ1, typ2) | Typ.Arrow (typ1, typ2) ->
    Set.union (uvars_in_typ typ1) (uvars_in_typ typ2)
  | Sum typs ->
    Uvar_set.union_list (List.map typs ~f:uvars_in_typ)
  | Record typs ->
    Uvar_set.union_list (List.map (Map.data typs) ~f:uvars_in_typ)

and uvars_in_modl modl =
  match Modl.out modl with
  | Var _ -> Uvar_set.empty
  | Modl_proj (modl, _) -> uvars_in_modl modl
  | Fun ((_, sigture), modl)
  | Proj_fun ((_, sigture), modl)
  | Rec ((_, sigture), modl) ->
    Set.union (uvars_in_sigture sigture) (uvars_in_modl modl)
  | Ap (modl1, modl2) -> Set.union (uvars_in_modl modl1) (uvars_in_modl modl2)
  | Proj_ap (modl1, modl2) -> Set.union (uvars_in_modl modl1) (uvars_in_modl modl2)
  | Ascribe (modl, sigture) ->
    Set.union (uvars_in_modl modl) (uvars_in_sigture sigture)
  | Body fields ->
    Uvar_set.union_list
      (List.map fields ~f:(fun (_str, field) -> uvars_in_modl_field field))
  | Dep_body defns ->
    uvars_in_defns defns
  | Let (defn, modl) ->
    Set.union (uvars_in_defn defn) (uvars_in_modl modl)

and uvars_in_modl_field modl_field =
  match modl_field with
  | Typ typ -> uvars_in_typ typ
  | Tag tag -> uvars_in_tag tag
  | Val term -> uvars_in_term term
  | Modl modl -> uvars_in_modl modl

and uvars_in_tag tag =
  match Tag.out tag with
  | Var _ | Tag.In _ -> Uvar_set.empty
  | Modl_proj (modl, _) -> uvars_in_modl modl
  | Destr term -> uvars_in_term term

and uvars_in_term term =
  match Term.out term with
  | Var _ | Number _ | Char _ | String _ -> Uvar_set.empty
  | Modl_proj (modl, _) -> uvars_in_modl modl
  | Fun ((args, typ_opt), term) ->
    let typ_uvars =
      match typ_opt with
      | None -> Uvar_set.empty
      | Some typ -> uvars_in_typ typ
    in
    let arg_uvars = Uvar_set.union_list (List.map args ~f:uvars_in_pat) in
    Set.union
      (Set.union typ_uvars arg_uvars)
      (uvars_in_term term)
  | Typ_fun ((_, kind), term) ->
    Set.union (uvars_in_kind kind) (uvars_in_term term)
  | Ap (term1, term2) -> Set.union (uvars_in_term term1) (uvars_in_term term2)
  | Typ_ap (term, typ) -> Set.union (uvars_in_term term) (uvars_in_typ typ)
  | Record terms -> Uvar_set.union_list (List.map (Map.data terms) ~f:uvars_in_term)
  | In (_, _, term) -> uvars_in_term term
  | Match (term, cases) ->
    Set.union
      (uvars_in_term term)
      (Uvar_set.union_list
         (List.map cases
            ~f:(fun (pat, term) ->
              Set.union (uvars_in_pat pat) (uvars_in_term term))))
  | Built_in (_, typ) -> uvars_in_typ typ
  | Ascribe (term, typ) ->
    Set.union (uvars_in_term term) (uvars_in_typ typ)
  | Let (defn, term) -> Set.union (uvars_in_defn defn) (uvars_in_term term)

and uvars_in_defn = function
  | Defn.Typ (_, typ) -> uvars_in_typ typ
  | Defn.Tag (_, tag) -> uvars_in_tag tag
  | Defn.Val (_, term) -> uvars_in_term term
  | Defn.Modl (_, modl) -> uvars_in_modl modl

and uvars_in_defns defns =
  match Defns.out defns with
  | Defns.End -> Uvar_set.empty
  | Defns.Cons ((_, defn), defns) ->
    Set.union (uvars_in_defn defn) (uvars_in_defns defns)

and uvars_in_pat = function
  | Pat.Wild | Pat.Var _ | Pat.Number _ | Pat.String _ -> Uvar_set.empty
  | Pat.Record pats -> Uvar_set.union_list (List.map (Map.data pats) ~f:uvars_in_pat)
  | Pat.Tag (tag, pat_opt) ->
    Set.union (uvars_in_tag tag)
      (match pat_opt with
       | None -> Uvar_set.empty
       | Some pat -> uvars_in_pat pat)
  | Pat.Ascribe (pat, typ) ->
    Set.union (uvars_in_pat pat) (uvars_in_typ typ)
;;

let rec subkind context kind kind' =
  match (Kind.out kind, Kind.out kind') with
  | (Typ, Typ) | (Sing _, Typ) -> true
  | (Sing typ, Sing typ') ->
    typ_equiv context typ typ' (Kind.typ ())
  | (Arrow ((var, kind1), kind2), Arrow ((var', kind1'), kind2')) ->
    subkind context kind1' kind1
    && subkind
         (Context.add_typ context var kind1')
         kind2 (Kind.subst Typ (Typ.var var) var' kind2')
  | _ -> false

and kind_equiv context kind kind' =
  subkind context kind kind'
  && subkind context kind' kind

(* ??? test that this is reflexive *)
and typ_equiv context typ1 typ2 kind =
  match Kind.out kind with
  | Typ ->
    begin
      match
        (* CR wduff: We need to keep track of the context in which a unification var is created, and
           check when we unify that the type we are unifying with is well-defined within the context
           where the unifcation variable was created. Otherwise, type variables may escape their
           scope. When unifying two unification variables, we should restrict the resulting variable
           to the intersection of the two contexts. *)
        (* CR wduff: Is it correct that we don't need to weak_normalize again after doing the
           unification find? Are we assuming uvars always point to paths? *)
        Unification.unify
          ~value_of_uvar:Typ.uvar
          ~value_is_uvar:typ_is_uvar
          ~occurs:(fun ~tip ~in_ ->
            Set.mem (uvars_in_typ in_) tip)
          (weak_normalize context typ1)
          (weak_normalize context typ2)
      with
      | `Ok -> true
      | `These_must_be_equal (path1, path2) ->
        Option.is_some (path_equiv context path1 path2)
    end
  | Sing _ -> true
  | Arrow ((var, kind), kind') ->
    typ_equiv
      (Context.add_typ context var kind)
      (Typ.ap (typ1, Typ.var var))
      (Typ.ap (typ2, Typ.var var))
      kind'

and path_equiv context path1 path2 =
  match (Typ.out path1, Typ.out path2) with
  | (Typ.Var var1, Typ.Var var2) ->
    if Typ.Var.equal var1 var2
    then Some (Map.find_exn context.typs var1)
    else None
  | (Typ.Modl_proj (modl_path1, field1), Typ.Modl_proj (modl_path2, field2)) ->
    if not (String.equal field1 field2)
    then None
    else begin
      match modl_path_equiv context modl_path1 modl_path2 with
      | Some sigture ->
        Some (lookup_field_in_sigture modl_path1 sigture Typ field1)
      | _ -> None
    end
  | (Typ.Ap (path1', typ1), Typ.Ap (path2', typ2)) ->
    (Option.bind (path_equiv context path1' path2') ~f:(fun kind ->
       match Kind.out kind with
       | Arrow ((var, kind), kind') ->
         if typ_equiv context typ1 typ2 kind
         then Some (Kind.subst Typ typ1 var kind')
         else None
       | _ -> None))
  | (Typ.Arrow (typ1, typ1'), Typ.Arrow (typ2, typ2')) ->
    if typ_equiv context typ1 typ2 (Kind.typ ())
    && typ_equiv context typ1' typ2' (Kind.typ ())
    then Some (Kind.typ ())
    else None
  | (Typ.Forall ((var1, kind1), typ1), Typ.Forall ((var2, kind2), typ2)) ->
    if not (kind_equiv context kind1 kind2)
    then None
    else begin
      if typ_equiv
           (Context.add_typ context var1 kind1)
           typ1
           (Typ.subst Typ (Typ.var var1) var2 typ2)
           (Kind.typ ())
      then Some (Kind.typ ())
      else None
    end
  | (Typ.Record fields1, Typ.Record fields2) ->
    if Map.equal
         (fun typ1 typ2 -> typ_equiv context typ1 typ2 (Kind.typ ()))
         fields1
         fields2
    then Some (Kind.typ ())
    else None
  | (Typ.Sum typs1, Typ.Sum typs2) ->
    if List.equal (fun typ1 typ2 -> typ_equiv context typ1 typ2 (Kind.typ ())) typs1 typs2
    then Some (Kind.typ ())
    else None
  | (Typ.Number, Typ.Number)
  | (Typ.Char, Typ.Char)
  | (Typ.String, Typ.String)
    ->
    Some (Kind.typ ())
  | _ -> None

and modl_path_equiv context modl_path1 modl_path2 =
  match (Modl.out modl_path1, Modl.out modl_path2) with
  | (Modl.Var var1, Modl.Var var2) ->
    if Modl.Var.equal var1 var2
    then
      Some
        (match Map.find context.modls var1 with
         | Some sigture -> sigture
         | None ->
           raise_s
             [%message
               "missing module var"
                 (var1 : Modl.Var.t)
                 (context : Context.t)])
    else None
  | (Modl.Modl_proj (modl_path1', field1),
     Modl.Modl_proj (modl_path2', field2)) ->
    if not (String.equal field1 field2)
    then None
    else begin
      match modl_path_equiv context modl_path1' modl_path2' with
      | Some sigture ->
        Some (lookup_field_in_sigture modl_path1' sigture Modl field1)
      | _ -> None
    end
  | _ -> None
;;

(* ??? implement *)
let subsigture _context _sigture1 _sigture2 = true

let rec check_term (context : Context.t) (term : Term.t) : Typ.t =
  let open Term in
  match Term.out term with
  | Var term_var ->
    begin
      match Map.find context.terms term_var with
      | Some typ -> typ
      | None ->
        raise_s [%message "No such value." (term_var : Term.Var.t)]
    end
  | Modl_proj (modl, field) ->
    let (purity, sigture) = check_modl context modl in
    if Purity.equal purity Impure then failwithf !"???3%{sexp: Modl.t}" modl () else ();
    lookup_field_in_sigture modl sigture Field_sort.Val field
  | Fun ((args, result_typ_opt), body) ->
    let (arg_typs, arg_contexts) =
      List.unzip (List.map args ~f:(check_pat context))
    in
    let body_context =
      List.fold arg_contexts
        ~init:context.terms
        ~f:(fun acc arg_context ->
          Map.fold arg_context
            ~init:acc
            ~f:(fun ~key ~data acc ->
              Map.set acc ~key ~data))
    in
    let body_typ = check_term { context with terms = body_context} body in
    let result_typ =
      match result_typ_opt with
      | None -> body_typ
      | Some result_typ ->
        if typ_equiv context result_typ body_typ (Kind.typ ())
        then result_typ
        else begin
          raise_s
            [%message
              "Result type of function is not equivalent to type of function body."
                (term : Term.t)
                (body_typ : Typ.t)
                (weak_normalize context result_typ : Typ.t)]
        end
    in
    List.fold_right arg_typs
      ~init:result_typ
      ~f:(fun arg_typ acc -> Typ.arrow (arg_typ, acc))
  | Typ_fun _ -> failwith "unimpl"
  | Ap (funct, arg) ->
    let funct_typ = check_term context funct in
    let arg_typ = check_term context arg in
    let result_typ = Typ.uvar (Unification.newvar ()) in
    if typ_equiv context funct_typ (Typ.arrow (arg_typ, result_typ)) (Kind.typ ())
    then result_typ
    else
      (* CR wduff: This error message is wrong. It might be that
         the arg type doesn't match the arg type of the function. *)
      raise_s
        [%message
          "Term used in application is non-function type"
            (context : Context.t)
            (funct : Term.t)
            (arg : Term.t)
            (funct_typ : Typ.t)
            (arg_typ : Typ.t)
            (weak_normalize context funct_typ : Typ.t)
            (weak_normalize context arg_typ : Typ.t)]
  | Typ_ap (funct, typ) ->
    let funct_typ = check_term context funct in
    let arg_kind = check_typ context typ in
    begin
      match Typ.out (weak_normalize context funct_typ) with
      | Forall ((arg_var, arg_kind'), result_typ) ->
        if kind_equiv context arg_kind arg_kind'
        then Typ.subst Typ typ arg_var result_typ
        else failwith "???4.5"
      | _ -> failwith "Term used in application is non-function type2"
    end
  | Record terms -> Typ.record (Map.map terms ~f:(check_term context))
  | In (n, i, term) ->
    if Int.between i ~low:0 ~high:(n - 1)
    then ()
    else failwith "???5";
    let typ_i = check_term context term in
    let typs =
      List.init n
        ~f:(fun j ->
            if Int.equal i j
            then typ_i
            else Typ.uvar (Unification.newvar ()))
    in
    Typ.sum typs
  | Match (term, cases) ->
    let term_typ = check_term context term in
    let result_typ = Typ.uvar (Unification.newvar ()) in
    List.iter cases
      ~f:(fun (pat, term) ->
        let (pat_typ, pat_context) = check_pat context pat in
        if typ_equiv context pat_typ term_typ (Kind.typ ())
        then ()
        else begin
          failwith
            "Type of term in match statement is \
             not equivalent to type of pattern"
        end;
        let result_context =
          Map.fold pat_context
            ~init:context.terms
            ~f:(fun ~key ~data acc ->
              Map.set acc ~key ~data)
        in
        let result_typ' =
          check_term { context with terms = result_context } term
        in
        if typ_equiv context result_typ result_typ' (Kind.typ ())
        then ()
        else
          raise_s
            [%message
              "???6"
                (context : Context.t)
                (pat : Pat.t)
                (term : Term.t)
                (result_typ : Typ.t)
                (result_typ' : Typ.t)
                (weak_normalize context result_typ : Typ.t)
                (weak_normalize context result_typ' : Typ.t)]);
    result_typ
  | Number _ -> Typ.number ()
  | Char _ -> Typ.char ()
  | String _ -> Typ.string ()
  | Built_in (_, typ) -> typ
  | Let (defn, term) ->
    (match defn with
     | Defn.Typ (typ_var, typ) ->
       let kind = check_typ context typ in
       let context' = Context.add_typ context typ_var (singleton typ kind) in
       Typ.subst Typ typ typ_var (check_term context' term)
     | Defn.Tag (tag_var, tag) ->
       let tag_typs = check_tag context tag in
       let context' = Context.add_tag context tag_var tag_typs in
       check_term context' term
     | Defn.Val (term_var, term') ->
       let term'_typ = check_term context term' in
       check_term (Context.add_term context term_var term'_typ) term
     | Modl (modl_var, modl) ->
       let (_purity, sigture') = check_modl context modl in
       let context' =
         Context.add_modl context modl_var
           (selfify_sigture (Modl.var modl_var) sigture')
       in
       (* CR wduff: existential will escape its scope here... *)
       check_term context' term)
  | Ascribe (term, typ) ->
    let kind = check_typ context typ in
    if subkind context kind (Kind.typ ())
    then ()
    else failwith "???7";
    let typ' = check_term context term in
    if typ_equiv context typ typ' (Kind.typ ())
    then typ
    else failwith "???8"

and singleton typ (kind : Kind.t) =
  match Kind.out kind with
  | Typ -> Kind.sing typ
  | Sing _ -> kind
  | Arrow ((typ_var, kind1), kind2) ->
    Kind.arrow
      ((typ_var, kind1), singleton (Typ.ap (typ, Typ.var typ_var)) kind2)

and selfify_decls modl (decls : Decls.t) : Decls.t =
  match Decls.out decls with
  | End -> Decls.end_ ()
  | Cons ((name, decl), rest) ->
    let selfified_decl =
      match decl with
      | Tag _ | Val _ -> decl
      | Typ (typ_var, kind) ->
        Typ (typ_var, singleton (Typ.modl_proj (modl, name)) kind)
      | Modl (modl_var, sigture) ->
        Modl (modl_var, selfify_sigture (Modl.modl_proj (modl, name)) sigture)
    in
    Decls.cons ((name, selfified_decl), selfify_decls modl rest)

and selfify_sigture modl (sigture : Sigture.t) =
  match Sigture.out sigture with
  | Arrow _ -> sigture
  | Proj_arrow ((arg_var, arg_sigture), result_sigture) ->
    Sigture.proj_arrow ((arg_var, arg_sigture), selfify_sigture modl result_sigture)
  | Body decls ->
    Sigture.body (selfify_decls modl decls)
  | Rec (modl_var, sigture') ->
    selfify_sigture modl (Sigture.subst Modl modl modl_var sigture')

and check_typ context (typ : Typ.t) : Kind.t =
  let open Typ in
  match Typ.out typ with
  | Var v -> Map.find_exn context.typs v
  | UVar _ -> Kind.typ ()
  | Modl_proj (modl, field) ->
    let (purity, sigture) = check_modl context modl in
    if Purity.equal purity Impure then failwith "???9" else ();
    lookup_field_in_sigture modl sigture Field_sort.Typ field
  | Fun ((arg_var, kind), body) ->
    check_kind context kind;
    let arg_var_context =
      Map.set context.typs ~key:arg_var ~data:kind
    in
    let kind' = check_typ { context with typs = arg_var_context } body in
    Kind.arrow ((arg_var, kind), kind')
  | Ap (funct, arg) ->
    let ((funct_arg_var, funct_arg_kind), funct_body_kind) =
      match Kind.out (check_typ context funct) with
      | Kind.Arrow f -> f
      | _ -> failwith "???10"
    in
    let arg_kind = check_typ context arg in
    if subkind context arg_kind funct_arg_kind
    then ()
    else failwith "???11";
    Kind.subst Typ arg funct_arg_var funct_body_kind
  | Arrow (arg, result) ->
    if subkind context (check_typ context arg) (Kind.typ ())
    && subkind context (check_typ context result) (Kind.typ ())
    then (Kind.typ ())
    else failwith "???12"
  | Forall ((arg_var, kind), typ) ->
    check_kind context kind;
    let context' =
      { context with
        typs = Map.set context.typs ~key:arg_var ~data:kind
      }
    in
    let kind' = check_typ context' typ in
    if subkind context' kind' (Kind.typ ())
    then Kind.typ ()
    else failwith "???12.5"
  | Sum typs ->
    if List.for_all typs
         ~f:(fun typ ->
           subkind context (check_typ context typ) (Kind.typ ()))
    then Kind.typ ()
    else failwith "???13"
  | Record typs ->
    if List.for_all (Map.data typs)
         ~f:(fun typ ->
           subkind context (check_typ context typ) (Kind.typ ()))
    then Kind.typ ()
    else failwith "???13"
  | Number -> Kind.typ ()
  | Char -> Kind.typ ()
  | String -> Kind.typ ()

and check_kind context (kind : Kind.t) =
  match Kind.out kind with
  | Typ -> ()
  | Sing typ ->
    if subkind context (check_typ context typ) (Kind.typ ())
    then ()
    else failwith "???14"
  | Arrow ((arg_var, arg), result) ->
    check_kind context arg;
    let context' = Context.add_typ context arg_var arg in
    check_kind context' result

and check_pat context (pat : Pat.t)
    : Typ.t * Typ.t Term.Var.Map.t =
  match pat with
  | Wild -> (Typ.uvar (Unification.newvar ()), Term.Var.Map.empty)
  | Var v ->
    let typ = Typ.uvar (Unification.newvar ()) in
    (typ, Term.Var.Map.singleton v typ)
  | Record pats ->
    let (pat_typs, pat_contexts) =
      List.unzip
        (List.map (Map.to_alist pats) ~f:(fun (field, pat) ->
           let (typ, context) = check_pat context pat in
           ((field, typ), context)))
    in
    let pat_typ = Typ.record (String.Map.of_alist_exn pat_typs) in
    let pat_context =
      List.fold pat_contexts
        ~init:Term.Var.Map.empty
        ~f:(fun acc pat_context ->
          Map.fold pat_context
            ~init:acc
            ~f:(fun ~key ~data acc ->
              Map.set acc ~key ~data))
    in
    (pat_typ, pat_context)
  | Tag (tag, pat_opt) ->
    let (from_typ, to_typ_opt) = check_tag context tag in
    (match (pat_opt, to_typ_opt) with
     | (None, None) -> (from_typ, Term.Var.Map.empty)
     | (Some pat, Some to_typ) ->
       let (pat_typ, pat_context) = check_pat context pat in
       if typ_equiv context pat_typ to_typ (Kind.typ ())
       then (from_typ, pat_context)
       else failwith "???15replace with legit error message."
     | _ -> failwith "???16replace with legit error message.")
  | Number _ -> (Typ.number (), Term.Var.Map.empty)
  | String _ -> (Typ.string (), Term.Var.Map.empty)
  | Ascribe (pat, typ) ->
    let kind = check_typ context typ in
    if subkind context kind (Kind.typ ())
    then ()
    else failwith "???17";
    let (pat_typ, pat_context) = check_pat context pat in
    if typ_equiv context pat_typ typ (Kind.typ ())
    then (typ, pat_context)
    else failwith "???18replace with legit error message."

and check_tag context (tag : Tag.t) =
  match Tag.out tag with
  | Var v -> Map.find_exn context.tags v
  | Modl_proj (modl, field) ->
    let (purity, sigture) = check_modl context modl in
    if Purity.equal purity Impure then failwith "???19" else ();
    lookup_field_in_sigture modl sigture Tag field
  | In (n, i) ->
    if Int.between i ~low:0 ~high:(n - 1)
    then ()
    else failwith "???20";
    let typs =
      List.init n
        ~f:(fun _ -> Typ.uvar (Unification.newvar ()))
    in
    (Typ.sum typs, Some (List.nth_exn typs i)) (*???*)
  | Destr term ->
    let typ = check_term context term in
    let u1 = Typ.uvar (Unification.newvar ()) in
    let u2 = Typ.uvar (Unification.newvar ()) in
    if
      typ_equiv
        context
        typ
        (Typ.arrow (u1, Typ.ap (Typ.var option_var, u2)))
        (Kind.typ ())
    then (u1, Some u2) (*???*)
    else failwith "???21"

and check_sigture context (sigture : Sigture.t) : unit =
  match Sigture.out sigture with
  | Arrow ((arg_var, arg_sigture), result_sigture) ->
    check_sigture context arg_sigture;
    check_sigture (Context.add_modl context arg_var arg_sigture) result_sigture
  | Proj_arrow ((arg_var, arg_sigture), result_sigture) ->
    check_sigture context arg_sigture;
    (* CR wduff: need to check that the typ part of [result_sigture]
       is well formed in the plain [context], not just [context'] *)
    check_sigture (Context.add_modl context arg_var arg_sigture) result_sigture
  | Body decls -> check_decls context decls
  | Rec (rec_var, sigture) ->
    (* CR wduff: This needs to check the typ part of [sigture] in [context]
       and then only add that to the context when checking the full [sigture]. *)
    check_sigture (Context.add_modl context rec_var sigture) sigture

and check_decls context (decls : Decls.t) : unit =
  match Decls.out decls with
  | End -> ()
  | Cons ((_, decl), decls) ->
    match decl with
    | Typ (typ_var, kind) ->
      check_kind context kind;
      check_decls (Context.add_typ context typ_var kind) decls
    | Tag (typ1, typ2_opt) ->
      if subkind context (check_typ context typ1) (Kind.typ ())
      then ()
      else failwith "???";
      (match typ2_opt with
       | None -> ()
       | Some typ2 ->
         if subkind context (check_typ context typ2) (Kind.typ ())
         then ()
         else failwith "???");
      check_decls context decls
    | Val typ ->
      if subkind context (check_typ context typ) (Kind.typ ())
      then ()
      else failwith "???";
      check_decls context decls
    | Modl (modl_var, sigture) ->
      check_sigture context sigture;
      check_decls (Context.add_modl context modl_var sigture) decls

and check_modl context (modl : Modl.t) : Purity.t * Sigture.t =
  match Modl.out modl with
  | Var modl_var ->
    begin
      match Map.find context.modls modl_var with
      | Some sigture -> (Pure, sigture)
      | None ->
        raise_s
          [%message
            "No such module."
              (context : Context.t)
              (modl_var : Modl.Var.t)]
    end
  | Modl_proj (modl, field) ->
    let (purity, sigture) = check_modl context modl in
    if Purity.equal purity Impure then failwith "???22" else ();
    (Pure, lookup_field_in_sigture modl sigture Field_sort.Modl field)
  | Fun ((modl_var, sigture), body) ->
    check_sigture context sigture;
    let context' = Context.add_modl context modl_var sigture in
    let (_, sigture') = check_modl context' body in
    (Pure, Sigture.arrow ((modl_var, sigture), sigture'))
  | Proj_fun ((modl_var, sigture), body) ->
    (* CR wduff: need to check that the typ part of [body] is
       well formed in the plain [context], not just [context'] *)
    check_sigture context sigture;
    let context' = Context.add_modl context modl_var sigture in
    let (_, sigture') = check_modl context' body in
    (Pure, Sigture.proj_arrow ((modl_var, sigture), sigture'))
  | Ap (funct, arg) ->
    let (_, funct_sigture) = check_modl context funct in
    let (arg_purity, arg_sigture) = check_modl context arg in
    if Purity.equal arg_purity Impure then failwith "???23" else ();
    (match Sigture.out funct_sigture with
     | Sigture.Arrow ((modl_var, arg_sigture'), result_sigture) ->
       if subsigture context arg_sigture arg_sigture'
       then (Impure, Sigture.subst Modl arg modl_var result_sigture)
       else failwith "???24"
     | _ -> failwithf !"???25%{sexp: Sigture.t}" funct_sigture ())
  | Proj_ap (funct, arg) ->
    let (_, funct_sigture) = check_modl context funct in
    let (arg_purity, arg_sigture) = check_modl context arg in
    if Purity.equal arg_purity Impure then failwith "???23" else ();
    (match Sigture.out funct_sigture with
     | Sigture.Proj_arrow ((modl_var, arg_sigture'), result_sigture) ->
       if subsigture context arg_sigture arg_sigture'
       then (Pure, selfify_sigture funct (Sigture.subst Modl arg modl_var result_sigture))
       else failwith "???25.1"
     | _ -> failwithf !"???25.2%{sexp: Sigture.t}" funct_sigture ())
  | Ascribe (modl, sigture) ->
    let (_, sigture') = check_modl context modl in
    if subsigture context sigture' sigture
    then (Impure, sigture)
    else failwith "???26"
  | Rec ((modl_var, sigture), modl) ->
    check_sigture context sigture;
    let context' = Context.add_modl context modl_var sigture in
    let (_purity, sigture') = check_modl context' modl in
    (* CR wduff: if Purity.equal purity Impure then failwith "???27" else (); *)
    if subsigture context' sigture' sigture
    then (Pure, sigture)
    else failwith "???28"
  | Body fields ->
    let (purity, decls) =
      (* ??? keep field_name consistent everywhere else *)
      List.fold_right fields ~init:(Pure, Decls.end_ ())
        ~f:(fun (field_name, field) (purity, decls) ->
          let (purity', decl) = check_modl_field context field in
          (Purity.max purity purity',
           Decls.cons ((field_name, decl), decls)))
    in
    (purity, Sigture.body decls)
  | Dep_body defns ->
    let (purity, decls) = check_defns context defns in
    (purity, Sigture.body decls)
  | Let (defn, modl) ->
    (match defn with
     | Defn.Typ (typ_var, typ) ->
       let kind = check_typ context typ in
       let context' = Context.add_typ context typ_var (singleton typ kind) in
       let (purity, sigture) = check_modl context' modl in
       (purity, Sigture.subst Typ typ typ_var sigture)
     | Defn.Tag (tag_var, tag) ->
       let tag_typs = check_tag context tag in
       let context' = Context.add_tag context tag_var tag_typs in
       check_modl context' modl
     | Defn.Val (term_var, term) ->
       let typ = check_term context term in
       check_modl (Context.add_term context term_var typ) modl
    | Defn.Modl (modl_var, modl') ->
      let (purity', sigture') = check_modl context modl' in
      let context' =
        Context.add_modl context modl_var
          (selfify_sigture (Modl.var modl_var) sigture')
      in
      (* CR wduff: existential will escape its scope here... *)
      let (purity, sigture) = check_modl context' modl in
      (Purity.max purity' purity, sigture))

and check_defns context defns =
  match Defns.out defns with
  | Defns.End -> (Pure, Decls.end_ ())
  | Defns.Cons ((name, defn), defns) ->
    match defn with
    | Typ (typ_var, typ) ->
      let kind = check_typ context typ in
      let kind' = singleton typ kind in
      let (purity, decls) =
        check_defns (Context.add_typ context typ_var kind') defns
      in
      (purity, Decls.cons ((name, Decl.Typ (typ_var, kind')), decls))
    | Tag (tag_var, tag) ->
      let typs = check_tag context tag in
      let (purity, decls) =
        check_defns (Context.add_tag context tag_var typs) defns
      in
      (purity, Decls.cons ((name, Decl.Tag typs), decls))
    | Val (term_var, term) ->
      let typ = check_term context term in
      let (purity, decls) =
        check_defns (Context.add_term context term_var typ) defns
      in
      (purity, Decls.cons ((name, Decl.Val typ), decls))
    | Modl (modl_var, modl) ->
      let (purity, sigture) = check_modl context modl in
      let (purity', decls) =
        check_defns (Context.add_modl context modl_var sigture) defns
      in
      (Purity.max purity purity', Decls.cons ((name, Decl.Modl (modl_var, sigture)), decls))

and check_modl_field context field =
  match field with
  | Typ typ ->
    let kind = check_typ context typ in
    (Pure, Decl.Typ (Typ.Var.create " ", singleton typ kind))
  | Tag tag ->
    let (typ1, typ2_opt) = check_tag context tag in
    (Pure, Decl.Tag (typ1, typ2_opt))
  | Val term ->
    let typ = check_term context term in
    (Pure, Decl.Val typ)
  | Modl modl ->
    let (purity, sigture) = check_modl context modl in
    (purity, Decl.Modl (Modl.Var.create " ", sigture))
;;
