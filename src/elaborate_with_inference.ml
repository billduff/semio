open! Core
open! Import

module U = Unbound
module T = Typed

module Dependence = Graph.Persistent.Digraph.ConcreteBidirectional (Int)
module SCC = Graph.Components.Make (Dependence)

type before = U.Defn.t list
type after = T.Term.t

let singleton_decls decl =
  T.Decls.cons (decl, T.Decls.end_ ())
;;

let rec append_decls decls1 decls2 =
  match T.Decls.out decls1 with
  | T.Decls.End -> decls2
  | T.Decls.Cons (x, xs) ->
    T.Decls.cons (x, append_decls xs decls2)
;;

let rec decls_of_list = function
  | [] -> T.Decls.end_ ()
  | decl :: decls -> T.Decls.cons (decl, decls_of_list decls)
;;

module Invariant_checks = struct
  let maps_match data_matches map1 map2 =
    List.iter2_exn
      (Map.to_alist map1)
      (Map.to_alist map2)
      ~f:(fun (key1, data1) (key2, data2) ->
        assert (String.equal key1 key2);
        data_matches data1 data2)
  ;;

  let rec fixity_context_matches_elab_context (fixity : Context.Fixity.t) (elab : Context.Elab.t) =
    maps_match
      (fun a (_, b) -> fixity_sigture_matches_foo_sigture a b)
      fixity.sigtures
      elab.sigtures;
    maps_match
      (fun a (_, b) -> fixity_sigture_matches_elab_sigture a b)
      fixity.modls
      elab.modls

  and fixity_context_matches_elab_context_creator
        (fixity : Context.Fixity.t)
        (elab : Context.Elab_creator.t)
    =
    maps_match
      (fun a (_, b) -> fixity_sigture_matches_foo_sigture a b)
      fixity.sigtures
      elab.sigtures;
    maps_match
      (fun a (_, b) -> fixity_sigture_matches_elab_sigture a b)
      fixity.modls
      elab.modls

  and fixity_context_matches_foo_context (fixity : Context.Fixity.t) (foo : Context.Foo.t) =
    maps_match fixity_sigture_matches_foo_sigture fixity.sigtures foo.sigtures;
    maps_match fixity_sigture_matches_foo_sigture fixity.modls foo.modls

  and fixity_sigture_matches_elab_sigture fixity_sigture elab_sigture =
    match (fixity_sigture, elab_sigture) with
    | (Body fixity_context, Body elab_context_creator) ->
      fixity_context_matches_elab_context_creator fixity_context elab_context_creator
    | (Arrow fixity_sigture, Arrow (_, elab_sigture)) ->
      fixity_sigture_matches_elab_sigture fixity_sigture elab_sigture
    | ((Body _, Arrow _) | (Arrow _, Body _)) -> assert false

  and fixity_sigture_matches_foo_sigture fixity_sigture foo_sigture =
    match (fixity_sigture, foo_sigture) with
    | (Body fixity_context, Body foo_context) ->
      fixity_context_matches_foo_context fixity_context foo_context
    | (Arrow fixity_sigture, Arrow (_, foo_sigture)) ->
      fixity_sigture_matches_foo_sigture fixity_sigture foo_sigture
    | ((Body _, Arrow _) | (Arrow _, Body _)) -> assert false
  ;;

  let elab_context_type_checks (internal : Context.Internal.t) (elab : Context.Elab.t) =
    List.iter (String.Map.data elab.typs) ~f:(fun typ ->
      ignore (Type_checker.check_typ internal typ : T.Kind.t));
    List.iter (String.Map.data elab.tags) ~f:(fun tag ->
      ignore
        (Type_checker.check_tag internal (tag `Specialize)
         : T.Typ.t * T.Typ.t option));
    List.iter (String.Map.data elab.terms) ~f:(fun term ->
      ignore (Type_checker.check_term internal (term `Specialize) : T.Typ.t));
    List.iter (String.Map.data elab.sigtures) ~f:(fun (sigture, _foo_sigture) ->
      Type_checker.check_sigture internal sigture);
    List.iter (String.Map.data elab.modls) ~f:(fun (modl, _elab_sigture) ->
      (* CR wduff: Don't ignore elab_sigture *)
      ignore (Type_checker.check_modl internal (modl `Specialize) : Purity.t * T.Sigture.t))
  ;;

  let elab_context_creator_type_checks internal elab_context_creator sigture =
    let modl_var = T.Modl.Var.create " z" in
    let internal' = Context.Internal.add_modl internal modl_var sigture in
    let elab_context =
      Context.Elab_creator.apply elab_context_creator (T.Modl.var modl_var)
    in
    elab_context_type_checks internal' elab_context
  ;;

  let elab_sigture_matches_sigture
            (internal : Context.Internal.t)
            (elab_sigture : Context.Elab_sigture.t)
            (sigture : T.Sigture.t)
    =
    match elab_sigture with
    | Body elab_context_creator ->
      elab_context_creator_type_checks internal elab_context_creator sigture
    | Arrow (_foo_sigture, _elab_sigture) ->
      (* CR wduff: Implement. *)
      ()
  ;;

  let internal_context_well_formed ({ Context.Internal. typs; tags; terms; modls } as context)=
    Map.iter typs ~f:(fun _kind -> (* CR wduff: kind_ok kind *) ());
    Map.iter tags ~f:(fun (typ1, typ2_opt) ->
      ignore (Type_checker.check_typ context typ1 : T.Kind.t);
      Option.iter typ2_opt ~f:(fun typ2 ->
        ignore (Type_checker.check_typ context typ2 : T.Kind.t)));
    Map.iter terms ~f:(fun typ ->
      ignore (Type_checker.check_typ context typ : T.Kind.t));
    Map.iter modls ~f:(fun _sigture -> (* CR wduff: kind_ok kind *) ())
  ;;

  let context_well_formed { Context. fixity; elab; internal } : unit =
    begin
      try internal_context_well_formed internal
      with exn ->
        let backtrace = Backtrace.get () in
        raise_s
          [%message
            "interal context is not well formed"
              (internal : Context.Internal.t)
              (exn : exn)
              (Backtrace.to_string backtrace : string)]
    end;
    begin
      try fixity_context_matches_elab_context fixity elab
      with exn ->
        let backtrace = Backtrace.get () in
        raise_s
          [%message
            "fixity context doesn't match elab context"
              (fixity : Context.Fixity.t)
              (elab : Context.Elab.t)
              (exn : exn)
              (Backtrace.to_string backtrace : string)]
    end;
    begin
      try elab_context_type_checks internal elab
      with exn ->
        let backtrace = Backtrace.get () in
        raise_s
          [%message
            "elab context doesn't type check"
              (internal : Context.Internal.t)
              (elab : Context.Elab.t)
              (exn : exn)
              (Backtrace.to_string backtrace : string)]
    end;
  ;;
end

let rec elab_sigture_of_foo_sigture = function
  | Context.Foo_sigture.Body foo_context ->
    Context.Elab_sigture.Body (elab_context_of_foo_context foo_context)
  | Context.Foo_sigture.Arrow (arg_foo_sigture, result_foo_sigture) ->
    Context.Elab_sigture.Arrow
      (arg_foo_sigture, elab_sigture_of_foo_sigture result_foo_sigture)

and elab_context_of_foo_context foo_context =
  { typs =
      List.map (Set.to_list foo_context.typs)
        ~f:(fun name -> (name, (fun modl -> T.Typ.modl_proj (modl, name))))
      |> String.Map.of_alist_exn
  ; tags =
      List.map (Set.to_list foo_context.tags)
        ~f:(fun name -> (name, (fun modl -> const (T.Tag.modl_proj (modl, name)))))
      |> String.Map.of_alist_exn
  ; terms =
      List.map (Set.to_list foo_context.terms)
        ~f:(fun name -> (name, (fun modl -> const (T.Term.modl_proj (modl, name)))))
      |> String.Map.of_alist_exn
  ; sigtures =
      Map.mapi foo_context.sigtures
        ~f:(fun ~key:_name ~data:foo_sigture ->
          (* CR wduff: *)
          (failwith "???", foo_sigture))
  ; modls =
      Map.mapi foo_context.modls
        ~f:(fun ~key:name ~data:foo_sigture ->
          ((fun modl -> const (T.Modl.modl_proj (modl, name))),
           elab_sigture_of_foo_sigture foo_sigture))
  }
;;

let rec foo_sigture_of_elab_sigture
          (elab_sigture : Context.Elab_sigture.t)
  : Context.Foo_sigture.t =
  match elab_sigture with
  | Body elab_context_creator ->
    Body (foo_context_of_elab_context_creator elab_context_creator)
  | Arrow (arg_foo_sigture, result_elab_sigture) ->
    Arrow (arg_foo_sigture, foo_sigture_of_elab_sigture result_elab_sigture)

and foo_context_of_elab_context_creator
      ({ typs
       ; tags
       ; terms
       ; sigtures
       ; modls
       }
       : Context.Elab_creator.t)
  : Context.Foo.t =
  { typs = String.Set.of_list (String.Map.keys typs)
  ; tags = String.Set.of_list (String.Map.keys tags)
  ; terms = String.Set.of_list (String.Map.keys terms)
  ; sigtures = String.Map.map sigtures ~f:snd
  ; modls =
      String.Map.map modls ~f:(fun (_, elab_sigture) ->
        foo_sigture_of_elab_sigture elab_sigture)
  }
;;

(* CR wduff: *)
let _ = foo_sigture_of_elab_sigture

let generalize
      (context : Context.t)
      modl
      sigture
      (elab_context_creator : Context.Elab_creator.t) =
  let sigture_uvars = Type_checker.uvars_in_sigture sigture in
  let context_uvars =
    let typ_uvars =
      Type_checker.Uvar_set.union_list
        (List.map (Map.data context.internal.typs)
           ~f:Type_checker.uvars_in_kind)
    in
    let tag_uvars =
      Type_checker.Uvar_set.union_list
        (List.map (Map.data context.internal.tags)
           ~f:(fun (typ1, typ2) ->
             Set.union
               (Type_checker.uvars_in_typ typ1)
               (match typ2 with
                | Some typ2 -> Type_checker.uvars_in_typ typ2
                | None -> Type_checker.Uvar_set.empty)))
    in
    let term_uvars =
      Type_checker.Uvar_set.union_list
        (List.map (Map.data context.internal.terms)
           ~f:Type_checker.uvars_in_typ)
    in
    let modl_uvars =
      Type_checker.Uvar_set.union_list
        (List.map (Map.data context.internal.modls)
           ~f:Type_checker.uvars_in_sigture)
    in
    Type_checker.Uvar_set.union_list
      [typ_uvars; tag_uvars; term_uvars; modl_uvars]
  in
  let uvars_to_generalize = Set.diff sigture_uvars context_uvars in
  let arg_var = T.Modl.Var.create " a" in
  let fields =
    List.mapi (Set.to_list uvars_to_generalize)
      ~f:(fun i uvar -> (Int.to_string i, uvar))
  in
  let arg_sigture =
    T.Sigture.body
      (List.fold fields ~init:(T.Decls.end_ ())
         ~f:(fun acc (field, _) ->
           T.Decls.cons
             ((field, T.Decl.Typ (T.Typ.Var.create "_", T.Kind.typ ())), acc)))
  in
  begin
    let context =
      Context.Internal.add_modl context.internal arg_var arg_sigture
    in
    List.iter fields
      ~f:(fun (field, uvar) ->
        assert
          (Type_checker.typ_equiv context
             (T.Typ.uvar uvar) (T.Typ.modl_proj (T.Modl.var arg_var, field))
             (T.Kind.typ ())))
  end;
  let create_arg_for_specialization () =
    T.Modl.body
      (List.map fields ~f:(fun (field, _) ->
         (field, T.Modl_field.Typ (T.Typ.uvar (Unification.newvar ())))))
  in
  (T.Modl.proj_fun ((arg_var, arg_sigture), modl),
   T.Sigture.proj_arrow ((arg_var, arg_sigture), sigture),
   { elab_context_creator with
     tags =
       Map.map elab_context_creator.tags
         ~f:(fun f modl `Specialize ->
           f (T.Modl.proj_ap (modl, create_arg_for_specialization ())) `Specialize)
   ; terms =
       Map.map elab_context_creator.terms
         ~f:(fun f modl `Specialize ->
           f (T.Modl.proj_ap (modl, create_arg_for_specialization ())) `Specialize)
   ; sigtures =
       Map.map elab_context_creator.sigtures
         ~f:(fun (f, elab_sigture) ->
           ((fun modl -> f (T.Modl.proj_ap (modl, create_arg_for_specialization ()))),
            elab_sigture))
   ; modls =
       Map.map elab_context_creator.modls
         ~f:(fun (f, elab_sigture) ->
           ((fun modl `Specialize ->
              f (T.Modl.proj_ap (modl, create_arg_for_specialization ())) `Specialize),
            elab_sigture))
   })
;;

let rec coerce_modl
          context
          modl
          (elab_sigture : Context.Elab_sigture.t)
          (foo_sigture : Context.Foo_sigture.t) =
  match (elab_sigture, foo_sigture) with
  | (Arrow _, Body _) | (Body _, Arrow _) ->
    failwith "???replace with legit error message."
  | (Arrow _, Arrow _) -> failwith "unimpl1"
  | (Body elab_context_creator, Body foo_context) ->
    let var = T.Modl.Var.create " c" in
    let elab_context = Context.Elab_creator.apply elab_context_creator (T.Modl.var var) in
    let modl_fields =
      (* CR wduff: Add types and stuff to foo sigture and ascribe them here.
         Also deal with polymorphism. *)
      List.concat
        [ List.map (Set.to_list foo_context.typs) ~f:(fun name ->
            (name, T.Modl_field.Typ (Map.find_exn elab_context.typs name)))
        ; List.map (Set.to_list foo_context.tags) ~f:(fun name ->
            (name, T.Modl_field.Tag (Map.find_exn elab_context.tags name `Specialize)))
        ; List.map (Set.to_list foo_context.terms) ~f:(fun name ->
            (name, T.Modl_field.Val (Map.find_exn elab_context.terms name `Specialize)))
        ; List.map (Map.keys foo_context.sigtures) ~f:(fun _name -> failwith "???")
        ; List.map (Map.to_alist foo_context.modls) ~f:(fun (name, foo_sigture) ->
            let (modl, elab_sigture) = Map.find_exn elab_context.modls name in
            (name,
             T.Modl_field.Modl (coerce_modl context (modl `Specialize) elab_sigture foo_sigture)))
        ]
    in
    T.Modl.let_ (T.Defn.Modl (var, modl), T.Modl.body modl_fields)
;;

(* Preconditions:
   - [context] is well-formed
   - [kind] ok in [context] *)
(* Postconditions:
   - [result] : [kind] in [context] *)
let rec check_typ'
          (context : Context.t)
          (typ : U.Typ.t)
          (kind : T.Kind.t)
  : T.Typ.t =
  let (typ', kind') = synth_typ context typ in
  if Type_checker.subkind context.internal kind' kind
  then typ'
  else failwith "???replace with legit error message."

and check_typ context typ kind =
  Invariant_checks.context_well_formed context;
  (* CR wduff: assert (Type_checker.kind_ok kind) *)
  let typ' = check_typ' context typ kind in
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ')
       kind);
  typ'

(* Preconditions:
   - [context] is well-formed *)
(* Postconditions:
   if [result] = [(typ, kind)] then
   - [kind] ok in [context]
   - [typ] : [kind] in [context] *)
and synth_typ' (context : Context.t) (typ : U.Typ.t) : T.Typ.t * T.Kind.t =
  match typ.without_positions with
  | Var (code_pos, name) ->
    (match String.Map.find context.elab.typs name with
     | Some typ -> (typ, Type_checker.check_typ context.internal typ)
     | None ->
       raise_s
         [%message
           "No such type."
             (code_pos : Source_code_position.t)
             (name : string)
             (context : Context.t)])
  | Modl_proj (modl, field) ->
    let (modl', purity, _, elab_sigture, _) = synth_modl context modl in
    if Purity.equal purity Pure
    then
      match elab_sigture with
      | Context.Elab_sigture.Body elab_context_creator ->
        let typ = Map.find_exn elab_context_creator.typs field modl' in
        (typ, Type_checker.check_typ context.internal typ)
      | _ ->
        failwith "???replace with legit error message."
    else
      failwith "???replace with legit error message."
  | Ap typs ->
    Parse_infix.parse_infix [%sexp_of: U.Typ.t]
      ~is_infix:(fun (typ : U.Typ.t) ->
        match typ.without_positions with
        | U.Typ.Var (_, name) ->
          (match String.Map.find context.fixity.infix_typs name with
           | None -> false
           | Some _ -> true)
        | _ -> false)
      ~precedence:(fun typ1 typ2 ->
        match (typ1.without_positions, typ2.without_positions) with
        | (U.Typ.Var (_, name1), U.Typ.Var (_, name2)) ->
          String.Map.find
            (String.Map.find_exn context.fixity.infix_typs name1)
            name2
        | _ -> failwith "???compiler bug")
      ~convert:(synth_typ context)
      ~ap:(fun (typ1, kind1) (typ2, kind2) ->
        match T.Kind.out kind1 with
        | Arrow ((var, kind11), kind12) ->
          if Type_checker.subkind context.internal kind2 kind11
          then (T.Typ.ap (typ1, typ2), T.Kind.subst Typ typ2 var kind12)
          else failwith "???replace with legit error message."
        | _ ->
          let _ : _ =
            raise_s
              [%message
                ""
                  (typ1 : T.Typ.t)
                  (kind1 : T.Kind.t)
                  (typ2 : T.Typ.t)
                  (kind2 : T.Kind.t)]
          in
          failwith "???replace with legit error message.")
      typs
  | Record fields ->
    (List.map fields ~f:(fun (field, typ) ->
       (field, check_typ context typ (T.Kind.typ ())))
     |> String.Map.of_alist_exn
     |> T.Typ.record,
     T.Kind.typ ())
  | Forall (arg_name, result) ->
    let arg_var = T.Typ.Var.create arg_name in
    let context' =
      { context with
        elab =
          Context.Elab.add_typ context.elab arg_name (T.Typ.var arg_var)
      ; internal =
          Context.Internal.add_typ context.internal arg_var (T.Kind.typ ())
      }
    in
    let result' = check_typ context' result (T.Kind.typ ()) in
    (T.Typ.forall ((arg_var, T.Kind.typ ()), result'), (T.Kind.typ ()))

and synth_typ context typ =
  Invariant_checks.context_well_formed context;
  let (typ', kind) = synth_typ' context typ in
  (* CR wduff: assert (Type_checker.kind_ok kind) *)
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ')
       kind);
  (typ', kind)

(* Preconditions:
   - [context] is well-formed
   - [typ1] : [T.Kind.Typ] in [context]
   - if [typ2_opt] = [Some typ2] then [typ2] : [T.Kind.Typ] in [context] *)
(* Postconditions:
   - [result] : [typ1] => [typ2_opt] in [context] *)
and check_tag'
      (context : Context.t)
      (tag : U.Tag.t)
      (typ1 : T.Typ.t)
      (typ2_opt : T.Typ.t option)
  : T.Tag.t =
  let (tag', typ1', typ2_opt') = synth_tag context tag in
  if Type_checker.typ_equiv context.internal typ1 typ1' (T.Kind.typ ())
  && (match (typ2_opt', typ2_opt) with
      | (None, None) -> true
      | (Some typ2', Some typ2) ->
        Type_checker.typ_equiv context.internal typ2' typ2 (T.Kind.typ ())
      | _ -> false)
  then tag'
  else failwith "???replace with legit error message"

and check_tag context tag typ1 typ2_opt =
  Invariant_checks.context_well_formed context;
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ1)
       (T.Kind.typ ()));
  assert
    (match typ2_opt with
     | None -> true
     | Some typ2 ->
       Type_checker.subkind
         context.internal
         (Type_checker.check_typ context.internal typ2)
         (T.Kind.typ ()));
  let tag' = check_tag' context tag typ1 typ2_opt in
  let (typ1', typ2_opt') = Type_checker.check_tag context.internal tag' in
  assert
    (Type_checker.typ_equiv context.internal typ1 typ1' (T.Kind.typ ()));
  assert
    (Option.equal
       (fun typ2 typ2' ->
          Type_checker.typ_equiv
            context.internal
            typ2
            typ2'
            (T.Kind.typ ()))
       typ2_opt
       typ2_opt');
  tag'

(* Preconditions:
   - [context] is well-formed *)
(* Postconditions:
   if [result] = [(tag, typ1, typ2_opt)] then
   - [typ1] : [T.Kind.Typ] in [context]
   - if [typ2_opt] = [Some typ2] then [typ2] : [T.Kind.Typ] in [context]
   - [tag] : [typ1] => [typ2_opt] in [context] *)
and synth_tag' (context : Context.t) (tag : U.Tag.t) : T.Tag.t * T.Typ.t * T.Typ.t option =
  match tag.without_positions with
  | Var (code_pos, name) ->
    (match String.Map.find context.elab.tags name with
     | Some f ->
       let tag = f `Specialize in
       let (typ1, typ2_opt) = Type_checker.check_tag context.internal tag in
       (tag, typ1, typ2_opt)
     | None ->
       raise_s
         [%message
           "No such tag."
             (code_pos : Source_code_position.t)
             (name : string)
             (context : Context.t)])
  | Modl_proj (modl, field) ->
    let (modl', purity, _, elab_sigture, _) = synth_modl context modl in
    if Purity.equal purity Pure
    then
      match elab_sigture with
      | Body elab_context_creator ->
        let tag =
          match Map.find elab_context_creator.tags field with
          | Some f -> f modl' `Specialize
          | None ->
            raise_s [%message "No such tag in module." (modl' : T.Modl.t) (field : string)]
        in
        let (typ1, typ2_opt) = Type_checker.check_tag context.internal tag in
        (tag, typ1, typ2_opt)
      | _ ->
        failwith "???replace with legit error message"
    else
      failwith "???replace with legit error message"
  | Destr term ->
    let (term', typ) = synth_term context term in
    let typ1 = T.Typ.uvar (Unification.newvar ()) in
    let typ2 = T.Typ.uvar (Unification.newvar ()) in
    let typ2' = T.Typ.uvar (Unification.newvar ()) in
    if Type_checker.typ_equiv context.internal
         typ
         (T.Typ.arrow (typ1, typ2))
         (T.Kind.typ ())
    && Type_checker.typ_equiv context.internal
         typ2
         (T.Typ.ap (String.Map.find_exn context.elab.typs "option", typ2'))
         (T.Kind.typ ())
    then (T.Tag.destr term', typ1, Some typ2')
    else failwith "???replace with legit error message."

and synth_tag context tag =
  Invariant_checks.context_well_formed context;
  let (tag', typ1, typ2_opt) = synth_tag' context tag in
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ1)
       (T.Kind.typ ()));
  assert
    (match typ2_opt with
     | None -> true
     | Some typ2 ->
       Type_checker.subkind
         context.internal
         (Type_checker.check_typ context.internal typ2)
         (T.Kind.typ ()));
  let (typ1', typ2_opt') = Type_checker.check_tag context.internal tag' in
  begin
    match
      Type_checker.typ_equiv
        context.internal
        typ1'
        typ1
        (T.Kind.typ ())
    with
    | true -> ()
    | false ->
      raise_s
        [%message
          "typ of tag doesn't match returned typ"
            (context.internal : Context.Internal.t)
            (typ1 : T.Typ.t)
            (typ1' : T.Typ.t)]
  end;
  assert
    (Option.equal
       (fun typ2' typ2 ->
          Type_checker.typ_equiv
            context.internal
            typ2'
            typ2
            (T.Kind.typ ()))
       typ2_opt'
       typ2_opt);
  (tag', typ1, typ2_opt)

(* Preconditions:
   - [context] is well-formed
   - [typ] : [T.Kind.Typ] in [context] *)
(* Postconditions:
   if [result] = [(term_defn_lookup, context', pat)] then
   - [term_defn_lookup] is well-formed in [context] U [context']
   - (context' ||- [pat] : [typ]) in [context] *)
and check_pat'
      (context : Context.t)
      (pat : U.Pat.t)
      (typ : T.Typ.t)
  : T.Term.t String.Map.t * T.Typ.t T.Term.Var.Map.t * T.Pat.t =
  let (pat_elab_context, pat_internal_context, pat', typ') =
    synth_pat context pat
  in
  if Type_checker.typ_equiv context.internal typ typ' (T.Kind.typ ())
  then (pat_elab_context, pat_internal_context, pat')
  else begin
    raise_s
      [%message
        "check_pat: types are not equivalent"
          (context : Context.t)
          (pat : U.Pat.t)
          (pat' : T.Pat.t)
          (typ : T.Typ.t)
          (typ' : T.Typ.t)]
  end

and check_pat context pat typ =
  Invariant_checks.context_well_formed context;
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ)
       (T.Kind.typ ()));
  let (pat_elab_context, context', pat') = check_pat' context pat typ in
  (* CR wduff: assert stuff *)
  (pat_elab_context, context', pat')

(* Preconditions:
   - [context] is well-formed *)
(* Postconditions:
   if [result] = [(term_defn_lookup, context', pat, typ)] then
   - [term_defn_lookup] is well-formed in [context] U [context']
   - [typ] : [T.Kind.Typ] in [context]
   - (context' ||- [pat] : [typ]) in [context] *)
and synth_pat' (context : Context.t) (pat : U.Pat.t)
  : T.Term.t String.Map.t * T.Typ.t T.Term.Var.Map.t * T.Pat.t * T.Typ.t =
  match pat.without_positions with
  | Wild ->
    (String.Map.empty,
     T.Term.Var.Map.empty,
     T.Pat.Wild,
     T.Typ.uvar (Unification.newvar ()))
  | Var (_, name) ->
    let var = T.Term.Var.create name in
    let typ = T.Typ.uvar (Unification.newvar ()) in
    (String.Map.singleton name (T.Term.var var),
     T.Term.Var.Map.singleton var typ,
     T.Pat.Var var,
     typ)
  | Record fields ->
    let (pat_elab_contexts, pat_internal_contexts, fields', typ_fields) =
      List.map fields ~f:(fun (field, pat) ->
        let (pat_elab_context, pat_internal_context, pat', typ) =
          synth_pat context pat
        in
        (pat_elab_context, pat_internal_context, (field, pat'), (field, typ)))
      |> unzip4
    in
    (List.fold
       pat_elab_contexts
       ~init:String.Map.empty
       ~f:Context.merge_maps,
     List.fold
       pat_internal_contexts
       ~init:T.Term.Var.Map.empty
       ~f:Context.merge_maps,
     T.Pat.Record (String.Map.of_alist_exn fields'),
     T.Typ.record (String.Map.of_alist_exn typ_fields))
  | Tag (tag, pat_opt) ->
    let (tag', typ1, typ2_opt) = synth_tag context tag in
    (match (pat_opt, typ2_opt) with
     | (None, None) ->
       (String.Map.empty, T.Term.Var.Map.empty, T.Pat.Tag (tag', None), typ1)
     | (Some pat, Some typ2) ->
       let (pat_elab_context, pat_internal_context, pat') =
         check_pat context pat typ2
       in
       (pat_elab_context,
        pat_internal_context,
        T.Pat.Tag (tag', Some pat'), typ1)
     | _ ->
       raise_s
         [%message
           "???replace with legit error message."
             (tag : U.Tag.t)
             (tag' : T.Tag.t)
             (pat_opt : U.Pat.t option)
             (typ2_opt : T.Typ.t option)])
  | Number i ->
    (String.Map.empty, T.Term.Var.Map.empty, T.Pat.Number i, T.Typ.number ())
  | String s ->
    (String.Map.empty, T.Term.Var.Map.empty, T.Pat.String s, T.Typ.string ())
  | Ascribe (pat, typ) ->
    let typ' = check_typ context typ (T.Kind.typ ()) in
    let (pat_elab_context, pat_internal_context, pat') =
      check_pat context pat typ'
    in
    (pat_elab_context,
     pat_internal_context,
     T.Pat.Ascribe (pat', typ'),
     typ')

and synth_pat context pat =
  Invariant_checks.context_well_formed context;
  let (pat_elab_context, context', pat', typ) = synth_pat' context pat in
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ)
       (T.Kind.typ ()));
  (* CR wduff: assert more stuff *)
  (pat_elab_context, context', pat', typ)

(* Preconditions:
   - [context] is well-formed
   - [typ] has kind [T.Kind.Typ] in [context] *)
(* Postconditions:
   - [result] : [typ] in [context] *)
and check_term' context term typ =
  let (term', typ') = synth_term context term in
  if Type_checker.typ_equiv context.internal typ' typ (T.Kind.typ ())
  then term'
  else begin
    raise_s
      [%message
        "check_term: types are not equivalent"
          (typ : T.Typ.t)
          (typ' : T.Typ.t)]
  end

and check_term context term typ =
  Invariant_checks.context_well_formed context;
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ)
       (T.Kind.typ ()));
  let term' = check_term' context term typ in
  assert
    (Type_checker.typ_equiv
       context.internal
       (Type_checker.check_term context.internal term')
       typ
       (T.Kind.typ ()));
  term'

and specialize context (term, typ) =
  match T.Typ.out (Type_checker.weak_normalize context typ) with
  | Forall ((typ_var, kind), typ') ->
    let arg_typ =
      (* CR wduff: Can we do something fancy here? *)
      match T.Kind.out kind with
      | Typ -> T.Typ.uvar (Unification.newvar ())
      | _ -> failwith "can only generalize terms of kind typ"
    in
    specialize context
      (T.Term.typ_ap (term, arg_typ),
       T.Typ.subst Typ arg_typ typ_var typ')
  | _ -> (term, typ)

(* Preconditions:
   - [context] is well-formed *)
(* Postconditions:
   if [result] = [(term, typ)] then
   - [typ] has kind [T.Kind.Typ] in [context]
   - [term] : [typ] in [context] *)
and synth_term' (context : Context.t) (term : U.Term.t) : T.Term.t * T.Typ.t =
  match term.without_positions with
  | Var (code_pos, name) ->
    (match Map.find context.elab.terms name with
     | Some general_term ->
       let term = general_term `Specialize in
       (term, Type_checker.check_term context.internal term)
     | None ->
       raise_s
         [%message
           "No such term."
             (code_pos : Source_code_position.t)
             (name : string)
             (context : Context.t)])
  | Modl_proj (modl, field) ->
    let (modl', purity, _, elab_sigture, _) = synth_modl context modl in
    if Purity.equal purity Pure
    then
      match elab_sigture with
      | Body elab_context_creator ->
        (match Map.find elab_context_creator.terms field with
         | Some general_term ->
           let term = general_term modl' `Specialize in
           (term, Type_checker.check_term context.internal term)
         | None ->
           raise_s
             [%message
               "No such term in module."
                 (context : Context.t)
                 (modl : U.Modl.t)
                 (field : string)
                 (modl' : T.Modl.t)
                 (elab_context_creator : Context.Elab_creator.t)])
      | _ ->
        failwith "???replace with legit error message."
    else
      failwith "???replace with legit error message."
  | Fun (args, typ_opt, body) ->
    let (pat_elab_contexts, pat_internal_contexts, args', typs) =
      unzip4 (List.map args ~f:(synth_pat context))
    in
    let term_elab_context' =
      List.fold pat_elab_contexts ~init:context.elab.terms
        ~f:(fun term_elab_context pat_elab_context ->
          Context.merge_maps
            term_elab_context
            (Map.map pat_elab_context ~f:const))
    in
    let term_internal_context' =
      List.fold pat_internal_contexts ~init:context.internal.terms
        ~f:(fun term_internal_context pat_internal_context ->
          Context.merge_maps term_internal_context pat_internal_context)
    in
    let context' =
      { context with
        elab = { context.elab with terms = term_elab_context' }
      ; internal = { context.internal with terms = term_internal_context' }
      }
    in
    let (body', typ') =
      (match typ_opt with
       | None -> synth_term context' body
       | Some typ ->
         let typ' = check_typ context' typ (T.Kind.typ ()) in
         (check_term context body typ', typ'))
    in
    (T.Term.fun_ ((args', Some typ'), body'),
     List.fold_right typs ~init:typ'
       ~f:(fun typ typ' -> T.Typ.arrow (typ, typ')))
  | Ap terms ->
    Parse_infix.parse_infix [%sexp_of: U.Term.t]
      ~is_infix:(fun (term : U.Term.t) ->
        match term.without_positions with
        | U.Term.Var (_, name) ->
          (match String.Map.find context.fixity.infix_terms name with
           | None -> false
           | Some _ -> true)
        | _ -> false)
      ~precedence:(fun term1 term2 ->
        match (term1.without_positions, term2.without_positions) with
        | (U.Term.Var (_, name1), U.Term.Var (_, name2)) ->
          String.Map.find
            (String.Map.find_exn context.fixity.infix_terms name1)
            name2
        | _ -> failwith "???compiler bug")
      ~convert:(synth_term context)
      ~ap:(fun (term1, typ1) (term2, typ2) ->
        let typ11 = T.Typ.uvar (Unification.newvar ()) in
        let typ12 = T.Typ.uvar (Unification.newvar ()) in
        if Type_checker.typ_equiv context.internal typ1 (T.Typ.arrow (typ11, typ12)) (T.Kind.typ ())
        && Type_checker.typ_equiv context.internal typ2 typ11 (T.Kind.typ ())
        then (T.Term.ap (term1, term2), typ12)
        else begin
          raise_s
            [%message
              "???replace with legit error message."
                (context : Context.t)
                (term1 : T.Term.t)
                (term2 : T.Term.t)
                (typ1 : T.Typ.t)
                (typ2 : T.Typ.t)
                (Type_checker.weak_normalize context.internal typ1 : T.Typ.t)
                (Type_checker.weak_normalize context.internal typ2 : T.Typ.t)]
        end)
      terms
  | Record fields ->
    let (fields', typ_fields) =
      List.map fields ~f:(fun (field, term) ->
        let (term', typ) = synth_term context term in
        ((field, term'), (field, typ)))
      |> List.unzip
    in
    (T.Term.record (String.Map.of_alist_exn fields'),
     T.Typ.record (String.Map.of_alist_exn typ_fields))
  | Match (term, cases) ->
    let (term', typ) = synth_term context term in
    let (cases', typs) =
      List.unzip
        (List.map cases ~f:(fun (pat, term) ->
           let (pat_elab_context, pat_internal_context, pat') =
             check_pat context pat typ
           in
           let (term', typ') =
             synth_term
               { context with
                 elab =
                   { context.elab with
                     terms =
                       Context.merge_maps context.elab.terms
                         (String.Map.map pat_elab_context ~f:const)
                   }
               ; internal =
                   { context.internal with
                     terms =
                       Context.merge_maps
                         context.internal.terms
                         pat_internal_context
                   }
               }
               term
           in
           ((pat', term'), typ')))
    in
    let typ' =
      match typs with
      | [] -> T.Typ.uvar (Unification.newvar ())
      | typ :: typs ->
        if
          List.for_all typs
            ~f:(fun typ' -> Type_checker.typ_equiv context.internal typ typ' (T.Kind.typ ()))
        then typ
        else
          raise_s
            [%message
              "Not all the branches of the match have the same type."
                (context : Context.t)
                ~typs:(typ :: typs : T.Typ.t list)]
    in
    (T.Term.match_ (term', cases'), typ')
  | Number n -> (T.Term.number n, T.Typ.number ())
  | String s -> (T.Term.string s, T.Typ.string ())
  | Built_in (name, typ) ->
    let typ' = check_typ context typ (T.Kind.typ ()) in
    (T.Term.built_in (name, typ'), typ')
  | Let (defns, term) ->
    let (modl, _, sigture, elab_context_creator, fixity_context) =
      elab_defns context defns
    in
    let modl_var = T.Modl.Var.create "???use block name in the future" in
    let context' : Context.t =
      { fixity = Context.Fixity.merge context.fixity fixity_context
      ; elab =
          Context.Elab.merge context.elab
            (Context.Elab_creator.apply
               elab_context_creator
               (T.Modl.var modl_var))
      ; internal =
          Context.Internal.add_modl context.internal modl_var sigture
      }
    in
    let (term', typ) = synth_term context' term in
    (T.Term.let_ (T.Defn.Modl (modl_var, modl), term'), typ)
  | Ascribe (term, typ) ->
    let typ' = check_typ context typ (T.Kind.typ ()) in
    let term' = check_term context term typ' in
    (T.Term.ascribe (term', typ'), typ')

and synth_term context term =
  Invariant_checks.context_well_formed context;
  let (term', typ) = specialize context.internal (synth_term' context term) in
  assert
    (Type_checker.subkind
       context.internal
       (Type_checker.check_typ context.internal typ)
       (T.Kind.typ ()));
  begin
    match
      Type_checker.typ_equiv
        context.internal
        (Type_checker.check_term context.internal term')
        typ
        (T.Kind.typ ())
    with
    | true -> ()
    | false | exception _ ->
      raise_s
        [%message
          [%here]
            (context : Context.t)
            (term : U.Term.t)
            (term' : T.Term.t)
            (typ : T.Typ.t)
            (Type_checker.check_term context.internal term': T.Typ.t)]
  end;
  (term', typ)

(* Preconditions:
   - [context] is well-formed
   - [sigture] ok in [context] *)
(* Postconditions:
   - [result] :_{[purity]} [sigture] in [context] *)
and check_modl'
      (context : Context.t)
      (modl : U.Modl.t)
      (purity : Purity.t)
      (sigture : T.Sigture.t)
      (foo_sigture : Context.Foo_sigture.t)
  : T.Modl.t =
  let (modl', purity', sigture', elab_sigture, _) = synth_modl context modl in
  if Purity.(purity' <= purity)
  && Type_checker.subsigture context.internal sigture' sigture
  then coerce_modl context modl' elab_sigture foo_sigture
  else failwith "???replace with legit error message."

and check_modl context modl purity sigture foo_sigture =
  Invariant_checks.context_well_formed context;
  (* CR wduff: assert (sigture_ok context sigture); *)
  (* CR wduff: (pre/post)-conditions about foo_sigture? *)
  let modl' = check_modl' context modl purity sigture foo_sigture in
  let (purity', sigture') = Type_checker.check_modl context.internal modl' in
  assert (Purity.(<=) purity' purity);
  assert (Type_checker.subsigture context.internal sigture' sigture);
  modl'

(* Preconditions:
   - [context] is well-formed *)
(* Postconditions:
   if [result] = [(modl, purity, sigture, elab_sigture, _fixity_sigture)] then
   - [elab_sigture] is well-formed in [context]
   - [sigture] ok in [context]
   - [modl] :_{[purity]} [sigture] in [context] *)
and synth_modl' (context : Context.t) (modl : U.Modl.t)
  : T.Modl.t * Purity.t * T.Sigture.t * Context.Elab_sigture.t * Context.Fixity_sigture.t =
  match modl.without_positions with
  | Var (code_pos, name) ->
    (match
       (String.Map.find context.fixity.modls name,
        String.Map.find context.elab.modls name)
     with
     | (Some fixity_sigture, Some (modl, elab_sigture)) ->
       let modl = modl `Specialize in
       let (purity, sigture) = Type_checker.check_modl context.internal modl in
       (modl, purity, sigture, elab_sigture, fixity_sigture)
     | _ ->
       raise_s
         [%message
           "No such module."
             (code_pos : Source_code_position.t)
             (name : string)
             (context : Context.t)])
  | Modl_proj (modl, field) ->
    let (modl', purity, _, elab_sigture, fixity_sigture) =
      synth_modl context modl
    in
    if Purity.equal purity Pure
    then
      match (elab_sigture, fixity_sigture) with
      | (Body elab_context, Body fixity_context) ->
        (match
           (String.Map.find elab_context.modls field,
            String.Map.find fixity_context.modls field)
         with
         | (Some (f, elab_sigture'), Some fixity_sigture') ->
           let modl'' = f modl' `Specialize in
           let (purity', sigture') = Type_checker.check_modl context.internal modl'' in
           (modl'', purity', sigture', elab_sigture', fixity_sigture')
         | _ -> failwith "???replace with legit error message.1")
      | _ -> failwith "???replace with legit error message.2"
    else
      failwith "???replace with legit error message.3"
  | Ap (modl1, modl2) ->
    let (modl1', _purity, sigture, elab_sigture, fixity_sigture) =
      synth_modl context modl1
    in
    (match (T.Sigture.out sigture, elab_sigture, fixity_sigture) with
     | (Arrow ((var, sigture), sigture'),
        Arrow (foo_sigture, elab_sigture),
        Arrow fixity_sigture') ->
       let modl2' = check_modl context modl2 Pure sigture foo_sigture in
       (T.Modl.ap (modl1', modl2'),
        Impure,
        T.Sigture.subst Modl modl2' var sigture',
        elab_sigture,
        fixity_sigture')
     | _ -> failwith "???replace with legit error message.4")
  | Ascribe (modl, sigture) ->
    let (sigture', foo_sigture, fixity_sigture) =
      elab_rec_sigture context sigture
    in
    let modl' = check_modl context modl Impure sigture' foo_sigture in
    (T.Modl.ascribe (modl', sigture'),
     Impure,
     sigture',
     elab_sigture_of_foo_sigture foo_sigture,
     fixity_sigture)
  | Body defns ->
    let (modl, purity, sigture, elab_context_creator, fixity_context) =
      elab_defns context defns
    in
    (modl, purity, sigture, Body elab_context_creator, Body fixity_context)

and synth_modl (context : Context.t) (modl : U.Modl.t)
  : T.Modl.t * Purity.t * T.Sigture.t * Context.Elab_sigture.t * Context.Fixity_sigture.t =
  Invariant_checks.context_well_formed context;
  let (modl', purity, sigture, elab_sigture, fixity_sigture) =
    synth_modl' context modl
  in
  begin
    try
      Type_checker.check_sigture context.internal sigture;
      Invariant_checks.fixity_sigture_matches_elab_sigture fixity_sigture elab_sigture;
      Invariant_checks.elab_sigture_matches_sigture context.internal elab_sigture sigture;
      let (purity', sigture') = Type_checker.check_modl context.internal modl' in
      assert (Purity.(<=) purity' purity);
      assert (Type_checker.subsigture context.internal sigture' sigture);
    with exn ->
      raise_s
        [%message
          "Invariant check failed in synth_modl"
            (exn : exn)
            (context : Context.t)
            (modl : U.Modl.t)
            (modl' : T.Modl.t)
            (purity : Purity.t)
            (sigture : T.Sigture.t)
            (elab_sigture : Context.Elab_sigture.t)
            (fixity_sigture : Context.Fixity_sigture.t)]
  end;
  (modl', purity, sigture, elab_sigture, fixity_sigture)

(* CR wduff: Completeness theorem idea:

   Extend [Unbound.Defn.t] to add [Rec_modl] and define a non-deterministic algorithm
   [remove_implicit_recursion] from [Unbound.Defn.t list] to [Unbound.Defn.t list] as follows:

   {[
     let make_recursive_modl defns =
       let modl_var = (* some name not already in use *) in
       let defns' =
         (* Replace a non-deterministic subset of the variables used by [defns] with
            [Modl_proj (modl_var, name)], where [name] is the name of the variable. *)
       in
       let sigture = (* Non-deterministically pick a sigture. *) in
       Unbound.Defn.Rec_modl ((modl_var, sigture), defns')
     ;;

     let rec remove_implicit_recursion defns =
       let defns = List.map defns ~f:remove_implicit_recursion_from_defn in
       let permutation : Unbound.t list = (* non-determinisitcally permute defns *) in
       let sccs : Unbound.t list list = (* non-deterministically group permutation *) in
       List.map sccs ~f:(fun scc ->
         match scc with
         | [] -> assert false
         | [defn] ->
           if <non-deterministic bool>
           then defn
           else make_recursive_modl defns
         | _ ->
           make_recursive_modl defns)

     and remove_implicit_recursion_from_modl modl =
       match modl with
       (* ... *)
       | Body defns ->
         Body (remove_implicit_recursion defns)

     and remove_implicit_recursion_from_term term =
       match term with
       (* ... *)
       | Let (defns, term) ->
         Let (remove_implicit_recursion defns, term)

     (* ... *)
     ;;
   ]}

   Issues:
   - Need a way to rename variable uses, particularly in the module case.
   - Need to restrict re-ordering of effectful defns.
   - May need to constrain how the sigtures for the explicit recursive modules are picked. *)
(* Preconditions:
   - [context] is well-formed *)
(* Postcondition:
   if [result] = [(modl, sigture, fixity_sigture)] then
   - [sigture] ok in [context]
   - [modl] :_P [sigture] in [context] *)
and elab_defns' (context : Context.t) defns
  : T.Modl.t * Purity.t * T.Sigture.t * Context.Elab_creator.t * Context.Fixity.t =
  let indices_of_non_values =
    List.filter_mapi defns
      ~f:(fun i defn ->
        if Unbound_semantics.defn_is_value defn
        then None
        else Some i)
  in
  let defn_array = Array.of_list defns in
  let defns_by_names_defined : int Unbound_semantics.Sorted_name.Map.t =
    Array.foldi defn_array ~init:Unbound_semantics.Sorted_name.Map.empty
      ~f:(fun i map defn ->
        let names = Unbound_semantics.names_defined_by_defn defn in
        Set.fold names ~init:map
          ~f:(fun map name ->
            if Map.mem map name
            then failwith "???replace with legit error message."
            else Map.set map ~key:name ~data:i))
  in
  let dep_graph_without_edges =
    Array.foldi defn_array ~init:Dependence.empty
      ~f:(fun i graph _ -> Dependence.add_vertex graph i)
  in
  let dep_graph =
    Array.foldi defn_array ~init:dep_graph_without_edges
      ~f:(fun i graph defn ->
        let names_used = Unbound_semantics.names_used_by_defn defn in
        Set.fold names_used ~init:graph
          ~f:(fun graph name ->
            match Map.find defns_by_names_defined name with
            | None -> graph
            | Some j -> Dependence.add_edge graph i j))
  in
  let (_, dep_graph) =
    List.fold_left indices_of_non_values
      ~init:(None, dep_graph)
      ~f:(fun (prev, graph) i ->
        (Some i,
         match prev with
         | None -> graph
         | Some prev -> Dependence.add_edge graph i prev))
  in
  let sccs = SCC.scc_list dep_graph in
  (* CR wduff: We need to generalize whenever defn_index is a value, so for now we do this hack.
     We should unwind this and separate polymorphism from recursion. *)
  let should_elaborate_recursively defn_index =
    match Dependence.mem_edge dep_graph defn_index defn_index with
    | true -> true
    | false ->
      match Unbound_semantics.defn_is_value defn_array.(defn_index) with
      | false -> false
      | true ->
        match defn_array.(defn_index).without_positions with
        | TypAlias _ | Sigture _ -> false
        | _ -> true
  in
  let rec loop (context : Context.t) sccs index =
    match sccs with
    | [] ->
      (T.Defns.end_ (),
       Purity.Pure,
       T.Decls.end_ (),
       Context.Elab_creator.empty,
       Context.Fixity.empty)
    | scc :: sccs ->
      print_s
        [%message
          "begin defn block"
            (index : int)
            ~defns:
              (List.map scc ~f:(fun defn_index ->
                 let defn = defn_array.(defn_index) in
                 let string = U.Defn.to_string defn in
                 match String.lsplit2  string ~on:'(' with
                 | Some (string, _) -> string
                 | None ->
                   match String.lsplit2 string ~on:'=' with
                   | Some (string, _) -> string
                   | None -> string)
               : string list)];
      let result =
        match scc with
        | [] -> assert false
        | [defn_index] when not (should_elaborate_recursively defn_index) ->
          begin
            match defn_array.(defn_index).without_positions with
            | InfixTyp _ | InfixTerm _ ->
              loop context sccs (index + 1)
            | TypAlias (name, args, typ) ->
              let typ_var = T.Typ.Var.create name in
              let (context_with_args, wrap_typ, wrap_kind) =
                List.fold_right args ~init:(context, ident, ident)
                  ~f:(fun arg_name ((context : Context.t), wrap_typ, wrap_kind) ->
                    let arg_var = T.Typ.Var.create arg_name in
                    ({ context with
                       elab =
                         Context.Elab.add_typ context.elab arg_name (T.Typ.var arg_var)
                     ; internal =
                         Context.Internal.add_typ context.internal arg_var (T.Kind.typ ())
                     },
                     (fun body  ->
                        T.Typ.fun_ ((arg_var, T.Kind.typ ()), wrap_typ body)),
                     (fun result_kind  ->
                        T.Kind.arrow ((arg_var, T.Kind.typ ()), wrap_kind result_kind))))
              in
              let (typ', kind) =
                synth_typ context_with_args typ
              in
              let typ'' = wrap_typ typ' in
              let kind' = wrap_kind kind in
              let kind'' = Type_checker.singleton typ'' kind' in
              let context' =
                { context with
                  elab =
                    Context.Elab.add_typ context.elab name (T.Typ.var typ_var)
                ; internal =
                    Context.Internal.add_typ context.internal typ_var kind''
                }
              in
              let (defns, purity, decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (T.Defns.cons ((name, T.Defn.Typ (typ_var, typ'')), defns),
               purity,
               T.Decls.cons ((name, T.Decl.Typ (typ_var, kind'')), decls),
               Context.Elab_creator.add_typ elab_context_creator name
                 (fun modl -> T.Typ.modl_proj (modl, name)),
               fixity_context)
            | SumTyp (name, args, cases) ->
              let (context_with_args, wrap_typ, wrap_kind) =
                List.fold_right args ~init:(context, ident, ident)
                  ~f:(fun arg_name ((context : Context.t), wrap_typ, wrap_kind) ->
                    let arg_var = T.Typ.Var.create arg_name in
                    ({ context with
                       elab =
                         Context.Elab.add_typ context.elab arg_name (T.Typ.var arg_var)
                     ; internal =
                         Context.Internal.add_typ context.internal arg_var (T.Kind.typ ())
                     },
                     (fun body  ->
                        T.Typ.fun_ ((arg_var, T.Kind.typ ()), wrap_typ body)),
                     (fun result_kind  ->
                        T.Kind.arrow ((arg_var, T.Kind.typ ()), wrap_kind result_kind))))
              in
              let uvars () =
                List.map args ~f:(fun _ -> Unification.newvar ())
              in
              let apply_typ_to_uvars typ uvars =
                List.fold uvars ~init:typ ~f:(fun typ uvar ->
                  T.Typ.ap (typ, T.Typ.uvar uvar))
              in
              let num_cases = List.length cases in
              let cases' =
                List.map cases
                  ~f:(fun (name, typ_opt) ->
                    (name,
                     Option.map typ_opt ~f:(fun typ ->
                       check_typ context_with_args typ (T.Kind.typ ()))))
              in
              let typ_var = T.Typ.Var.create name in
              let typ =
                wrap_typ
                  (T.Typ.sum
                     (List.map cases'
                        ~f:(fun (_, typ_opt) ->
                          Option.value typ_opt ~default:(T.Typ.sum []))))
              in
              let modl_var = T.Modl.Var.create name in
              let sigture =
                T.Sigture.body
                  (T.Decls.cons
                     ((name, T.Decl.Typ (typ_var, wrap_kind (T.Kind.typ ()))),
                      decls_of_list
                        (List.concat_map cases' ~f:(fun (name, typi_opt) ->
                           let uvars = uvars () in
                           let typ = apply_typ_to_uvars (T.Typ.var typ_var) uvars in
                           let typi_opt =
                             Option.map typi_opt ~f:(fun typi ->
                               apply_typ_to_uvars (wrap_typ typi) uvars)
                           in
                           [ (name,
                              T.Decl.Val
                                (match typi_opt with
                                 | None -> typ
                                 | Some typi ->
                                   T.Typ.arrow (typi, typ)))
                           ; (name,
                              T.Decl.Tag (typ, typi_opt))
                           ]))))
              in
              let modl =
                T.Modl.ascribe
                  (T.Modl.body
                     ((name, T.Modl_field.Typ typ)
                      :: List.mapi cases'
                           ~f:(fun i (name, typi_opt) ->
                             (name,
                              T.Modl_field.Val
                                (match typi_opt with
                                 | None ->
                                   T.Term.in_ (num_cases, i, T.Term.record String.Map.empty)
                                 | Some typi ->
                                   let term_var = T.Term.Var.create " d" in
                                   let uvars = uvars () in
                                   let typi = apply_typ_to_uvars (wrap_typ typi) uvars in
                                   T.Term.fun_
                                     (([T.Pat.Ascribe (T.Pat.Var term_var, typi)],
                                       Some (apply_typ_to_uvars typ uvars)),
                                      T.Term.in_
                                        (num_cases, i, T.Term.var term_var)))))
                      @ List.mapi cases'
                          ~f:(fun i (name, _) ->
                            (name,
                             T.Modl_field.Tag (T.Tag.in_ (num_cases, i))))),
                   sigture)
              in
              let context' =
                { context with
                  elab =
                    List.fold cases
                      ~init:(
                        Context.Elab.add_typ context.elab name
                          (T.Typ.modl_proj (T.Modl.var modl_var, name)))
                      ~f:(fun elab_context (name, _) ->
                        Context.Elab.add_tag
                          (Context.Elab.add_term elab_context name
                             (T.Term.modl_proj (T.Modl.var modl_var, name)))
                          name
                          (T.Tag.modl_proj (T.Modl.var modl_var, name)))
                ; internal =
                    Context.Internal.add_modl context.internal modl_var sigture
                }
              in
              let (defns, (_ : Purity.t), decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (T.Defns.cons ((name, T.Defn.Modl (modl_var, modl)), defns),
               Purity.Impure,
               T.Decls.cons (((name, T.Decl.Modl (modl_var, sigture))), decls),
               List.fold cases
                 ~init:(
                   Context.Elab_creator.add_typ elab_context_creator name
                     (fun modl ->
                        T.Typ.modl_proj (T.Modl.modl_proj (modl, name), name)))
                 ~f:(fun elab_context (case_name, _) ->
                   Context.Elab_creator.add_tag
                     (Context.Elab_creator.add_term elab_context case_name
                        (fun modl ->
                           T.Term.modl_proj
                             (T.Modl.modl_proj (modl, name), case_name)))
                     case_name
                     (fun modl ->
                        T.Tag.modl_proj
                          (T.Modl.modl_proj (modl, name), case_name))),
               fixity_context)
            | U.Defn.Tag (name, typs_opt, tag) ->
              let tag_var = T.Tag.Var.create name in
              let (tag', typ1, typ2_opt) =
                match typs_opt with
                | None -> synth_tag context tag
                | Some (typ1, typ2_opt) ->
                  let typ1' = check_typ context typ1 (T.Kind.typ ()) in
                  let typ2_opt' =
                    Option.map typ2_opt
                      ~f:(fun typ2 -> check_typ context typ2 (T.Kind.typ ()))
                  in
                  (check_tag context tag typ1' typ2_opt', typ1', typ2_opt')
              in
              let context' =
                { context with
                  elab =
                    Context.Elab.add_tag context.elab name (T.Tag.var tag_var)
                ; internal =
                    Context.Internal.add_tag context.internal tag_var (typ1, typ2_opt)
                }
              in
              let (defns, purity, decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (T.Defns.cons ((name, T.Defn.Tag (tag_var, tag')), defns),
               purity,
               T.Decls.cons ((name, T.Decl.Tag (typ1, typ2_opt)), decls),
               Context.Elab_creator.add_tag elab_context_creator name
                 (fun modl -> T.Tag.modl_proj (modl, name)),
               fixity_context)
            | Val (pat, term) ->
              (* CR wduff: This could be simplified by changing [Typed.Defn.Val] to take a pattern
                 instead of a variable, but that may make other code more complicated. *)
              let (pat_elab_context, pat_internal_context, pat', typ) =
                synth_pat context pat
              in
              let term' = check_term context term typ in
              let record_name = Int.to_string index in
              let record_var = T.Term.Var.create record_name in
              let record_pat_vars =
                Map.mapi pat_elab_context ~f:(fun ~key:name ~data:_ ->
                  T.Term.Var.create name)
              in
              let pat_elab_context_via_record =
                Map.map record_pat_vars
                  ~f:(fun var record `Specialize ->
                    T.Term.match_
                      (record,
                       [ (T.Pat.Record
                            (Map.map record_pat_vars
                               ~f:(fun var -> T.Pat.Var var)),
                          T.Term.var var)
                       ]))
              in
              let record_typ =
                T.Typ.record
                  (Map.map pat_elab_context
                     ~f:(Type_checker.check_term
                           { context.internal with
                             terms =
                               Context.merge_maps context.internal.terms pat_internal_context
                           }))
              in
              let context' =
                { context with
                  elab =
                    { context.elab with
                      terms =
                        Context.merge_maps context.elab.terms
                          (Map.map
                             pat_elab_context_via_record
                             ~f:(fun f -> f (T.Term.var record_var)))
                    }
                ; internal =
                    Context.Internal.add_term context.internal record_var record_typ
                }
              in
              let (defns, purity, decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (T.Defns.cons
                 ((record_name,
                   T.Defn.Val
                     (record_var,
                      T.Term.match_
                        (term', [(pat', T.Term.record pat_elab_context)]))),
                  defns),
               purity,
               T.Decls.cons ((record_name, T.Decl.Val record_typ), decls),
               { elab_context_creator with
                 terms =
                   Context.merge_maps
                     elab_context_creator.terms
                     (Map.map pat_elab_context_via_record ~f:(fun f modl ->
                        f (T.Term.modl_proj (modl, record_name))))
               },
               fixity_context)
            | Fun (name, args, result_typ_opt, body) ->
              let (term, typ) =
                synth_term context
                  { start_pos = defn_array.(defn_index).start_pos
                  ; end_pos = defn_array.(defn_index).end_pos
                  ; without_positions = U.Term.Fun (args, result_typ_opt, body)
                  }
              in
              let var = T.Term.Var.create name in
              let context' =
                { context with
                  elab = Context.Elab.add_term context.elab name (T.Term.var var)
                ; internal = Context.Internal.add_term context.internal var typ
                }
              in
              let (defns, purity, decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (T.Defns.cons ((name, T.Defn.Val (var, term)), defns),
               purity,
               T.Decls.cons ((name, T.Decl.Val typ), decls),
               Context.Elab_creator.add_term elab_context_creator name
                 (fun modl -> T.Term.modl_proj (modl, name)),
               fixity_context)
            | Sigture (name, sigture) ->
              let (sigture', foo_sigture, fixity_sigture) =
                elab_rec_sigture context sigture
              in
              let context' =
                { context with
                  elab = Context.Elab.add_sigture context.elab name (sigture', foo_sigture)
                ; fixity = Context.Fixity.add_sigture context.fixity name fixity_sigture
                }
              in
              let (defns, purity, decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (defns,
               purity,
               decls,
               (* CR wduff: For now, we don't expose the signature outside the current block of
                  definitions. One way to fix this would be to elaborate the signature twice, or is
                  some generic way, so that it can be exposed internally as it is now, but so that the
                  externally exposed version refers to components of the module we create from this
                  block of definitions, rather that to internal variables for those definitions.

                  Both [elab_context_creator] and [fixity_context] will need to be updated. *)
               elab_context_creator,
               fixity_context)
            | Modl (name, arg_opt, sigture_opt, body) ->
              let modl_var = T.Modl.Var.create name in
              let (modl, purity, sigture, elab_sigture, fixity_sigture) =
                match arg_opt with
                | None ->
                  (match sigture_opt with
                   | None -> synth_modl context body
                   | Some sigture ->
                     synth_modl context
                       { start_pos = defn_array.(defn_index).start_pos
                       ; end_pos = defn_array.(defn_index).end_pos
                       ; without_positions = U.Modl.Ascribe (body, sigture)
                       })
                | Some (arg_name, arg_sigture) ->
                  let arg_var = T.Modl.Var.create arg_name in
                  let (arg_sigture', arg_foo_sigture, arg_fixity_sigture) =
                    elab_rec_sigture context arg_sigture
                  in
                  let context' =
                    { Context.
                      fixity =
                        Context.Fixity.add_modl context.fixity arg_name arg_fixity_sigture
                    ; elab =
                        Context.Elab.add_modl context.elab arg_name
                          (T.Modl.var arg_var,
                           elab_sigture_of_foo_sigture arg_foo_sigture)
                    ; internal =
                        Context.Internal.add_modl context.internal arg_var arg_sigture'
                    }
                  in
                  let (body', _, sigture, elab_sigture, fixity_sigture) =
                    match sigture_opt with
                    | None -> synth_modl context' body
                    | Some sigture ->
                      synth_modl context'
                        { start_pos = defn_array.(defn_index).start_pos
                        ; end_pos = defn_array.(defn_index).end_pos
                        ; without_positions = U.Modl.Ascribe (body, sigture)
                        }
                  in
                  (T.Modl.fun_ ((arg_var, arg_sigture'), body'),
                   Pure,
                   T.Sigture.arrow ((arg_var, arg_sigture'), sigture),
                   Context.Elab_sigture.Arrow (arg_foo_sigture, elab_sigture),
                   Context.Fixity_sigture.Arrow fixity_sigture)
              in
              let (context' : Context.t) =
                { fixity = Context.Fixity.add_modl context.fixity name fixity_sigture
                ; elab =
                    Context.Elab.add_modl
                      context.elab
                      name
                      (T.Modl.var modl_var, elab_sigture)
                ; internal =
                    Context.Internal.add_modl
                      context.internal
                      modl_var
                      sigture
                }
              in
              let (defns, purity', decls, elab_context_creator, fixity_context) =
                loop context' sccs (index + 1)
              in
              (T.Defns.cons ((name, T.Defn.Modl (modl_var, modl)), defns),
               Purity.max purity purity',
               T.Decls.cons
                 ((name,
                   T.Decl.Modl (modl_var, sigture)),
                  decls),
               Context.Elab_creator.add_modl elab_context_creator name
                 ((fun modl -> T.Modl.modl_proj (modl, name)),
                  elab_sigture),
               Context.Fixity.add_modl fixity_context name fixity_sigture)
            | U.Defn.Include _ ->
              failwith "unimpl4"
          end
        | _ ->
          let names_defined_in_this_scc =
            List.map scc ~f:(fun defn_index ->
              Unbound_semantics.names_defined_by_defn defn_array.(defn_index))
            |> Unbound_semantics.Sorted_name.Set.union_list
          in
          let defn_index_can_be_recursive defn_index =
            Unbound_semantics.defn_is_value defn_array.(defn_index)
            && not
                 (Unbound_semantics.defn_value_has_exposed_uses
                    defn_array.(defn_index)
                    ~of_:names_defined_in_this_scc)
          in
          match List.for_all scc ~f:defn_index_can_be_recursive with
          | false ->
            let defn_index =
              List.find_exn scc ~f:(fun defn_index ->
                not (defn_index_can_be_recursive defn_index))
            in
            let defn = defn_array.(defn_index) in
            raise_s
              [%message
                "???replace with legit error message."
                  (defn : U.Defn.t)
                  ~defn_is_value:(Unbound_semantics.defn_is_value defn : bool)
                  (names_defined_in_this_scc : Unbound_semantics.Sorted_name.Set.t)
              ]
          | true ->
            (* elaborate recursive module *)
            let (modl, purity, sigture, elab_context_creator, fixity_context) =
              elab_rec_defns context (List.map scc ~f:(Array.get defn_array))
            in
            (* CR wduff: Make sure this doesn't show up in errors. *)
            let modl_name = Int.to_string index in
            let modl_var = T.Modl.Var.create modl_name in
            let context' : Context.t =
              { fixity = Context.Fixity.merge context.fixity fixity_context
              ; elab =
                  Context.Elab.merge context.elab
                    (Context.Elab_creator.apply
                       elab_context_creator
                       (T.Modl.var modl_var))
              ; internal =
                  Context.Internal.add_modl context.internal modl_var sigture
              }
            in
            let (defns, purity', decls, elab_context_creator', fixity_context') =
              loop context' sccs (index + 1)
            in
            (T.Defns.cons ((modl_name, T.Defn.Modl (modl_var, modl)), defns),
             Purity.max purity purity',
             T.Decls.cons ((modl_name, T.Decl.Modl (modl_var, sigture)), decls),
             Context.Elab_creator.merge
               { typs =
                   String.Map.map elab_context_creator.typs ~f:(fun f modl ->
                     (f (T.Modl.modl_proj (modl, modl_name))))
               ; tags =
                   String.Map.map elab_context_creator.tags ~f:(fun f modl ->
                     (f (T.Modl.modl_proj (modl, modl_name))))
               ; terms =
                   String.Map.map elab_context_creator.terms ~f:(fun f modl ->
                     (f (T.Modl.modl_proj (modl, modl_name))))
               ; sigtures =
                   String.Map.map elab_context_creator.sigtures ~f:(fun (f, foo_sigture) ->
                     ((fun modl -> f (T.Modl.modl_proj (modl, modl_name))),
                      foo_sigture))
               ; modls =
                   String.Map.map elab_context_creator.modls ~f:(fun (f, elab_sigture) ->
                     ((fun modl -> f (T.Modl.modl_proj (modl, modl_name))),
                      (* CR wduff: Think. *)
                      elab_sigture))
               }
               (let modl = T.Modl.modl_proj (T.Modl.var modl_var, modl_name) in
                { typs =
                    String.Map.map elab_context_creator'.typs ~f:(fun f modl' ->
                      T.Typ.subst Modl modl modl_var (f modl'))
                ; tags =
                    String.Map.map elab_context_creator'.tags ~f:(fun f modl' `Specialize ->
                      T.Tag.subst Modl modl modl_var (f modl' `Specialize))
                ; terms =
                    String.Map.map elab_context_creator'.terms ~f:(fun f modl' `Specialize ->
                      T.Term.subst Modl modl modl_var (f modl' `Specialize))
                ; sigtures =
                    String.Map.map elab_context_creator'.sigtures ~f:(fun (f, foo_sigture) ->
                      ((fun modl' -> T.Sigture.subst Modl modl modl_var (f modl')),
                       foo_sigture))
                ; modls =
                    String.Map.map elab_context_creator'.modls ~f:(fun (f, elab_sigture) ->
                      ((fun modl' `Specialize ->
                         T.Modl.subst Modl modl modl_var (f modl' `Specialize)),
                       (* CR wduff: Think. *)
                       elab_sigture))
                }),
             Context.Fixity.merge fixity_context fixity_context')
      in
      printf "end defn block %d\n%!" index;
      result
  in
  let (defns, purity, decls, elab_context_creator, fixity_context) =
    loop context sccs 0
  in
  (T.Modl.dep_body defns,
   purity,
   T.Sigture.body decls,
   elab_context_creator,
   fixity_context)

and elab_defns context defns =
  Invariant_checks.context_well_formed context;
  let (modl, purity, sigture, elab_context_creator, fixity_context) =
    elab_defns' context defns
  in
  begin
    try
      Type_checker.check_sigture context.internal sigture;
      Invariant_checks.fixity_context_matches_elab_context_creator fixity_context elab_context_creator;
      Invariant_checks.elab_context_creator_type_checks context.internal elab_context_creator sigture;
      let (purity', sigture') = Type_checker.check_modl context.internal modl in
      assert (Purity.(<=) purity' purity);
      assert (Type_checker.subsigture context.internal sigture' sigture);
    with exn ->
      let backtrace = Backtrace.get () in
      raise_s
        [%message
          "Invariant check failed in elab_defns"
            (exn : exn)
            (Backtrace.to_string backtrace : string)
            (defns : U.Defn.t list)
            (modl : T.Modl.t)
            (purity : Purity.t)
            (sigture : T.Sigture.t)
            (Context.Elab_creator.apply
               elab_context_creator
               (T.Modl.var (T.Modl.Var.create " x "))
             : Context.Elab.t)
            (fixity_context : Context.Fixity.t)]
  end;
  (modl, purity, sigture, elab_context_creator, fixity_context)

(* Elaborate a single recursive block of definitions. *)
and elab_rec_defns' (context : Context.t) defns
  : T.Modl.t * Purity.t * T.Sigture.t * Context.Elab_creator.t * Context.Fixity.t =
  (* Elaborate the decls from the defns. *)
  let (wrap_decls, elab_context_creator, fixity_context) =
    List.fold_right defns
      ~init:(ident, Context.Elab_creator.empty, Context.Fixity.empty)
      ~f:(fun defn (wrap_decls, elab_context_creator, fixity_context) ->
        let (decls', elab_context_creator', fixity_context') =
          decls_of_defn context defn
        in
        ((fun decls ->
           wrap_decls
             (append_decls decls' decls)),
         Context.Elab_creator.merge elab_context_creator elab_context_creator',
         Context.Fixity.merge fixity_context fixity_context'))
  in
  let rec_var = T.Modl.Var.create " e" in
  let decls = wrap_decls (T.Decls.end_ ()) in
  (* Add recursive module variable to context. *)
  let context' =
    { Context.
      fixity = Context.Fixity.merge context.fixity fixity_context
    ; elab =
        Context.Elab.merge context.elab
          (Context.Elab_creator.apply elab_context_creator (T.Modl.var rec_var))
    ; internal =
        Context.Internal.add_modl context.internal rec_var (T.Sigture.body decls)
    }
  in
  (* Elaborate defns into recursive module fields
   * with recursive names added to the context.
  *)
  let (rev_modl_fields, wrap_decls) =
    List.fold_left defns
      ~init:([], ident)
      ~f:(fun (rev_modl_fields, wrap_decls) defn ->
        elab_rec_defn context' (rev_modl_fields, wrap_decls) defn)
  in
  let sigture = T.Sigture.rec_ (rec_var, T.Sigture.body decls) in
  if
    not
      (Type_checker.subsigture context.internal
         (T.Sigture.rec_ (rec_var, T.Sigture.body (wrap_decls (T.Decls.end_ ()))))
         sigture)
  then failwith "???replace with legit error message."
  else begin
    let modl =
      T.Modl.rec_ ((rec_var, sigture), T.Modl.body (List.rev rev_modl_fields))
    in
    let (modl', sigture', elab_context_creator') =
      generalize context modl sigture elab_context_creator
    in
    (* CR wduff: Is [Impure] correct here? *)
    (modl', Impure, sigture', elab_context_creator', fixity_context)
  end

and elab_rec_defns context defns =
  Invariant_checks.context_well_formed context;
  let (modl, purity, sigture, elab_context_creator, fixity_context) =
    elab_rec_defns' context defns
  in
  (* CR wduff: Other post-conditions? *)
  let (purity', sigture') = Type_checker.check_modl context.internal modl in
  assert (Purity.(<=) purity' purity);
  assert (Type_checker.subsigture context.internal sigture' sigture);
  (modl, purity, sigture, elab_context_creator, fixity_context)

(* CR wduff: Reduce code duplication between [elab_rec_defn] and [elab_defn]. *)
and elab_rec_defn' context (rev_modl_fields, wrap_decls) (defn : U.Defn.t) =
  match defn.without_positions with
  | InfixTyp _ | InfixTerm _ ->
    (rev_modl_fields, wrap_decls)
  | TypAlias _ -> failwith "???replace with legit error message."
  | SumTyp (name, args, cases) ->
    let (context_with_args, wrap_typ, wrap_kind) =
      List.fold_right args ~init:(context, ident, ident)
        ~f:(fun arg_name ((context : Context.t), wrap_typ, wrap_kind) ->
          let arg_var = T.Typ.Var.create arg_name in
          ({ context with
             elab =
               Context.Elab.add_typ context.elab arg_name (T.Typ.var arg_var)
           ; internal =
               Context.Internal.add_typ context.internal arg_var (T.Kind.typ ())
           },
           (fun body  ->
              T.Typ.fun_ ((arg_var, (T.Kind.typ ())), wrap_typ body)),
           (fun result_kind  ->
              T.Kind.arrow ((arg_var, (T.Kind.typ ())), wrap_kind result_kind))))
    in
    let uvars () =
      List.map args ~f:(fun _ -> Unification.newvar ())
    in
    let apply_typ_to_uvars typ uvars =
      List.fold uvars ~init:typ ~f:(fun typ uvar ->
        T.Typ.ap (typ, T.Typ.uvar uvar))
    in
    let num_cases = List.length cases in
    let cases' =
      List.map cases
        ~f:(fun (name, typ_opt) ->
          (name,
           Option.map typ_opt ~f:(fun typ ->
             check_typ context_with_args typ (T.Kind.typ ()))))
    in
    let typ_var = T.Typ.Var.create name in
    let typ =
      wrap_typ
        (T.Typ.sum
           (List.map cases'
              ~f:(fun (_, typ_opt) ->
                Option.value typ_opt ~default:(T.Typ.sum []))))
    in
    let modl_var = T.Modl.Var.create name in
    let sigture =
      T.Sigture.body
        (T.Decls.cons
           ((name, T.Decl.Typ (typ_var, wrap_kind (T.Kind.typ ()))),
            decls_of_list
              (List.concat_map cases' ~f:(fun (name, typi_opt) ->
                 let uvars = uvars () in
                 let typ = apply_typ_to_uvars (T.Typ.var typ_var) uvars in
                 let typi_opt =
                   Option.map typi_opt ~f:(fun typi ->
                     apply_typ_to_uvars (wrap_typ typi) uvars)
                 in
                 [ (name,
                    T.Decl.Val
                      (match typi_opt with
                       | None -> typ
                       | Some typi ->
                         T.Typ.arrow (typi, typ)))
                 ; (name,
                    T.Decl.Tag (typ, typi_opt))
                 ]))))
    in
    let modl =
      T.Modl.ascribe
        (T.Modl.body
           ((name, T.Modl_field.Typ typ)
            :: List.mapi cases'
                 ~f:(fun i (name, typi_opt) ->
                   (name,
                    T.Modl_field.Val
                      (match typi_opt with
                       | None ->
                         T.Term.in_ (num_cases, i, T.Term.record String.Map.empty)
                       | Some typi ->
                         let term_var = T.Term.Var.create " f" in
                         let uvars = uvars () in
                         let typi = apply_typ_to_uvars (wrap_typ typi) uvars in
                         T.Term.fun_
                           (([T.Pat.Ascribe (T.Pat.Var term_var, typi)],
                             Some (apply_typ_to_uvars typ uvars)),
                            T.Term.in_
                              (num_cases, i, T.Term.var term_var)))))
            @ List.mapi cases'
                ~f:(fun i (name, _) ->
                  (name,
                   T.Modl_field.Tag (T.Tag.in_ (num_cases, i))))),
         sigture)
    in
    ((name, T.Modl_field.Modl modl) :: rev_modl_fields,
     (fun rest ->
        wrap_decls
          (T.Decls.cons
             (((name, T.Decl.Modl (modl_var, sigture))), rest))))
  | Tag (name, typs_opt, tag) ->
    let (tag', typ1, typ2_opt) =
      match typs_opt with
      | None -> synth_tag context tag
      | Some (typ1, typ2_opt) ->
        let typ1' = check_typ context typ1 (T.Kind.typ ()) in
        let typ2_opt' =
          Option.map typ2_opt
            ~f:(fun typ2 -> check_typ context typ2 (T.Kind.typ ()))
        in
        (check_tag context tag typ1' typ2_opt', typ1', typ2_opt')
    in
    ((name, T.Modl_field.Tag tag') :: rev_modl_fields,
     fun rest ->
       wrap_decls
         (T.Decls.cons ((name, T.Decl.Tag (typ1, typ2_opt)), rest)))
  | Val (pat, term) ->
    (* CR wduff: rename *)
    let foo (pat : U.Pat.t) =
      (match pat.without_positions with
       | Var (_, name) ->
         let (term', typ) = synth_term context term in
         ((name, T.Modl_field.Val term') :: rev_modl_fields,
          fun rest ->
            wrap_decls
              (T.Decls.cons ((name, T.Decl.Val typ), rest)))
       | Ascribe (_pat, _typ) ->
         failwith "unimpl6"
       | _ -> failwith "???replace with legit error message")
    in
    foo pat
  | Fun (name, args, result_typ_opt, body) ->
    let (term, typ) =
      synth_term context
        { start_pos = defn.start_pos
        ; end_pos = defn.end_pos
        ; without_positions = U.Term.Fun (args, result_typ_opt, body)
        }
    in
    ((name, T.Modl_field.Val term) :: rev_modl_fields,
     fun rest -> wrap_decls (T.Decls.cons ((name, T.Decl.Val typ), rest)))
  | Sigture _ -> failwith "unimpl7"
  | Modl (name, arg_opt, sigture_opt, body) ->
    let (modl, _, sigture, _foo_sigture, _fixity_sigture) =
      match arg_opt with
      | None ->
        (match sigture_opt with
         | None -> synth_modl context body
         | Some sigture ->
           synth_modl context
             { start_pos = defn.start_pos
             ; end_pos = defn.end_pos
             ; without_positions = U.Modl.Ascribe (body, sigture)
             })
      | Some (arg_name, arg_sigture) ->
        let arg_var = T.Modl.Var.create arg_name in
        let (arg_sigture', arg_foo_sigture, arg_fixity_sigture) =
          elab_rec_sigture context arg_sigture
        in
        let context' =
          { Context.
            fixity =
              Context.Fixity.add_modl context.fixity arg_name arg_fixity_sigture
          ; elab =
              Context.Elab.add_modl context.elab arg_name
                (T.Modl.var arg_var, elab_sigture_of_foo_sigture arg_foo_sigture)
          ; internal =
              Context.Internal.add_modl context.internal arg_var arg_sigture'
          }
        in
        let (body', _, sigture, elab_sigture, fixity_sigture) =
          (match sigture_opt with
           | None -> synth_modl context' body
           | Some sigture ->
             synth_modl context'
               { start_pos = defn.start_pos
               ; end_pos = defn.end_pos
               ; without_positions = U.Modl.Ascribe (body, sigture)
               })
        in
        (T.Modl.fun_ ((arg_var, arg_sigture'), body'),
         Pure,
         T.Sigture.arrow ((arg_var, arg_sigture'), sigture),
         Context.Elab_sigture.Arrow (arg_foo_sigture, elab_sigture),
         Context.Fixity_sigture.Arrow fixity_sigture)
    in
    ((name, T.Modl_field.Modl modl) :: rev_modl_fields,
     fun rest ->
       wrap_decls
         (T.Decls.cons
            ((name, T.Decl.Modl ((T.Modl.Var.create "_"), sigture)), rest)))
  | Include _ ->
    failwith "???replace with legit error message."

and elab_rec_defn context (rev_modl_fields, wrap_decls) defn =
  Invariant_checks.context_well_formed context;
  (* CR wduff: Other pre-conditions? *)
  let (rev_modl_fields', wrap_decls') =
    elab_rec_defn' context (rev_modl_fields, wrap_decls) defn
  in
  (* CR wduff: post-conditions? *)
  (rev_modl_fields', wrap_decls')

and elab_tag_decl context wrap_decls foo_context name typ1 typ2_opt =
  let typ1' = check_typ context typ1 (T.Kind.typ ()) in
  let typ2_opt' =
    match typ2_opt with
    | None -> None
    | Some typ2 -> Some (check_typ context typ2 (T.Kind.typ ()))
  in
  ((fun decls ->
     wrap_decls
       (T.Decls.cons
          ((name, T.Decl.Tag (typ1', typ2_opt')), decls))),
   Context.Foo.add_tag foo_context name)

and elab_val_decl context wrap_decls foo_context name typ =
  let typ' = check_typ context typ (T.Kind.typ ()) in
  ((fun decls ->
     wrap_decls
       (T.Decls.cons
          ((name, T.Decl.Val typ'), decls))),
   Context.Foo.add_term foo_context name)

and decls_of_defn (context : Context.t) (defn : U.Defn.t)
  : T.Decls.t * Context.Elab_creator.t * Context.Fixity.t =
  match defn.without_positions with
  | InfixTyp _name -> failwith "unimpl9"
  | InfixTerm _name -> failwith "unimpl10"
  | TypAlias (name, args, _) ->
    (singleton_decls
       (name,
        T.Decl.Typ
          (T.Typ.Var.create "_",
           List.fold args ~init:(T.Kind.typ ())
             ~f:(fun acc _ ->
               T.Kind.arrow ((T.Typ.Var.create "_", (T.Kind.typ ())), acc)))),
     Context.Elab_creator.add_typ
       Context.Elab_creator.empty
       name
       (fun modl -> T.Typ.modl_proj (modl, name)),
     Context.Fixity.empty)
  | SumTyp (name, args, cases) ->
    let typ_var = T.Typ.Var.create name in
    let apply_typ_to_uvar_args () =
      let arg_uvars = List.map args ~f:(fun _ -> Unification.newvar ()) in
      List.fold arg_uvars
        ~init:(T.Typ.var typ_var)
        ~f:(fun typ arg_uvar ->
          T.Typ.ap (typ, T.Typ.uvar arg_uvar))
    in
    let term_and_tag_decls =
      List.fold cases ~init:(T.Decls.end_ ())
        ~f:(fun acc (name, typ_opt) ->
          let typ = apply_typ_to_uvar_args () in
          match typ_opt with
          | None ->
            T.Decls.cons
              ((name, T.Decl.Val typ),
               T.Decls.cons
                 ((name, T.Decl.Tag (typ, None)),
                  acc))
          | Some _ ->
            let uvar = Unification.newvar () in
            T.Decls.cons
              ((name,
                T.Decl.Val
                  (T.Typ.arrow (T.Typ.uvar uvar, typ))),
               T.Decls.cons
                 ((name,
                   T.Decl.Tag (typ, Some (T.Typ.uvar uvar))),
                  acc)))
    in
    (singleton_decls
       (name,
        T.Decl.Modl
          (T.Modl.Var.create name,
           T.Sigture.body
             (T.Decls.cons
                ((name,
                  T.Decl.Typ
                    (typ_var,
                     List.fold_right args ~init:(T.Kind.typ ())
                       ~f:(fun arg kind ->
                         T.Kind.arrow
                           ((T.Typ.Var.create arg, T.Kind.typ ()), kind)))),
                 term_and_tag_decls)))),
     List.fold cases
       ~init:(
         Context.Elab_creator.add_typ
           Context.Elab_creator.empty
           name
           (fun modl ->
              T.Typ.modl_proj (T.Modl.modl_proj (modl, name), name)))
       ~f:(fun elab_context_creator (case_name, _) ->
         Context.Elab_creator.add_tag
           (Context.Elab_creator.add_term elab_context_creator case_name
              (fun modl ->
                 T.Term.modl_proj (T.Modl.modl_proj (modl, name), case_name)))
           case_name
           (fun modl ->
              T.Tag.modl_proj (T.Modl.modl_proj (modl, name), case_name))),
     Context.Fixity.empty)
  | Tag (name, _, _) ->
    let u1 = T.Typ.uvar (Unification.newvar ()) in
    let u2 = T.Typ.uvar (Unification.newvar ()) in
    (* CR wduff: how to tell whether second uvar is some/none *)
    (singleton_decls (name, T.Decl.Tag (u1, Some u2)),
     Context.Elab_creator.add_tag Context.Elab_creator.empty name
       (fun modl -> T.Tag.modl_proj (modl, name)),
     Context.Fixity.empty)
  | Val (pat, _) ->
    let names = Set.to_list (Unbound_semantics.names_defined_by_pat pat) in
    (List.fold names ~init:(T.Decls.end_ ())
       ~f:(fun acc name ->
         T.Decls.cons
           ((name, T.Decl.Val (T.Typ.uvar (Unification.newvar ()))),
            acc)),
     List.fold names ~init:Context.Elab_creator.empty
       ~f:(fun acc name ->
         Context.Elab_creator.add_term acc name
           (fun modl -> T.Term.modl_proj (modl, name))),
     Context.Fixity.empty)
  | Fun (name, _, _, _) ->
    (singleton_decls
       (name, T.Decl.Val (T.Typ.uvar (Unification.newvar ()))),
     Context.Elab_creator.add_term Context.Elab_creator.empty name
       (fun modl -> T.Term.modl_proj (modl, name)),
     Context.Fixity.empty)
  | Sigture _ -> failwith "unimpl12"
  | Modl (name, arg_opt, sigture_opt, body) ->
    let (sigture, elab_sigture, fixity_sigture) =
      match arg_opt with
      | None ->
        (match sigture_opt with
         | None -> unification_sigture_of_modl context body
         | Some sigture ->
           let (sigture', foo_sigture, fixity_sigture) =
             elab_unification_sigture context sigture
           in
           (sigture', elab_sigture_of_foo_sigture foo_sigture, fixity_sigture))
      | Some (arg_name, arg_sigture) ->
        let arg_var = T.Modl.Var.create arg_name in
        let (arg_sigture', arg_foo_sigture, arg_fixity_sigture) =
          elab_unification_sigture context arg_sigture
        in
        let context' : Context.t =
          { fixity = Context.Fixity.add_modl context.fixity arg_name arg_fixity_sigture
          ; elab =
              Context.Elab.add_modl context.elab arg_name
                (T.Modl.var arg_var, elab_sigture_of_foo_sigture arg_foo_sigture)
          ; internal = Context.Internal.add_modl context.internal arg_var arg_sigture'
          }
        in
        let (result_sigture, result_elab_sigture, result_fixity_sigture) =
          match sigture_opt with
          | None ->
            unification_sigture_of_modl context' body
          | Some sigture ->
            let (sigture, foo_sigture, fixity_sigture) =
              elab_unification_sigture context' sigture
            in
            (sigture, elab_sigture_of_foo_sigture foo_sigture, fixity_sigture)
        in
        (T.Sigture.arrow ((arg_var, arg_sigture'), result_sigture),
         Context.Elab_sigture.Arrow (arg_foo_sigture, result_elab_sigture),
         Context.Fixity_sigture.Arrow result_fixity_sigture)
    in
    (singleton_decls
       (name,
        T.Decl.Modl
          (T.Modl.Var.create "_", sigture)),
     Context.Elab_creator.add_modl Context.Elab_creator.empty name
       ((fun modl -> (T.Modl.modl_proj (modl, name))), elab_sigture),
     Context.Fixity.add_modl Context.Fixity.empty name fixity_sigture)
  | Include modl ->
    let (_, _, sigture, elab_sigture, fixity_sigture) =
      synth_modl context modl
    in
    (decls_in_sigture sigture,
     (match (elab_sigture : Context.Elab_sigture.t) with
      | Body elab_context_creator -> elab_context_creator
      | Arrow _ -> failwith "???replace with legit error message."),
     (match (fixity_sigture : Context.Fixity_sigture.t) with
      | Body fixity_context -> fixity_context
      | Arrow _ -> failwith "???replace with legit error message."))

and unification_sigture_of_modl context (modl : U.Modl.t)
  : T.Sigture.t * Context.Elab_sigture.t * Context.Fixity_sigture.t =
  match modl.without_positions with
  | Ascribe (_, sigture) ->
    let (sigture, foo_sigture, fixity_sigture) =
      elab_unification_sigture context sigture
    in
    (sigture, elab_sigture_of_foo_sigture foo_sigture, fixity_sigture)
  | Body defns ->
    let (wrap_decls, elab_context_creator, fixity_context) =
      List.fold_right defns
        ~init:(ident, Context.Elab_creator.empty, Context.Fixity.empty)
        ~f:(fun defn (wrap_decls, elab_context_creator, fixity_context) ->
          let (decls', elab_context_creator', fixity_context') =
            decls_of_defn context defn
          in
          ((fun decls ->
             wrap_decls
               (append_decls decls' decls)),
           Context.Elab_creator.merge elab_context_creator elab_context_creator',
           Context.Fixity.merge fixity_context fixity_context'))
    in
    (T.Sigture.body (wrap_decls (T.Decls.end_ ())),
     Body elab_context_creator,
     Body fixity_context)
  | _ ->
    let (_, _, sigture, elab_sigture, fixity_sigture) = synth_modl context modl in
    (sigture, elab_sigture, fixity_sigture)

and decls_in_sigture sigture =
  match T.Sigture.out sigture with
  | Arrow _ -> failwith "???replace with legit error message."
  | Proj_arrow _ -> failwith "unimpl14"
  | Body decls -> decls
  | Rec _ -> failwith "unimpl15" (* CR wduff: when do these even occur *)

and elab_sigture_shared elab_decls (context : Context.t) (sigture : U.Sigture.t)
  : T.Sigture.t * Context.Foo_sigture.t * Context.Fixity_sigture.t =
  match sigture.without_positions with
  | Var (code_pos, name) ->
    (match
       (String.Map.find context.fixity.sigtures name,
        String.Map.find context.elab.sigtures name)
     with
     | (Some fixity_sigture, Some (sigture, foo_sigture)) ->
       (sigture, foo_sigture, fixity_sigture)
     | _ ->
       raise_s
         [%message
           "No such signature."
             (code_pos : Source_code_position.t)
             (name : string)
             (context : Context.t)])
  | Modl_proj _ -> failwith "unimpl17"
  | Arrow ((arg_name, arg_sigture), sigture) ->
    let arg_var = T.Modl.Var.create arg_name in
    let (arg_sigture', arg_foo_sigture, arg_fixity_sigture) =
      elab_sigture_shared elab_decls context arg_sigture
    in
    let context' : Context.t =
      { fixity = Context.Fixity.add_modl context.fixity arg_name arg_fixity_sigture
      ; elab =
          Context.Elab.add_modl context.elab arg_name
            (T.Modl.var arg_var, elab_sigture_of_foo_sigture arg_foo_sigture)
      ; internal = Context.Internal.add_modl context.internal arg_var arg_sigture'
      }
    in
    let (sigture', result_foo_sigture, fixity_sigture) =
      elab_sigture_shared elab_decls context' sigture
    in
    (T.Sigture.arrow ((arg_var, arg_sigture'), sigture'),
     Arrow (arg_foo_sigture, result_foo_sigture),
     Arrow fixity_sigture)
  | Body decls ->
    let (sigture, foo_context, fixity_context) =
      elab_decls context decls
    in
    (sigture, Body foo_context, Body fixity_context)
  | With_type (sigture, (modl_path, typ_field), typ) ->
    let (sigture', foo_sigture, fixity_sigture) =
      elab_sigture_shared elab_decls context sigture
    in
    (* CR wduff: Support types at other kinds. *)
    let typ' = check_typ context typ (T.Kind.typ ()) in
    (sigture_with_type sigture' modl_path typ_field typ',
     foo_sigture,
     fixity_sigture)

and sigture_with_type sigture modl_path typ_field typ =
  match T.Sigture.out sigture with
  | Arrow _ | Proj_arrow _ -> failwith "???replace with legit error message"
  | Body decls ->
    T.Sigture.body (decls_with_type decls modl_path typ_field typ)
  | Rec (modl_var, sigture) ->
    T.Sigture.rec_ (modl_var, sigture_with_type sigture modl_path typ_field typ)

and decls_with_type decls modl_path typ_field typ =
  match T.Decls.out decls with
  | End ->
    raise_s
      [%message
        "???could not find field in decls"
          (modl_path : string list)
          (typ_field : string)]
  | Cons ((field, decl), decls) ->
    match modl_path with
    | [] ->
      begin
        match decl with
        | Typ (typ_var, kind) when String.equal field typ_field ->
          T.Decls.cons ((field, Typ (typ_var, Type_checker.singleton typ kind)), decls)
        | _ ->
          T.Decls.cons ((field, decl), decls_with_type decls modl_path typ_field typ)
      end
    | modl_field :: modl_path ->
      begin
        match decl with
        | Modl (modl_var, sigture) when String.equal field modl_field ->
          T.Decls.cons
            ((field, Modl (modl_var, sigture_with_type sigture modl_path typ_field typ)),
             decls)
        | _ ->
          T.Decls.cons ((field, decl), decls_with_type decls modl_path typ_field typ)
      end

and elab_decls_shared
      elab_tag_decl
      elab_val_decl
      elab_sigture
      (context : Context.t)
      (decls : U.Decl.t list)
  : T.Sigture.t * Context.Foo.t * Context.Fixity.t =
  let (wrap_decls, _, foo_context, fixity_context) =
    List.fold_left decls
      ~init:(ident, context, Context.Foo.empty, Context.Fixity.empty)
      ~f:(fun (wrap_decls, context, foo_context, fixity_context) decl ->
        match decl.without_positions with
        | U.Decl.InfixTyp name ->
          (wrap_decls,
           { context with
             fixity = Context.Fixity.add_infix_typ context.fixity name
           },
           foo_context,
           Context.Fixity.add_infix_typ fixity_context name)
        | U.Decl.InfixTerm name ->
          (wrap_decls,
           { context with
             fixity = Context.Fixity.add_infix_term context.fixity name
           },
           foo_context,
           Context.Fixity.add_infix_term fixity_context name)
        | U.Decl.Typ (name, args, typ_opt) ->
          let typ_var = T.Typ.Var.create name in
          let arg_vars =
            List.map args ~f:(fun arg_name ->
              (arg_name, T.Typ.Var.create arg_name))
          in
          let context' =
            List.fold arg_vars ~init:context
              ~f:(fun context (arg_name, arg_var) ->
                { context with
                  elab =
                    Context.Elab.add_typ context.elab arg_name (T.Typ.var arg_var)
                ; internal =
                    Context.Internal.add_typ context.internal arg_var (T.Kind.typ ())
                })
          in
          let result_kind =
            match typ_opt with
            | None -> (T.Kind.typ ())
            | Some typ ->
              let typ' = check_typ context' typ (T.Kind.typ ()) in
              T.Kind.sing typ'
          in
          let kind =
            List.fold_right arg_vars
              ~init:result_kind
              ~f:(fun (_, arg_var) acc ->
                T.Kind.arrow ((arg_var, (T.Kind.typ ())), acc))
          in
          ((fun decls ->
             wrap_decls
               (T.Decls.cons
                  ((name, T.Decl.Typ (typ_var, kind)), decls))),
           { context with
             elab = Context.Elab.add_typ context.elab name (T.Typ.var typ_var)
           ; internal = Context.Internal.add_typ context.internal typ_var kind
           },
           Context.Foo.add_typ foo_context name,
           fixity_context)
        | U.Decl.Tag (name, typ1, typ2_opt) ->
          let (wrap_decls, foo_context) =
            elab_tag_decl context wrap_decls foo_context name typ1 typ2_opt
          in
          (wrap_decls, context, foo_context, fixity_context)
        | U.Decl.Val (name, typ) ->
          let (wrap_decls, foo_context) =
            elab_val_decl context wrap_decls foo_context name typ
          in
          (wrap_decls, context, foo_context, fixity_context)
        | U.Decl.Sigture (name, sigture) ->
          let (sigture', foo_sigture, fixity_sigture) =
            elab_sigture context sigture
          in
          (wrap_decls,
           { context with
             fixity = Context.Fixity.add_sigture context.fixity name fixity_sigture
           ; elab = Context.Elab.add_sigture context.elab name (sigture', foo_sigture)
           },
           Context.Foo.add_sigture foo_context name foo_sigture,
           Context.Fixity.add_sigture fixity_context name fixity_sigture)
        | U.Decl.Modl (name, sigture) ->
          let modl_var = T.Modl.Var.create name in
          let (sigture', foo_sigture, fixity_sigture) =
            elab_sigture context sigture
          in
          ((fun decls ->
             wrap_decls
               (T.Decls.cons
                  ((name, T.Decl.Modl (modl_var, sigture')), decls))),
           { fixity = Context.Fixity.add_modl context.fixity name fixity_sigture
           ; elab =
               Context.Elab.add_modl context.elab name
                 (T.Modl.var modl_var, elab_sigture_of_foo_sigture foo_sigture)
           ; internal =
               Context.Internal.add_modl context.internal modl_var sigture'
           },
           Context.Foo.add_modl foo_context name foo_sigture,
           Context.Fixity.add_modl fixity_context name fixity_sigture)
        | U.Decl.Include sigture ->
          let (_sigture', _foo_sigture, _fixity_sigture) =
            elab_sigture context sigture
          in
          failwith "unimpl20")
  in
  (T.Sigture.body (wrap_decls (T.Decls.end_ ())), foo_context, fixity_context)

and elab_unification_sigture context sigture : T.Sigture.t * Context.Foo_sigture.t * Context.Fixity_sigture.t =
  elab_sigture_shared
    (elab_decls_shared
       elab_tag_unification_decl
       elab_val_unification_decl
       elab_unification_sigture)
    context
    sigture

and elab_tag_unification_decl _context wrap_decls foo_context name _typ1 typ2_opt =
  let typ1 = T.Typ.uvar (Unification.newvar ()) in
  let typ2_opt =
    Option.map typ2_opt ~f:(fun _ ->
      T.Typ.uvar (Unification.newvar ()))
  in
  ((fun decls ->
     wrap_decls
       (T.Decls.cons
          ((name, T.Decl.Tag (typ1, typ2_opt)), decls))),
   Context.Foo.add_tag foo_context name)

and elab_val_unification_decl _context wrap_decls foo_context name _typ =
  let typ = T.Typ.uvar (Unification.newvar ()) in
  ((fun decls ->
     wrap_decls
       (T.Decls.cons
          ((name, T.Decl.Val typ), decls))),
   Context.Foo.add_term foo_context name)

and elab_decls_typ_part context decls =
  elab_decls_shared
    (fun _context wrap_decls foo_context _name _typ1 _typ2_opt ->
       (wrap_decls, foo_context))
    (fun _context wrap_decls foo_context _name _typ ->
       (wrap_decls, foo_context))
    elab_sigture_typ_part
    context
    decls

and elab_sigture_typ_part context decls =
  elab_sigture_shared elab_decls_typ_part context decls

and elab_rec_decls context decls =
  let (typ_part, foo_context, fixity_context) =
    elab_decls_typ_part context decls
  in
  let rec_var = T.Modl.Var.create " k" in
  let context' =
    { Context.
      fixity = Context.Fixity.merge context.fixity fixity_context
    ; elab =
        (try
           Context.Elab.merge context.elab
             (Context.Elab_creator.apply
                (elab_context_of_foo_context foo_context)
                (T.Modl.var rec_var))
         with _ ->
           raise_s
             [%message
               ""
                 (context.elab : Context.Elab.t)
                 ((Context.Elab_creator.apply
                     (elab_context_of_foo_context foo_context)
                     (T.Modl.var rec_var))
                  : Context.Elab.t)])
    ; internal =
        Context.Internal.add_modl context.internal rec_var typ_part
    }
  in
  let (sigture, foo_context, fixity_context) =
    elab_decls_shared
      elab_tag_decl
      elab_val_decl
      elab_rec_sigture
      context'
      decls
  in
  (T.Sigture.rec_ (rec_var, sigture), foo_context, fixity_context)

and elab_rec_sigture context sigture =
  elab_sigture_shared
    elab_rec_decls
    context
    sigture
;;

let translate defns =
  let typ_var_1 = T.Typ.Var.create "x" in
  let typ_var_2 = T.Typ.Var.create "y" in
  let (modl, _, _, _, _) =
    elab_defns
      { fixity =
          { Context.Fixity.empty with
            infix_typs =
              String.Map.of_alist_exn
                [ ("->", String.Map.of_alist_exn [("->", Parse_infix.Less); ("*", Parse_infix.Less)])
                ; ("*", String.Map.of_alist_exn [("->", Parse_infix.Greater); ("*", Parse_infix.Greater)])
                ]
          }
      ; elab =
          { Context.Elab.empty with
            typs =
              String.Map.of_alist_exn
                ([ ("unit", T.Typ.record String.Map.empty)
                 ; ("number", T.Typ.number ())
                 ; ("char", T.Typ.char ())
                 ; ("string", T.Typ.string ())
                 ; ("*",
                    T.Typ.fun_
                      ((typ_var_1, (T.Kind.typ ())),
                       T.Typ.fun_
                         ((typ_var_2, (T.Kind.typ ())),
                          T.Typ.record
                            (String.Map.of_alist_exn
                               [ ("0", T.Typ.var typ_var_1)
                               ; ("1", T.Typ.var typ_var_2)
                               ]))))
                 ; ("->",
                    T.Typ.fun_
                      ((typ_var_1, (T.Kind.typ ())),
                       T.Typ.fun_
                         ((typ_var_2, (T.Kind.typ ())),
                          T.Typ.arrow (T.Typ.var typ_var_1, T.Typ.var typ_var_2))))
                 ])
          }
      ; internal = Context.Internal.empty
      }
      defns
  in
  T.Term.let_
    (T.Defn.Modl (T.Modl.Var.create "???", modl),
     T.Term.record String.Map.empty)
;;
