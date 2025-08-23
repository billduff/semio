open! Core
open! Import
open Core_ir

(* CR wduff: Consider whether there is anything to be gained by making "length" be a kind, rather
   than a separate syntactic class. This seems useful if things like kind len -> typ layout are
   useful (probably with other dependent kind features as well?) *)

(* CR wduff: Support or-patterns in a first-class way? *)

module Length_context = struct
  type t = Length.Var.Set.t

  let empty = Length.Var.Set.empty
end

module Typ_context = struct
  type t = Kind.t Typ.Var.Map.t

  let empty = Typ.Var.Map.empty
end

module Term_context = struct
  type t = Typ.t Term.Var.Map.t

  let empty = Term.Var.Map.empty
end

let map_disjoint_union_exn map1 map2 =
  Map.merge_skewed map1 map2 ~combine:(fun ~key:_ _ _ ->
    raise_s [%message "[map_disjoint_union_exn]: Got duplicate key."])

let map_disjoint_union_list_exn
      (type k cw)
      (module M : Map.S_plain with type Key.t = k and type Key.comparator_witness = cw)
      (maps : (k, _, cw) Map.t list)
  : (k, _, cw) Map.t =
  List.fold maps ~init:M.empty
    ~f:(Map.merge_skewed ~combine:(fun ~key:_ _ _ ->
      raise_s [%message "[map_disjoint_union_exn]: Got duplicate key."]))

let length_equal context length1 length2 =
  match Length.out length1, Length.out length2 with
  | Var len_var1, Var len_var2 ->
    Length.Var.equal len_var1 len_var2
    && Set.mem context len_var1
  | Static m, Static n -> Int.equal m n
  | _ -> false

let rec static_layout_equal context (layout1 : Static_layout.t) (layout2 : Static_layout.t) =
  match layout1, layout2 with
  | Normal_8, Normal_8 -> true
  | Normal_16, Normal_16 -> true
  | Normal_32, Normal_32 -> true
  | Normal_64, Normal_64 -> true
  | Float_32, Float_32 -> true
  | Float_64, Float_64 -> true
  | Array (length1, layout1), Array (length2, layout2) ->
    length_equal context length1 length2
    && static_layout_equal context layout1 layout2
  | Multi layouts1, Multi layouts2 ->
    (* Layout order matters, because otherwise we can write the following broken code:

       {v
         let f : forall (t : typ (normal_8 * normal_64)). t -> t =
           fun (t : typ (normal_8 * normal_64)) (v : t) => *(alloc[t] v)
         in
         let type u = { foo : int64, bar : int8 } in
         (f[u] { foo = 0, bar = 1 }).bar
       v}

       which will evaluate to 0, when it should evaluate to 1. However, collapsing nested multis is
       fine. *)
    let rec concat_multis (layouts : Static_layout.t list) =
      List.concat_map layouts ~f:(function
        | Multi layouts -> concat_multis layouts
        | layout -> [ layout ])
    in
    let layouts1 = concat_multis layouts1 in
    let layouts2 = concat_multis layouts2 in
    List.length layouts1 = List.length layouts2
    && List.for_all2_exn layouts1 layouts2 ~f:(static_layout_equal context)
  | _, _ -> false
;;

let rec dynamic_layout_equal context layout1 layout2 =
  match Dynamic_layout.out layout1, Dynamic_layout.out layout2 with
  | Static layout1, Static layout2 -> static_layout_equal context layout1 layout2
  | Exists_len (len_var1, layout1), Exists_len (len_var2, layout2) ->
    dynamic_layout_equal
      context
      layout1
      (Dynamic_layout.subst Length (Length.var len_var1) len_var2 layout2)
  | _ -> false

let kind_equal : Length_context.t -> Kind.t -> Kind.t -> bool = failwith "unimpl"

let check_length context (length : Length.t) =
  match Length.out length with
  | Var len_var ->
    if Set.mem context len_var
    then ()
    else raise_s [%message "kind error"]
  | Static _ -> ()

let rec check_static_layout context (layout : Static_layout.t) =
  match layout with
  | Normal_8 | Normal_16 | Normal_32 | Normal_64 | Float_32 | Float_64 -> ()
  | Multi layouts -> List.iter layouts ~f:(check_static_layout context)
  | Array (length, elt_layout) ->
    check_length context length;
    check_static_layout context elt_layout

let rec check_dynamic_layout context (layout : Dynamic_layout.t) =
  match Dynamic_layout.out layout with
  | Static layout -> check_static_layout context layout
  | Multi (static_layouts, dynamic_layout) ->
    List.iter static_layouts ~f:(check_static_layout context);
    check_dynamic_layout context dynamic_layout
  | Exists_len (len_var, layout) ->
    check_dynamic_layout (Set.add context len_var) layout

let rec check_kind context (kind : Kind.t) =
  match kind with
  | Arrow (arg_kind, result_kind) ->
    check_kind context arg_kind;
    check_kind context result_kind;
  | Typ layout -> check_dynamic_layout context layout

let rec synth_typ len_context context typ : Kind.t =
  match Typ.out typ with
  | Var typ_var ->
    (match Map.find context typ_var with
     | Some kind -> kind
     | None ->
       raise_s [%message "kind error"])
  | Fun ((arg_var, arg_kind), body) ->
    check_kind len_context arg_kind;
    let result_kind =
      synth_typ len_context (Map.add_exn context ~key:arg_var ~data:arg_kind) body
    in
    Arrow (arg_kind, result_kind)
  | Ap (func, arg) ->
    let func_kind = synth_typ len_context context func in
    let arg_kind = synth_typ len_context context arg in
    (match func_kind with
     | Arrow (arg_kind', result_kind) ->
       if kind_equal len_context arg_kind arg_kind'
       then result_kind
       else raise_s [%message "kind error"]
     | _ -> raise_s [%message "kind error"])
  (* All negative types are represented the same way: As a pointer to some code that does a match on
     the eliminators. In fact, in the case of a deep eliminator pattern match, the inner negative
     values won't even have an explicit representation: they'll just be part of the overall pattern
     match.

     These types _don't_ support closure over the environment, because that causes less efficient
     layout. Instead, closures may be encoded explicitly as something like:
     [exists env : typ ?. env * (env -> <rest>)]. *)
  | Arrow (arg_typ, result_typ) ->
    (match synth_typ len_context context arg_typ with
     | Typ _ -> ()
     | Arrow _ -> raise_s [%message "kind error"]);
    (match synth_typ len_context context result_typ with
     | Typ _ -> ()
     | Arrow _ -> raise_s [%message "kind error"]);
    Typ (Dynamic_layout.static Normal_64)
  | Neg_prod fields ->
    List.iter fields ~f:(fun (_label, typ) ->
      match synth_typ len_context context typ with
      | Typ _ -> ()
      | Arrow _ -> raise_s [%message "kind error"]);
    Typ (Dynamic_layout.static Normal_64)
  | Corec (typ_var, typ) ->
    (match
       synth_typ
         len_context
         (Map.add_exn context ~key:typ_var ~data:(Typ (Dynamic_layout.static Normal_64)))
         typ
     with
     | Typ _ -> ()
     | Arrow _ -> raise_s [%message "kind error"]);
    Typ (Dynamic_layout.static Normal_64)
  | Pos_prod fields ->
    List.map fields ~f:(fun (_label, typ) ->
      match synth_typ len_context context typ with
      | Arrow _ -> raise_s [%message "kind error"]
      | Typ layout ->
        match Dynamic_layout.out layout with
        | Static layout -> layout
        | Multi _ | Exists_len _ ->
          (* CR wduff: This is the crux of our layout restrictions. It means we can't have a dynamic
             layout in a record, even if that record is unboxed, which is sad in the "local"
             context, but necessary in the "in memory" context. We could have a notion of a
             "boxable" layout, to make this more fine-grained.

             wduff: We can actually allow this boxed and unboxed in the special case that the
             variable length thing is at the end. *)
          raise_s [%message "kind error"])
    |> Multi
    |> Dynamic_layout.static
    |> Typ
  | Sum (layout, clauses) ->
    check_dynamic_layout len_context layout;
    List.iter clauses ~f:(fun (_label, typ) ->
      match synth_typ len_context context typ with
      | Arrow _ -> raise_s [%message "kind error"]
      | Typ layout' ->
        if dynamic_layout_equal len_context layout layout'
        then ()
        else raise_s [%message "kind error"]);
    (* CR wduff: Can we have smaller tags than this? *)
    Typ (Dynamic_layout.multi ([ Normal_64 ], layout))
  | Rec ((typ_var, layout), typ) ->
    check_dynamic_layout len_context layout;
    (match synth_typ len_context (Map.add_exn context ~key:typ_var ~data:(Typ layout)) typ with
     | Arrow _ -> raise_s [%message "kind error"]
     | Typ layout' ->
       if dynamic_layout_equal len_context layout layout'
       then Typ layout
       else raise_s [%message "kind error"])
  (* We have type-erasure for polymorphic and existential types, so their layout matches the layout
     of their contents. *)
  | For_all ((typ_var, kind), typ) ->
    (match synth_typ len_context (Map.add_exn context ~key:typ_var ~data:kind) typ with
     | Arrow _ -> raise_s [%message "kind error"]
     | Typ layout -> Typ layout)
  | Exists ((typ_var, kind), typ) ->
    (match synth_typ len_context (Map.add_exn context ~key:typ_var ~data:kind) typ with
     | Arrow _ -> raise_s [%message "kind error"]
     | Typ layout -> Typ layout)
  | Exists_len (len_var, typ) ->
    (match synth_typ (Set.add len_context len_var) context typ with
     | Arrow _ -> raise_s [%message "kind error"]
     | Typ layout ->
       Typ (Dynamic_layout.exists_len (len_var, layout)))
  | Uninit layout -> Typ (Dynamic_layout.static layout)
  | Array (length, elt_typ) ->
    check_length len_context length;
    (match synth_typ len_context context elt_typ with
     | Arrow _ -> raise_s [%message "kind error"]
     | Typ elt_layout ->
       match Dynamic_layout.out elt_layout with
       | Static elt_layout -> Typ (Dynamic_layout.static (Array (length, elt_layout)))
       | Multi _ | Exists_len _ ->
         (* CR wduff: This is another important layout restriction, but unlike the record one, this
            is just necessary generally if you want to avoid slow access. *)
         raise_s [%message "kind error"])
  | Box typ ->
    (match synth_typ len_context context typ with
     | Typ _ -> ()
     | Arrow _ -> raise_s [%message "kind error"]);
    Typ (Dynamic_layout.static Normal_64)

and check_typ length_context context typ kind =
  let kind' = synth_typ length_context context typ in
  if kind_equal Length_context.empty kind kind'
  then ()
  else raise_s [%message "kind error"]

let normalize_typ : Length_context.t -> Typ_context.t -> Typ.t -> Typ.t = failwith "unimpl"

let typ_equal : Length_context.t -> Typ_context.t -> Typ.t -> Typ.t -> bool = failwith "unimpl"

(* CR wduff: Make sure we're checking all "user-provided" types. *)
let rec synth_value_pat typ_context (pat : Value_pat.t) =
  match pat with
  | Var (var, typ) -> Typ.Var.Map.empty, Term.Var.Map.singleton var typ, typ
  | Wild typ -> Typ.Var.Map.empty, Term.Var.Map.empty, typ
  | Record (fields, field_order) ->
    let (typ_contexts, term_contexts, typ_by_field) =
      List.map fields ~f:(fun (field, pat) ->
        let (typ_context, term_context, typ) =
          synth_value_pat typ_context pat
        in
        (typ_context, term_context, (field, typ)))
      |> List.unzip3
    in
    let typ_by_field =
      Label.Table.of_alist_exn typ_by_field
    in
    let field_typs =
      if Hashtbl.length typ_by_field <> List.length field_order
      then raise_s [%message "type error"]
      else begin
        List.map field_order ~f:(fun field ->
          match Hashtbl.find typ_by_field field with
          | None -> raise_s [%message "type error"]
          | Some typ -> (field, typ))
      end
    in
    map_disjoint_union_list_exn (module Typ.Var.Map) typ_contexts,
    map_disjoint_union_list_exn (module Term.Var.Map) term_contexts,
    Typ.pos_prod field_typs
  | Inj (tag, pat, tag_typs) ->
    (match List.Assoc.find tag_typs tag ~equal:Label.equal with
     | None -> raise_s [%message "type error"]
     | Some typ ->
       let (typ_context, term_context) = check_value_pat typ_context pat typ in
       (* CR wduff: Should we just require an explicit layout on the pat too? *)
       let layout = failwith "unimpl" in
       typ_context, term_context, Typ.sum (layout, tag_typs))
  | Roll (pat, (Bind (typ_var, typ), layout)) ->
    let rec_typ = Typ.rec_ ((typ_var, layout), typ) in
    let typ_context, term_context =
      check_value_pat typ_context pat (Typ.subst Typ rec_typ typ_var typ)
    in
    typ_context, term_context, rec_typ
  | Pack ((typ_var, kind), pat) ->
    let typ_context, term_context, typ =
      synth_value_pat (Map.add_exn typ_context ~key:typ_var ~data:kind) pat
    in
    Map.add_exn typ_context ~key:typ_var ~data:kind,
    term_context,
    Typ.exists ((typ_var, kind), typ)

and check_value_pat typ_context pat typ =
  let typ_context', term_context, typ' = synth_value_pat typ_context pat in
  (* CR wduff: Should this include typ_context'? *)
  if typ_equal Length_context.empty typ_context typ typ'
  then typ_context', term_context
  else raise_s [%message "type error"]

(* CR wduff: The empty case is weird. Should it be lazy or something? *)
let rec synth_elim_match_case typ_context term_context (pats : Elim_pat.t list) body =
  match pats with
  | [] ->
    synth_term typ_context term_context body
  | pat :: pats ->
    match pat with
    | Ap value_pat ->
      (* CR wduff: Extend instead of replacing the context *)
      let typ_context, term_context, typ = synth_value_pat typ_context value_pat in
      (* CR wduff: Use substitution instead of thunks? *)
      let result_typ = synth_elim_match_case typ_context term_context pats body in
      Typ.arrow (typ, result_typ)
    | Proj (field, field_typs) ->
      (match List.Assoc.find field_typs field ~equal:Label.equal with
       | None -> raise_s [%message "type error"]
       | Some typ ->
         check_elim_match_case typ_context term_context pats body typ;
         Typ.neg_prod field_typs)
    | Unroll (Bind (typ_var, typ)) ->
      let corec_typ = Typ.corec (typ_var, typ) in
      check_elim_match_case typ_context term_context pats body (Typ.subst Typ corec_typ typ_var typ);
      corec_typ
    | Ap_typ (typ_var, kind) ->
      let result_typ =
        synth_elim_match_case (Map.add_exn typ_context ~key:typ_var ~data:kind) term_context pats body
      in
      Typ.for_all ((typ_var, kind), result_typ)

and check_elim_match_case typ_context term_context pats body typ =
  let typ' = synth_elim_match_case typ_context term_context pats body in
  if typ_equal Length_context.empty typ_context typ typ'
  then ()
  else raise_s [%message "type error"]

(* CR wduff: Check for match exhaustiveness for both kinds of match. *)
(* CR wduff: Make sure we're checking all "user-provided" types. *)
and synth_term typ_context context term =
  match Term.out term with
  | Var var ->
    (match Map.find context var with
     | Some typ -> typ
     | None ->
       raise_s [%message "type error"])
  | Record (fields, field_order) ->
    let typ_by_field =
      List.map fields ~f:(fun (field, term) ->
        (field, synth_term typ_context context term))
      |> Label.Table.of_alist_exn
    in
    let field_typs =
      if Hashtbl.length typ_by_field <> List.length field_order
      then raise_s [%message "type error"]
      else begin
        List.map field_order ~f:(fun field ->
          match Hashtbl.find typ_by_field field with
          | None -> raise_s [%message "type error"]
          | Some typ -> (field, typ))
      end
    in
    Typ.pos_prod field_typs
  | Inj (tag, term, tag_typs) ->
    (match List.Assoc.find tag_typs tag ~equal:Label.equal with
     | None -> raise_s [%message "type error"]
     | Some typ ->
       check_term typ_context context term typ;
       (* CR wduff: Should we just require an explicit layout on the term too? *)
       let layout = failwith "unimpl" in
       Typ.sum (layout, tag_typs))
  | Roll (term, ((typ_var, layout), typ)) ->
    let rec_typ = Typ.rec_ ((typ_var, layout), typ) in
    let expanded_typ = Typ.subst Typ rec_typ typ_var typ in
    check_term typ_context context term expanded_typ;
    rec_typ
  | Pack (typ, term, (typ_var, typ')) ->
    let kind = synth_typ Length_context.empty typ_context typ in
    check_term typ_context context term (Typ.subst Typ typ typ_var typ');
    Typ.exists ((typ_var, kind), typ')
  | Match_value (term, cases, typ') ->
    let typ = synth_term typ_context context term in
    List.iter cases ~f:(fun (pat, term) ->
      let pat_typ_context, pat_context = check_value_pat typ_context pat typ in
      let typ_context = map_disjoint_union_exn typ_context pat_typ_context in
      let context = map_disjoint_union_exn context pat_context in
      check_term typ_context context term typ');
    typ'
  | Match_elim (cases, typ) ->
    List.iter cases ~f:(fun (pat, term) ->
      check_elim_match_case typ_context context pat term typ);
    typ
  | Ap (func, arg) ->
    let func_typ = synth_term typ_context context func in
    (match Typ.out (normalize_typ Length_context.empty typ_context func_typ) with
     | Arrow (arg_typ, result_typ) ->
       check_term typ_context context arg arg_typ;
       result_typ
     | _ -> raise_s [%message "type error"])
  | Proj (term, field) ->
    let record_typ = synth_term typ_context context term in
    (match Typ.out (normalize_typ Length_context.empty typ_context record_typ) with
     | Neg_prod fields ->
       (match List.Assoc.find fields field ~equal:Label.equal with
        | Some typ -> typ
        | None -> raise_s [%message "type error"])
     | _ -> raise_s [%message "type error"])
  | Unroll term ->
    let corec_typ = synth_term typ_context context term in
    (match Typ.out (normalize_typ Length_context.empty typ_context corec_typ) with
     | Corec (typ_var, typ) -> Typ.subst Typ corec_typ typ_var typ
     | _ -> raise_s [%message "type error"])
  | Ap_typ (term, typ) ->
    let forall_typ = synth_term typ_context context term in
    (match Typ.out (normalize_typ Length_context.empty typ_context forall_typ) with
     | For_all ((typ_var, kind), typ') ->
       check_typ Length_context.empty typ_context typ kind;
       Typ.subst Typ typ typ_var typ'
     | _ -> raise_s [%message "type error"])
  | Uninit layout ->
    Typ.uninit layout
  | Box term ->
    let typ = synth_term typ_context context term in
    Typ.box typ
  | Heap_loc _loc ->
    (* CR wduff: We need to track which heap locations are in scope. *)
    failwith "unimpl"
  | Unbox term ->
    let box_typ = synth_term typ_context context term in
    (match Typ.out (normalize_typ Length_context.empty typ_context box_typ) with
     | Box typ -> typ
     | _ -> raise_s [%message "type error"])
  | Fix ((var, typ), term) ->
    (* CR wduff: Do we need to check that the term is a value? *)
    check_term typ_context (Map.add_exn context ~key:var ~data:typ) term typ;
    typ
  | Let ((pat, term1), term2) ->
    let typ1 = synth_term typ_context context term1 in
    let pat_typ_context, pat_context = check_value_pat typ_context pat typ1 in
    (* CR wduff: We need to check for types escaping their scope here. *)
    synth_term
      (map_disjoint_union_exn typ_context pat_typ_context)
      (map_disjoint_union_exn context pat_context)
      term2

and check_term typ_context context term typ =
  let typ' = synth_term typ_context context term in
  if typ_equal Length_context.empty typ_context typ typ'
  then ()
  else raise_s [%message "type error"]
;;


(* CR wduff: This doesn't go in the "type checker." *)

let rec is_val context term =
  match Term.out term with
  | Var var -> Map.mem context var
  | Record (fields, _field_order) ->
    List.for_all fields ~f:(fun (_field, term) -> is_val context term)
  | Inj (_tag, term, _tag_typs) ->
    is_val context term
  | Roll (term, _typ) ->
    is_val context term
  | Pack (_typ, term, _typ') ->
    is_val context term
  | Match_elim _ -> true
  | Uninit _layout -> true
  | Heap_loc _ -> true
  | Match_value _
  | Ap _
  | Proj _
  | Unroll _
  | Ap_typ _
  | Box _
  | Unbox _
  | Fix _
  | Let _
    ->
    false

let try_value_pat : Value_pat.t -> Term.t -> Term.t Term.Var.Map.t option = failwith "unimpl"

let apply_subst_multi subst term =
  Map.fold subst ~init:term ~f:(fun ~key:var ~data:value acc ->
    Term.subst Term value var acc)
;;

let rec eval heap term =
  match Term.out term with
  | Var _ -> assert false
  | Record (fields, field_order) ->
    Term.record (List.map fields ~f:(fun (field, term) -> (field, eval heap term)), field_order)
  | Inj (tag, term, tag_typs) ->
    Term.inj (tag, eval heap term, tag_typs)
  | Roll (term, typ) ->
    Term.roll (eval heap term, typ)
  | Pack (typ, term, typ') ->
    Term.pack (typ, eval heap term, typ')
  | Match_elim _ -> term
  | Uninit _layout -> term
  | Match_value (term, cases, _typ) ->
    let value = eval heap term in
    List.find_map cases ~f:(fun (pat, term) ->
      Option.map (try_value_pat pat value) ~f:(fun subst -> apply_subst_multi subst term))
    |> Option.value_exn
  (* CR wduff: What if some of the lists are empty but others aren't? Can we solve this by appealing
     to what would happen if there were explicit shifts? *)
  | Ap (func, arg) ->
    let func = eval heap func in
    let arg = eval heap arg in
    (match Term.out func with
     | Match_elim (cases, typ) ->
       With_return.with_return (fun { return } ->
         let cases =
           (* CR wduff: Should we actually be willing to continue if the value pat fails? *)
           List.filter_map cases ~f:(fun (pats, term) ->
             match pats with
             | [] -> assert false
             | Ap pat :: pats ->
               Option.map (try_value_pat pat arg) ~f:(fun subst ->
                 let term = apply_subst_multi subst term in
                 match pats with
                 | [] -> return (eval heap term)
                 | _::_ ->
                   (pats, term))
             | _ :: _ -> assert false)
         in
         Term.match_elim (cases, typ))
     | _ -> assert false)
  | Proj (term, field) ->
    (* CR wduff: We should make an elim abt so we can share more code. *)
    (match Term.out (eval heap term) with
     | Match_elim (cases, typ) ->
       With_return.with_return (fun { return } ->
         let cases =
           (* CR wduff: Should we actually be willing to continue if the value pat fails? *)
           List.filter_map cases ~f:(fun (pats, term) ->
             match pats with
             | [] -> assert false
             | Proj (field', _field_typs) :: pats ->
               (match Label.equal field field' with
                | false -> None
                | true ->
                  match pats with
                  | [] -> return (eval heap term)
                  | _::_ -> Some (pats, term))
             | _ :: _ -> assert false)
         in
         Term.match_elim (cases, typ))
     | _ -> assert false)
  | Unroll term ->
    (match Term.out (eval heap term) with
     | Match_elim (cases, typ) ->
       With_return.with_return (fun { return } ->
         let cases =
           (* CR wduff: Should we actually be willing to continue if the value pat fails? *)
           List.map cases ~f:(fun (pats, term) ->
             match pats with
             | [] -> assert false
             | Unroll _typ :: pats ->
               (match pats with
                | [] -> return (eval heap term)
                | _::_ -> (pats, term))
             | _ :: _ -> assert false)
         in
         Term.match_elim (cases, typ))
     | _ -> assert false)
  | Ap_typ (term, typ) ->
    (match Term.out (eval heap term) with
     | Match_elim (cases, typ') ->
       With_return.with_return (fun { return } ->
         let cases =
           (* CR wduff: Should we actually be willing to continue if the value pat fails? *)
           List.map cases ~f:(fun (pats, term) ->
             match pats with
             | [] -> assert false
             | Ap_typ (typ_var, _kind) :: pats ->
               let term = Term.subst Typ typ typ_var term in
               (match pats with
                | [] -> return (eval heap term)
                | _::_ -> (pats, term))
             | _ :: _ -> assert false)
         in
         Term.match_elim (cases, typ'))
     | _ -> assert false)
  | Box term ->
    let value = eval heap term in
    let loc = Heap_loc.create () in
    Hashtbl.add_exn heap ~key:loc ~data:value;
    Term.heap_loc loc
  | Heap_loc _ -> term
  | Unbox term ->
    (match Term.out (eval heap term) with
     | Heap_loc loc -> Hashtbl.find_exn heap loc
     | _ -> assert false)
  | Fix ((var, _typ), term) ->
    eval heap (Term.subst Term term var term)
  | Let ((pat, term1), term2) ->
    let value = eval heap term1 in
    let subst =
      try_value_pat pat value
      |> Option.value_exn
    in
    eval heap (apply_subst_multi subst term2)

module Stack_machine = struct
  type address =
    | Stack of int
    | Heap of int

  type value =
    | Literal of int
    | Stack_pointer
    | Read of address

  (* CR wduff: Abstract type? *)
  type bytes = int

  type simple_instruction =
    [ `Push of value
    | `Grow_stack of bytes
    | `Shrink_stack of bytes
    | `Write of address * value
    | `Heap_alloc of bytes
    ]

  type 'a instruction =
    [ `Exit of value
    | `Jump of 'a
    | simple_instruction
    ]
end

let compile term =
  let open Stack_machine in
  check_term Typ_context.empty Term_context.empty term (Typ.base Int);
  let rec compile_term term typ ~dest_stack_offset =
    match Term.out term with
    | Var _ -> assert false
    | Record (fields, _field_order) ->
      let typ_and_dest_stack_offset_by_field =
        match Typ.out typ with
        | Pos_prod field_typs ->
          List.folding_map field_typs ~init:dest_stack_offset ~f:(fun acc (field, typ) ->
            let length = typ in
            (acc - length, (field, (typ, acc))))
          |> Label.Table.of_alist_exn
        | _ -> assert false
      in
      let (blocks, extra_blocks) =
        List.map fields ~f:(fun (field, term) ->
          let (typ, dest_stack_offset) =
            Hashtbl.find_exn typ_and_dest_stack_offset_by_field field
          in
          compile_term term typ ~dest_stack_offset)
        |> List.unzip
      in
      (List.concat blocks, List.concat extra_blocks)
    | Inj (tag, term, tag_typs) ->
      let tag_index =
        List.find_mapi_exn tag_typs ~f:(fun index (tag', _typ) ->
          Option.some_if (Label.equal tag tag') index)
      in
      let (block, extra_blocks) = compile_term term in
      (`Push (Literal tag_index) :: block, extra_blocks)
    | Roll (term, _typ) ->
      compile_term term
    | Pack (_typ, term, _typ') ->
      compile_term term
    | Match_elim (cases, _typ) ->
      let label = Instruction_label.create () in
      let (block, extra_blocks) = compile_elim_cases cases in
      ([ `Push (Literal label) ], [ (label, block) :: extra_blocks ])
    | Uninit layout -> ([ `Grow_stack (bytes_of_layout layout) ], [])
    | Match_value (term, cases, _typ) ->
      let (block, extra_blocks) = compile_term term in
      let labels =
        List.mapi cases ~f:(fun case_index _ -> Instruction_label.create ())
        |> Array.of_list
      in
      List.mapi cases ~f:(fun case_index (pat, term) ->
        let (pat_block, pat_extra_blocks) = compile_try_pat pat in
        let (term_block, term_extra_blocks) = compile_try_pat pat in
        (* CR wduff: Hrm. We need to somehow remove the stuff pat_block would dump on the stack when
           we return, which means we need to know how much stuff term is gonna write in advance, or
           we need to do the crazy ocaml thing. *)
        (pat_block
         @
         [ cmp (relative_stack_read 1)
         ; shrink_stack 1
         ; jump_if_zero labels.(case_index + 1)
         ]
         @
         term_block,
         pat_extra_blocks @ term_extra_blocks))
    | Ap (func, arg) -> ()
    | Proj (term, field) -> ()
    | Unroll term -> ()
    | Ap_typ (term, typ) -> ()
    | Box term -> ()
    | Heap_loc _ -> ()
    | Unbox term -> ()
    | Fix ((var, _typ), term) -> ()
    | Let ((pat, term1), term2) -> ()
  in
  compile term
;;

let rec repeat_until_finished state f =
  match f state with
  | `Repeat state -> repeat_until_finished state f
  | `Finished result -> result
;;

let exec instructions =
  let open Stack_machine in
  let ip = ref 0 in
  let stack = Bigstring.create (10 * 1024 * 1024) in
  let sp = ref 0 in
  let heap = Bigstring.create (1024 * 1024 * 1024) in
  let hp = ref 0 in
  let find_addr : address -> _ = function
    | Stack pos -> (stack, pos)
    | Heap pos -> (heap, pos)
  in
  (* CR wduff: Deal with value sizes. *)
  let get_value (value : value) =
    match value with
    | Literal n -> n
    | Stack_pointer -> !sp
    | Read addr ->
      let (buf, pos) = find_addr addr in
      Bigstring.get_int64_le_trunc buf ~pos
  in
  let push int =
    Bigstring.set_int64_le stack ~pos:!sp int;
    sp := !sp + 8
  in
  repeat_until_finished () (fun () ->
    match instructions.(0) with
    | `Exit value -> `Finished (get_value value)
    | `Jump loc ->
      ip := loc;
      `Repeat ()
    | #simple_instruction as instruction ->
      begin
        match instruction with
        | `Push value ->
          push (get_value value);
        | `Grow_stack bytes ->
          sp := !sp + bytes
        | `Shrink_stack bytes ->
          sp := !sp - bytes
        | `Write (addr, value) ->
          let (buf, pos) = find_addr addr in
          Bigstring.set_int64_le buf ~pos (get_value value)
        | `Heap_alloc bytes ->
          push !hp;
          hp := !hp + bytes
      end;
      incr ip;
      `Repeat ()
  )
;;
