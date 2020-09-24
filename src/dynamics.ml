(* CR wduff: Actually propagate types around... *)

open! Core
open! Import

open Typed

exception MatchFailure

type substitution =
  { tags : Tag.t Tag.Var.Map.t
  ; terms : Term.t Term.Var.Map.t
  ; modls : Modl.t Modl.Var.Map.t
  }

let empty_subst =
  { tags = Tag.Var.Map.empty
  ; terms = Term.Var.Map.empty
  ; modls = Modl.Var.Map.empty
  }

let merge subst1 subst2 =
  { tags =
      Map.fold subst2.tags ~init:subst1.tags
        ~f:(fun ~key ~data acc -> Map.set acc ~key ~data)
  ; terms =
      Map.fold subst2.terms ~init:subst1.terms
        ~f:(fun ~key ~data acc -> Map.set acc ~key ~data)
  ; modls =
      Map.fold subst2.modls ~init:subst1.modls
        ~f:(fun ~key ~data acc -> Map.set acc ~key ~data)
  }

module type Subst_into = sig
  type t
  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

let apply_subst (type a) (module S : Subst_into with type t = a) subst (value : a) =
  let value' =
    Map.fold subst.tags ~init:value
      ~f:(fun ~key ~data term -> S.subst Tag data key term)
  in
  let value'' =
    Map.fold subst.terms ~init:value'
      ~f:(fun ~key ~data term -> S.subst Term data key term)
  in
  Map.fold subst.modls ~init:value''
    ~f:(fun ~key ~data term -> S.subst Modl data key term)

let rec eval_tag tag =
  let () = printf "begin eval_tag\n%!" in
  let open Tag in
  let result =
    match out tag with
    | Var _ -> failwith "???cannot eval free var"
    | In i -> in_ i
    | Destr term -> destr (eval term)
    | Modl_proj (modl, field) ->
      match Modl.out (eval_modl modl) with
      | Modl.Body fields ->
        (match
           List.find_map fields
             ~f:(function
               | (field', modl_field) when String.equal field field' ->
                 (match modl_field with
                  | Tag tag' -> Some tag'
                  | _ -> None)
               | _ -> None)
         with
         | Some tag' ->
           eval_tag tag'
         | None -> assert false)
      | _ -> assert false
  in
  let () = printf "end eval_tag\n%!" in
  result

and trypat pat term =
  let () = printf "begin trypat\n%!" in
  let open Pat in
  let result =
    match pat with
    | Wild -> Some empty_subst
    | Var var ->
      Some
        { empty_subst with
          terms =
            Map.set empty_subst.terms ~key:var ~data:term
        }
    | Record pat_fields ->
      (match Term.out term with
       | Term.Record term_fields ->
         (match
            Map.merge pat_fields term_fields ~f:(fun ~key:_ ->
              function
              | `Left _ | `Right _ -> assert false
              | `Both (pat, term) ->
                Some (trypat pat term))
            |> Map.data
            |> Option.all
          with
          | None -> None
          | Some substs ->
            Some (List.fold substs ~init:empty_subst ~f:merge))
       | _ -> assert false)
    | Tag (tag, pat_opt) ->
      let term_opt =
        match Tag.out (eval_tag tag) with
        | Tag.In (_, i) ->
          (match Term.out term with
           | Term.In (_, j, term') ->
             if Int.equal i j
             then Some term'
             else None
           | _ ->
             failwithf !"%{sexp: Term.t}" term ())
        | Tag.Destr tag_term ->
          (match Term.out (eval (Term.ap (tag_term, term))) with
           | Term.In (_, 0, _) -> None
           | Term.In (_, 1, term') -> Some term'
           | _ -> assert false)
        | _ -> assert false
      in
      Option.bind term_opt ~f:(fun term' ->
        match pat_opt with
        | None -> Some empty_subst
        | Some pat' -> trypat pat' term')
    | Number _ | String _ -> failwith "unimpl2"
    | Ascribe (pat', _) -> trypat pat' term
  in
  let () = printf "end trypat\n%!" in
  result

and eval term =
  let () = printf "begin eval\n%!" in
  let open Term in
  let result =
    match out term with
    | Var _ -> failwith "???cannot eval free var"
    | Modl_proj (modl, field) ->
      (match Modl.out (eval_modl modl) with
       | Modl.Body fields ->
         (match
            List.find_map fields
              ~f:(function
                | (field', modl_field) when String.equal field field' ->
                  (match modl_field with
                   | Val term' -> Some term'
                   | _ -> None)
                | _ -> None)
          with
          | Some term' ->
            eval term'
          | None -> assert false)
       | _ -> assert false)
    | Fun _ -> term
    | Ap (term1, term2) ->
      begin
        let term1' = eval term1 in
        let term2' = eval term2 in
        match out term1' with
        | Built_in (name, _) ->
          (match name with
           | "print" ->
             (match out term2' with
              | String string ->
                printf "%s\n%!" string;
                record String.Map.empty
              | _ -> assert false)
           | "string_init" ->
             (match out term2' with
              | Record fields ->
                (match Map.to_alist fields with
                 | [ ("f", fun_term); ("length", length_term) ] ->
                   (match out length_term with
                    | Number n ->
                      List.init (Int64.to_int_exn n) ~f:(fun i ->
                        match out (eval (ap (fun_term, number (Int64.of_int i)))) with
                        | Char c -> c
                        | _ -> assert false)
                      |> String.of_char_list
                      |> string
                    | _ -> assert false)
                 | _ -> assert false)
              | _ -> assert false)
           | "string_length" ->
             (match out term2' with
              | String string -> number (Int64.of_int (String.length string))
              | _ -> assert false)
           | "string_unsafe_nth" ->
             (match out term2' with
              | Record fields ->
                (match Map.to_alist fields with
                 | [ ("n", index_term); ("string", string_term) ] ->
                   (match (out string_term, out index_term) with
                    | (String string, Number n) ->
                      char (String.get string (Int64.to_int_exn n))
                    | _ -> assert false)
                 | _ -> assert false)
              | _ -> assert false)
           | "number_compare" -> failwith "unimpl"
           | "char_compare" -> failwith "unimpl"
           | _ -> failwith "unimpl")
        | Fun ((arg::args, typ_opt), term1') ->
          (match trypat arg term2' with
           | None -> raise MatchFailure
           | Some subst ->
             if List.is_empty args
             then eval (apply_subst (module Term) subst term1')
             else fun_ ((args, typ_opt), apply_subst (module Term) subst term1'))
        | _ -> assert false
      end
    | Typ_fun _ | Typ_ap _ -> failwith "unimpl3"
    | Record fields ->
      record (Map.map fields ~f:eval)
    | In (n, i, term') ->
      in_ (n, i, eval term')
    | Match (term', cases) ->
      let term'' = eval term' in
      let rec trycases = function
        | [] -> raise MatchFailure
        | (pati, termi)::cases ->
          (match trypat pati term'' with
           | None -> trycases cases
           | Some subst -> apply_subst (module Term) subst termi)
      in
      eval (trycases cases)
    | Number _ -> term
    | Char _ -> term
    | String _ -> term
    | Built_in _ -> term
    | Let (defn, term') ->
      let (_modl_field, subst) = eval_defn defn in
      eval (apply_subst (module Term) subst term')
    | Ascribe (term, _) -> eval term
  in
  let () = printf "end eval\n%!" in
  result

and eval_defn defn =
  let () = printf "begin eval_defn\n%!" in
  let open Defn in
  let (result : Modl_field.t * substitution) =
    match defn with
    | Typ (_var, typ) -> (Typ typ, empty_subst)
    | Tag (var, tag) ->
      let tag' = eval_tag tag in
      (Tag tag',
       { empty_subst with
         tags =
           Map.set empty_subst.tags ~key:var ~data:tag'
       })
    | Val (var, term) ->
      let term' = eval term in
      (Val term',
       { empty_subst with
         terms =
           Map.set empty_subst.terms ~key:var ~data:term'
       })
    | Modl (var, modl) ->
      let modl' = eval_modl modl in
      (Modl modl',
       { empty_subst with
         modls =
           Map.set empty_subst.modls ~key:var ~data:modl'
       })
  in
  let () = printf "end eval_defn\n%!" in
  result

and eval_modl modl =
  let () = printf "begin eval_modl\n%!" in
  let open Modl in
  let result =
    match out modl with
    | Var _ -> failwith "???cannot eval free var"
    | Modl_proj (modl, field) ->
      (match Modl.out (eval_modl modl) with
       | Modl.Body fields ->
         (match
            List.find_map fields
              ~f:(function
                | (field', modl_field) when String.equal field field' ->
                  (match modl_field with
                   | Modl modl' -> Some modl'
                   | _ -> None)
                | _ -> None)
          with
          | Some modl' ->
            eval_modl modl'
          | None -> assert false)
       | _ -> assert false)
    | Fun _ -> modl
    | Proj_fun _ -> modl
    | Ap (modl1, modl2) ->
      (match out (eval_modl modl1) with
       | Fun ((arg_var, _), modl1') ->
         let modl2' = eval_modl modl2 in
         eval_modl (subst Modl modl2' arg_var modl1')
       | _ -> assert false)
    | Proj_ap (modl1, modl2) ->
      (match out (eval_modl modl1) with
       | Proj_fun ((arg_var, _), modl1') ->
         let modl2' = eval_modl modl2 in
         eval_modl (subst Modl modl2' arg_var modl1')
       | _ -> assert false)
    | Ascribe (modl, _) -> eval_modl modl
    | Rec ((var, sigture), modl) ->
      let modl' = eval_modl modl in
      eval_modl (subst Modl (rec_ ((var, sigture), modl')) var modl')
    | Body fields ->
      body
        (List.map fields
           ~f:(fun (field_name, modl_field) ->
             let (modl_field' : Modl_field.t) =
               match modl_field with
               | Typ typ -> Typ typ
               | Tag tag -> Tag (eval_tag tag)
               | Val term -> Val (eval term)
               | Modl modl -> Modl (eval_modl modl)
             in
             (field_name, modl_field')))
    | Dep_body defns ->
      body (eval_defns defns)
    | Let (defn, modl) ->
      let (_modl_field, subst) = eval_defn defn in
      eval_modl (apply_subst (module Modl) subst modl)
  in
  let () = printf "end eval_modl\n%!" in
  result

and eval_defns defns =
  let () = printf "begin eval_defns\n%!" in
  let result =
    match Defns.out defns with
    | End -> []
    | Cons ((name, defn), defns) ->
      let (modl_field, subst) = eval_defn defn in
      (name, modl_field) :: (eval_defns (apply_subst (module Defns) subst defns))
  in
  let () = printf "end eval_defns\n%!" in
  result
;;
