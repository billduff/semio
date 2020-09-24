open! Core
open! Import

module With_positions = struct
  type 'a t =
    { start_pos : Source_code_position.t
    ; end_pos : Source_code_position.t
    ; without_positions : 'a
    }
  [@@deriving sexp_of]
end

module Indentation_tree = struct
  type t =
    { header : string
    ; indentation_amount : int
    ; indented : t list
    ; footer : string option
    }
  [@@deriving fields]

  let node ~header ?footer ?(indentation_amount=2) indented =
    (*let total_width =
       List.max_elt ~cmp:Int.compare
         (String.length header
          :: (match footer with
            |  None -> 0
            | Some footer -> String.length footer)
          :: List.map indented ~f:(fun { total_width; _ } ->
            indentation_amount + total_width))
       |> Option.value_exn
      in*)
    { header; indentation_amount; indented; footer }
  ;;

  let singleton string = node ~header:string []

  let rec flatten { header; indentation_amount = _; indented; footer } =
    String.concat ~sep:" "
      (header :: (List.map indented ~f:flatten @ Option.to_list footer))
  ;;

  let rec to_string_list t ~max_width =
    let string = flatten t in
    if String.length string <= max_width
    then [string]
    else begin
      let indentation = String.init t.indentation_amount ~f:(fun _ -> ' ') in
      t.header
      :: (List.concat_map t.indented
            ~f:(to_string_list ~max_width:(max_width - t.indentation_amount))
          |> List.map ~f:(fun string -> indentation ^ string))
      @ Option.to_list t.footer
    end
  ;;

  let to_string t =
    String.concat ~sep:"\n" (to_string_list t ~max_width:90)
  ;;
end

open Indentation_tree

(* CR wduff: Make these [to_string] functions line up with the parser. *)
module rec Typ : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Ap of Typ.t list
    | Record of (string * Typ.t) list
    | Forall of (string * Typ.t)

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Ap of Typ.t list
    | Record of (string * Typ.t) list
    | Forall of (string * Typ.t)
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | Var (_, name) -> singleton name
    | Modl_proj (modl, name) ->
      singleton (sprintf "%s.%s" (flatten (Modl.to_indentation_tree modl)) name)
    | Ap [] -> assert false
    | Ap (funct :: args) ->
      node ~header:(flatten (Typ.to_indentation_tree funct))
        (List.map args ~f:Typ.to_indentation_tree)
    | Record fields ->
      node ~header:"{" ~footer:"}"
        (List.map fields ~f:(fun (field_name, typ) ->
           node ~header:(sprintf "; %s :" field_name)
             [Typ.to_indentation_tree typ]))
    | Forall (arg_name, result) ->
      node ~header:(sprintf "(type %s)" arg_name)
        [Typ.to_indentation_tree result]
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Decl : sig
  type untagged =
    | InfixTyp of string
    | InfixTerm of string
    | Typ of (string * string list * Typ.t option)
    | Tag of (string * Typ.t * Typ.t option)
    | Val of (string * Typ.t)
    | Sigture of (string * Sigture.t) (* ??? not yet in il *)
    | Modl of (string * Sigture.t)
    | Include of Sigture.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | InfixTyp of string
    | InfixTerm of string
    | Typ of (string * string list * Typ.t option)
    | Tag of (string * Typ.t * Typ.t option)
    | Val of (string * Typ.t)
    | Sigture of (string * Sigture.t)
    | Modl of (string * Sigture.t)
    | Include of Sigture.t
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | InfixTyp name ->
      node ~header:"infix type" [singleton name]
    | InfixTerm name ->
      node ~header:"infix" [singleton name]
    | Typ (name, args, typ_opt) ->
      let without_impl =
        sprintf "type %s%s"
          name
          (if List.is_empty args
           then ""
           else " " ^ String.concat ~sep:" " args)
      in
      (match typ_opt with
       | None -> singleton without_impl
       | Some typ ->
         node ~header:(without_impl ^ " =") [Typ.to_indentation_tree typ])
    | Tag (name, typ1, typ2_opt) ->
      node
        ~header:(sprintf "pat %s :" name)
        (match typ2_opt with
         | None -> [Typ.to_indentation_tree typ1]
         | Some typ2 ->
           [ Typ.to_indentation_tree typ1
           ; singleton "=>"
           ; Typ.to_indentation_tree typ2
           ])
    | Val (name, typ) ->
      node ~header:(sprintf "val %s :" name) [Typ.to_indentation_tree typ]
    | Sigture (name, sigture) ->
      node ~header:(sprintf "signature %s =" name) [Sigture.to_indentation_tree sigture]
    | Modl (name, sigture) ->
      node ~header:(sprintf "module %s :" name) [Sigture.to_indentation_tree sigture]
    | Include sigture ->
      node ~header:"include" [Sigture.to_indentation_tree sigture]
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Sigture : sig
  (* ??? Add sigture calculus operations. *)
  type untagged =
    | Var of (Source_code_position.t * string) (* ??? not yet in il *)
    | Modl_proj of (Modl.t * string) (* ??? not yet in il *)
    | Arrow of ((string * Sigture.t) * Sigture.t) (* ??? not yet in parser *)
    | Body of Decl.t list
    | With_type of Sigture.t * (string list * string) * Typ.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Arrow of ((string * Sigture.t) * Sigture.t)
    | Body of Decl.t list
    | With_type of Sigture.t * (string list * string) * Typ.t
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | Var (_, name) -> singleton name
    | Modl_proj (modl, name) ->
      singleton (sprintf "%s.%s" (flatten (Modl.to_indentation_tree modl)) name)
    | Arrow ((arg_name, arg_sigture), result_sigture) ->
      singleton
        (sprintf !"(%s : %s) -> %s"
           arg_name
           (flatten (Sigture.to_indentation_tree arg_sigture))
           (flatten (Sigture.to_indentation_tree result_sigture)))
    | Body l ->
      node ~header:"sig" ~footer:"end"
        (List.map l ~f:(Decl.to_indentation_tree))
    | With_type (sigture, (path, typ_field), typ) ->
      singleton
        (sprintf "%s with type %s = %s"
           (flatten (Sigture.to_indentation_tree sigture))
           (String.concat ~sep:"."  path ^ "." ^ typ_field)
           (flatten (Typ.to_indentation_tree typ)))
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Tag : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Destr of Term.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Destr of Term.t
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | Var (_, name) -> singleton name
    | Modl_proj (modl, name) ->
      singleton (sprintf "%s.%s" (flatten (Modl.to_indentation_tree modl)) name)
    | Destr term ->
      node ~header:"destr" [Term.to_indentation_tree term]
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Pat : sig
  type untagged =
    | Wild
    | Var of (Source_code_position.t * string)
    | Record of (string * Pat.t) list
    | Tag of (Tag.t * Pat.t option)
    | Number of Int64.t
    | String of string
    | Ascribe of (Pat.t * Typ.t) (**)

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | Wild
    | Var of (Source_code_position.t * string)
    | Record of (string * Pat.t) list
    | Tag of (Tag.t * Pat.t option)
    | Number of Int64.t
    | String of string
    | Ascribe of (Pat.t * Typ.t)
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | Wild -> singleton "_"
    | Var (_, name) -> singleton name
    | Record fields ->
      node ~header:"{" ~footer:"}"
        (List.map fields ~f:(fun (field_name, pat) ->
           node ~header:(sprintf "; %s =" field_name)
             [Pat.to_indentation_tree pat]))
    | Tag (tag, None) -> Tag.to_indentation_tree tag
    | Tag (tag, Some pat) ->
      node ~header:(flatten (Tag.to_indentation_tree tag))
        [Pat.to_indentation_tree pat]
    | Number n -> singleton (Int64.to_string n)
    | String s -> singleton (sprintf !"\"%s\"" (String.escaped s))
    | Ascribe (pat, typ) ->
      singleton
        (sprintf !"(%s : %s)"
           (flatten (Pat.to_indentation_tree pat))
           (flatten (Typ.to_indentation_tree typ)))

  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Term : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string) (* ??? only for modl vars for now *)
    | Fun of (Pat.t list * Typ.t option * Term.t)
    | Ap of Term.t list
    | Record of (string * Term.t) list (* ??? fields could possibly be in modules *)
    | Match of (Term.t * (Pat.t * Term.t) list)
    | Number of Int64.t
    | String of string
    | Built_in of (string * Typ.t)
    | Let of (Defn.t list * Term.t)
    | Ascribe of (Term.t * Typ.t) (**)

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Fun of (Pat.t list * Typ.t option * Term.t)
    | Ap of Term.t list
    | Record of (string * Term.t) list
    | Match of (Term.t * (Pat.t * Term.t) list)
    | Number of Int64.t
    | String of string
    | Built_in of (string * Typ.t)
    | Let of (Defn.t list * Term.t)
    | Ascribe of (Term.t * Typ.t)
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | Var (_, name) -> singleton name
    | Modl_proj (modl, name) ->
      singleton (sprintf "%s.%s" (flatten (Modl.to_indentation_tree modl)) name)
    | Fun (args, typ_opt, body) ->
      node
        ~header:(
          sprintf "fn %s%s => "
            (String.concat ~sep:" "
               (List.map args ~f:(fun pat ->
                  flatten (Pat.to_indentation_tree pat))))
            (match typ_opt with
             | None -> ""
             | Some typ ->
               sprintf ": %s" (flatten (Typ.to_indentation_tree typ))))
        ~footer:"end"
        [Term.to_indentation_tree body]
    | Ap [] -> assert false
    | Ap (funct :: args) ->
      node ~header:(flatten (Term.to_indentation_tree funct))
        (List.map args ~f:Term.to_indentation_tree)
    | Record fields ->
      node ~header:"{" ~footer:"}"
        (List.map fields ~f:(fun (field_name, term) ->
           node ~header:(sprintf "; %s =" field_name)
             [Term.to_indentation_tree term]))
    | Match (term, cases) ->
      node
        ~header:(
          sprintf !"match %s with"
            (flatten (Term.to_indentation_tree term)))
        ~footer:"end"
        ~indentation_amount:0
        (List.map cases ~f:(fun (pat, term) ->
           node
             ~header:(sprintf !"| %s =>" (flatten (Pat.to_indentation_tree pat)))
             [Term.to_indentation_tree term]))
    | Number n -> singleton (Int64.to_string n)
    | String s -> singleton (sprintf !"\"%s\"" (String.escaped s))
    | Built_in (name, typ) ->
      singleton
        (sprintf "built-in \"%s\" : %s"
           (String.escaped name)
           (flatten (Typ.to_indentation_tree typ)))
    | Let (l, term) ->
      node ~header:"let" ~footer:"end"
        (List.map l ~f:Defn.to_indentation_tree
         @ [ singleton "in"; Term.to_indentation_tree term ])
    | Ascribe (term, typ) ->
      singleton
        (sprintf !"(%s : %s)"
           (flatten (Term.to_indentation_tree term))
           (flatten (Typ.to_indentation_tree typ)))
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Defn : sig
  type untagged =
    | InfixTyp of string
    | InfixTerm of string
    | TypAlias of (string * string list * Typ.t)
    | SumTyp of (string * string list * (string * Typ.t option) list)
    | Tag of (string * (Typ.t * Typ.t option) option * Tag.t)
    | Val of (Pat.t * Term.t)
    | Fun of (string * Pat.t list * Typ.t option * Term.t)
    | Sigture of (string * Sigture.t)
    | Modl of (string * (string * Sigture.t) option * Sigture.t option * Modl.t)
    | Include of Modl.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | InfixTyp of string
    | InfixTerm of string
    | TypAlias of (string * string list * Typ.t)
    | SumTyp of (string * string list * (string * Typ.t option) list)
    | Tag of (string * (Typ.t * Typ.t option) option * Tag.t)
    | Val of (Pat.t * Term.t)
    | Fun of (string * Pat.t list * Typ.t option * Term.t)
    | Sigture of (string * Sigture.t)
    | Modl of (string * (string * Sigture.t) option * Sigture.t option * Modl.t)
    | Include of Modl.t
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  (* CR wduff: Avoid [to_string] calls *)
  let to_indentation_tree (t : t) =
    match t.without_positions with
    | InfixTyp name -> node ~header:"infix type" [singleton name]
    | InfixTerm name -> node ~header:"infix" [singleton name]
    | TypAlias (name, args, typ) ->
      node
        ~header:(
          sprintf "type %s%s ="
            name
            (if List.is_empty args
             then ""
             else " " ^ String.concat ~sep:" " args))
        [Typ.to_indentation_tree typ]
    | SumTyp (name, args, cases) ->
      node
        ~header:(
          sprintf "type %s%s ="
            name
            (if List.is_empty args
             then ""
             else " " ^ String.concat ~sep:" " args))
        (List.map cases ~f:(fun (name, typ_opt) ->
           let (string2, sub_trees) =
             match typ_opt with
             | None -> ("", [])
             | Some typ -> (" of", [Typ.to_indentation_tree typ])
           in
           node ~header:(sprintf "| %s%s" name string2) sub_trees))
    | Tag (name, typs_opt, tag) ->
      node
        ~header:(
          sprintf "pat %s%s ="
            name
            (match typs_opt with
             | None -> ""
             | Some (typ1, typ2_opt) ->
               sprintf !" : %s%s"
                 (flatten (Typ.to_indentation_tree typ1))
                 (match typ2_opt with
                  | None -> ""
                  | Some typ2 ->
                    sprintf !" => %s" (flatten (Typ.to_indentation_tree typ2)))))
        [Tag.to_indentation_tree tag]
    | Val (pat, term) ->
      node ~header:(sprintf "val %s =" (flatten (Pat.to_indentation_tree pat)))
        [Term.to_indentation_tree term]
    | Fun (name, args, typ_opt, body) ->
      node
        ~header:(
          sprintf "fun %s%s%s ="
            name
            (if List.is_empty args
             then ""
             else begin
               " "
               ^ String.concat ~sep:" "
                   (List.map args ~f:(fun pat ->
                      flatten (Pat.to_indentation_tree pat)))
             end)
            (match typ_opt with
             | None -> ""
             | Some typ ->
               sprintf " : %s" (flatten (Typ.to_indentation_tree typ))))
        [Term.to_indentation_tree body]
    | Sigture (name, sigture) ->
      node ~header:(sprintf "signature %s =" name)
        [Sigture.to_indentation_tree sigture]
    | Modl (name, arg_opt, sigture_opt, body) ->
      node
        ~header:(
          sprintf "module %s%s%s ="
            name
            (match arg_opt with
             | None -> ""
             | Some (arg_name, arg_sigture) ->
               sprintf !" (%s : %s)"
                 arg_name
                 (flatten (Sigture.to_indentation_tree arg_sigture)))
            (match sigture_opt with
             | None -> ""
             | Some sigture ->
               sprintf !" : %s" (
                 flatten (Sigture.to_indentation_tree sigture))))
        [Modl.to_indentation_tree body]
    | Include modl ->
      node ~header:"include" [Modl.to_indentation_tree modl]
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end

and Modl : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string) (* ??? only for modl vars for now *)
    | Ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t) (* ??? not yet in parser *)
    | Body of Defn.t list

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_indentation_tree : t -> Indentation_tree.t
  val to_string : t -> string
end = struct
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t)
    | Body of Defn.t list
  [@@deriving sexp_of]

  type t = untagged With_positions.t [@@deriving sexp_of]

  let to_indentation_tree (t : t) =
    match t.without_positions with
    | Var (_, name) -> singleton name
    | Modl_proj (modl, name) ->
      singleton (sprintf "%s.%s" (flatten (Modl.to_indentation_tree modl)) name)
    | Ap (modl1, modl2) ->
      node ~header:(flatten (Modl.to_indentation_tree modl1)) [Modl.to_indentation_tree modl2]
    | Ascribe (modl, sigture) ->
      singleton
        (sprintf !"(%s : %s)"
           (flatten (Modl.to_indentation_tree modl))
           (flatten (Sigture.to_indentation_tree sigture)))
    | Body l ->
      node ~header:"mod" ~footer:"end"
        (List.map l ~f:(Defn.to_indentation_tree))
  ;;

  let to_string t =
    Indentation_tree.to_string (to_indentation_tree t)
  ;;
end
