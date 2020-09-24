open! Core
open! Abbot_runtime
module String_map = String.Map

type ('a, 'b) bind = 'a * 'b [@@deriving sexp_of]

module rec Kind : sig
  type oper
  type t = oper With_renaming.t [@@deriving sexp_of]

  type view =
    | Typ
    | Sing of Typ.t
    | Arrow of (Typ.Var.t * Kind.t, Kind.t) bind
  [@@deriving sexp_of]

  val typ : unit -> t
  val sing : Typ.t -> t
  val arrow : (Typ.Var.t * Kind.t, Kind.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | Typ
    | Sing of Typ.t
    | Arrow of (string compare_ignore * Kind.t, Kind.t) bind

  type t = oper With_renaming.t

  type view =
    | Typ
    | Sing of Typ.t
    | Arrow of (Typ.Var.t * Kind.t, Kind.t) bind
  [@@deriving sexp_of]

  let into (view : view) : t =
    let (oper : oper) =
      match view with
      | Typ -> Typ
      | Sing typ1 -> Sing typ1
      | Arrow ((typ_var1, kind1), kind2) ->
        Arrow
          ((Typ.Var.name typ_var1, kind1),
           With_renaming.apply_renaming (Renaming.bind typ_var1) kind2)
    in
    (Renaming.ident, oper)

  let out (renaming, oper) : view =
    match (oper : oper) with
    | Typ -> Typ
    | Sing typ1 -> Sing (Internal_sort.apply_renaming renaming typ1)
    | Arrow ((bound_typ_name1, kind1), kind2) ->
      let typ_var1 = Typ.Var.create bound_typ_name1 in
      Arrow
        ((typ_var1, With_renaming.apply_renaming renaming kind1),
         With_renaming.apply_renaming (Renaming.compose renaming (Renaming.unbind typ_var1)) kind2)

  let typ () = into Typ
  let sing arg = into (Sing arg)
  let arrow arg = into (Arrow arg)

  let sexp_of_t t =
    [%sexp_of: view] (out t)

  let subst sort value var t =
    match out t with
    | Typ -> typ ()
    | Sing typ -> sing (Typ.subst sort value var typ)
    | Arrow ((typ_var, kind1), kind2) ->
      arrow
        ((typ_var, Kind.subst sort value var kind1),
         Kind.subst sort value var kind2)
end

and Typ : sig
  type oper
  type t = oper Internal_sort.t [@@deriving sexp_of]
  module Var = Temp

  (* [unification_node] and [unification_var] are exposed
     only for use by [Type_checker.Unification]. *)
  type 'a unification_node =
    | Tip of int
    | Node of 'a

  type 'a unification_var = int * 'a unification_node ref

  type view =
    | Var of Var.t
    | UVar of Typ.t unification_var
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Var.t * Kind.t) * Typ.t)
    | Ap of (Typ.t * Typ.t)
    | Arrow of (Typ.t * Typ.t)
    | Forall of ((Var.t * Kind.t) * Typ.t)
    | Record of Typ.t String_map.t
    | Sum of Typ.t list
    | Number
    | Char
    | String
  [@@deriving sexp_of]

  val var : Typ.Var.t -> t
  val uvar : Typ.t unification_var -> t
  val modl_proj : Modl.t * string -> t
  val fun_ : (Typ.Var.t * Kind.t, Typ.t) bind -> t
  val ap : Typ.t * Typ.t -> t
  val arrow : Typ.t * Typ.t -> t
  val forall : (Typ.Var.t * Kind.t, Typ.t) bind -> t
  val record : Typ.t String.Map.t -> t
  val sum : Typ.t list -> t
  val number : unit -> t
  val char : unit -> t
  val string : unit -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  module Var = Temp

  type 'a unification_node =
    | Tip of int
    | Node of 'a

  type 'a unification_var = int * 'a unification_node ref

  let sexp_of_unification_var sexp_of_a (n, var) =
    Sexplib.Sexp.List
      (Sexplib.Sexp.Atom "UVar"
       :: Sexplib.Sexp.Atom ("uvar" ^ Int.to_string n)
       :: (match !var with Tip _ -> [] | Node a -> [[%sexp_of: a] a]))

  type oper =
    (* CR wduff: Can unification variables be modeled as an external abt? *)
    | UVar of Typ.t unification_var
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((string compare_ignore * Kind.t) * Typ.t)
    | Ap of (Typ.t * Typ.t)
    | Arrow of (Typ.t * Typ.t)
    | Forall of ((string compare_ignore * Kind.t) * Typ.t)
    | Record of Typ.t String_map.t
    | Sum of Typ.t list
    | Number
    | Char
    | String

  type t = oper Internal_sort.t

  type view =
    | Var of Var.t
    | UVar of Typ.t unification_var
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Var.t * Kind.t) * Typ.t)
    | Ap of (Typ.t * Typ.t)
    | Arrow of (Typ.t * Typ.t)
    | Forall of ((Var.t * Kind.t) * Typ.t)
    | Record of Typ.t String_map.t
    | Sum of Typ.t list
    | Number
    | Char
    | String
  [@@deriving sexp_of]

  let into (view : view) : t =
    match view with
    | Var typ_var -> Var (Free_var typ_var)
    | UVar uvar -> Oper (Renaming.ident, UVar uvar)
    | Modl_proj (modl, string) -> Oper (Renaming.ident, Modl_proj (modl, string))
    | Fun ((typ_var, kind), typ) ->
      Oper
        (Renaming.ident,
         Fun
           ((Typ.Var.name typ_var, kind),
            Internal_sort.apply_renaming (Renaming.bind typ_var) typ))
    | Ap (typ1, typ2) -> Oper (Renaming.ident, Ap (typ1, typ2))
    | Arrow (typ1, typ2) -> Oper (Renaming.ident, Arrow (typ1, typ2))
    | Forall ((typ_var, kind), typ) ->
      Oper
        (Renaming.ident,
         Forall
           ((Typ.Var.name typ_var, kind),
            Internal_sort.apply_renaming (Renaming.bind typ_var) typ))
    | Record fields -> Oper (Renaming.ident, Record fields)
    | Sum typs -> Oper (Renaming.ident, Sum typs)
    | Number -> Oper (Renaming.ident, Number)
    | Char -> Oper (Renaming.ident, Char)
    | String -> Oper (Renaming.ident, String)

  let out (t : t) : view =
    match t with
    | Var (Bound_var _) -> raise_s [%message "Internal Abbot error."]
    | Var (Free_var var) -> Var var
    | Oper (renaming, oper) ->
      match oper with
      | UVar (n, var) ->
        (* CR wduff: This is dubious. What if we unify with a term that has an outstanding
           renaming, then push the renaming inside thus incorrectly applying the renaming to the
           type the uvar was unified with. *)
        begin
          match !var with
          | Tip _ -> UVar (n, var)
          | Node typ ->
            (* CR wduff: This needs a new unique id, or better yet, this shouldn't be a uvar. *)
            UVar (n, ref (Node (Internal_sort.apply_renaming renaming typ)))
        end
      | Modl_proj (modl, string) -> Modl_proj (Internal_sort.apply_renaming renaming modl, string)
      | Fun ((bound_typ_name, kind), typ) ->
        let typ_var = Typ.Var.create bound_typ_name in
        Fun
          ((typ_var, With_renaming.apply_renaming renaming kind),
           Internal_sort.apply_renaming (Renaming.compose renaming (Renaming.unbind typ_var)) typ)
      | Ap (typ1, typ2) -> Ap (Internal_sort.apply_renaming renaming typ1, Internal_sort.apply_renaming renaming typ2)
      | Arrow (typ1, typ2) -> Arrow (Internal_sort.apply_renaming renaming typ1, Internal_sort.apply_renaming renaming typ2)
      | Forall ((bound_typ_name, kind), typ) ->
        let typ_var = Typ.Var.create bound_typ_name in
        Forall
          ((typ_var, With_renaming.apply_renaming renaming kind),
           Internal_sort.apply_renaming (Renaming.compose renaming (Renaming.unbind typ_var)) typ)
      | Record fields ->
        Record (Map.map fields ~f:(Internal_sort.apply_renaming renaming))
      | Sum typs -> Sum (List.map typs ~f:(Internal_sort.apply_renaming renaming))
      | Number -> Number
      | Char -> Char
      | String -> String

  let sexp_of_t t =
    [%sexp_of: view] (out t)

  let var arg = into (Var arg)
  let uvar arg = into (UVar arg)
  let modl_proj arg = into (Modl_proj arg)
  let fun_ arg = into (Fun arg)
  let ap arg = into (Ap arg)
  let arrow arg = into (Arrow arg)
  let forall arg = into (Forall arg)
  let record arg = into (Record arg)
  let sum arg = into (Sum arg)
  let number () = into Number
  let char () = into Char
  let string () = into String

  let subst
        (type var)
        (type sort)
        (sort : (var, sort) Sort.t)
        (value : sort)
        (var : var)
        (t : t)
    : t =
    let view = out t in
    let view' =
      match view with
      | Var var' ->
        (match sort with
         | Sort.Typ ->
           if Temp.equal var var'
           then Typ.out value
           else Var var'
         | _ ->
           Var var')
      | UVar (n, uvar) ->
        begin
          match !uvar with
          | Tip _ -> UVar (n, uvar)
          | Node typ -> Typ.out (Typ.subst sort value var typ)
        end
      | Modl_proj (modl, string) ->
        Modl_proj (Modl.subst sort value var modl, string)
      | Fun ((typ_var, kind), typ) ->
        Fun
          ((typ_var, Kind.subst sort value var kind),
           Typ.subst sort value var typ)
      | Ap (typ1, typ2) ->
        Ap (Typ.subst sort value var typ1, Typ.subst sort value var typ2)
      | Arrow (typ1, typ2) ->
        Arrow (Typ.subst sort value var typ1, Typ.subst sort value var typ2)
      | Forall ((typ_var, kind), typ) ->
        Forall
          ((typ_var, Kind.subst sort value var kind),
           Typ.subst sort value var typ)
      | Record fields ->
        Record (String_map.map fields ~f:(Typ.subst sort value var))
      | Sum typs ->
        Sum (List.map typs ~f:(Typ.subst sort value var))
      | Number -> Number
      | Char -> Char
      | String -> String
    in
    into view'
end

and Decl : sig
  type oper
  type internal = oper With_renaming.t

  type t =
    | Typ of (Typ.Var.t * Kind.t)
    | Tag of (Typ.t * Typ.t Option.t)
    | Val of Typ.t
    | Modl of (Modl.Var.t * Sigture.t)
  [@@deriving sexp_of]

  val into : t -> internal * Temp.t list
  val out : internal -> t * Temp.t list

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | Typ of (string compare_ignore * Kind.t)
    | Tag of (Typ.t * Typ.t Option.t)
    | Val of Typ.t
    | Modl of (string compare_ignore * Sigture.t)

  type internal = oper With_renaming.t

  type t =
    | Typ of (Typ.Var.t * Kind.t)
    | Tag of (Typ.t * Typ.t Option.t)
    | Val of Typ.t
    | Modl of (Modl.Var.t * Sigture.t)
  [@@deriving sexp_of]

  let into (t : t) =
    let ((oper : oper), vars) =
      match t with
      | Typ (typ_var, kind) ->
        (Typ (Typ.Var.name typ_var, kind), [typ_var])
      | Tag (typ1, typ2_opt) ->
        (Tag (typ1, typ2_opt), [])
      | Val typ ->
        (Val typ, [])
      | Modl (modl_var, sigture) ->
        (Modl (Modl.Var.name modl_var, sigture), [modl_var])
    in
    ((Renaming.ident, oper), vars)

  let out (renaming, oper) : t * Temp.t list =
    match (oper : oper) with
    | Typ (bound_typ_name, kind) ->
      let typ_var = Typ.Var.create bound_typ_name in
      (Typ (typ_var, With_renaming.apply_renaming renaming kind), [typ_var])
    | Tag (typ1, typ2_opt) ->
      (Tag (Internal_sort.apply_renaming renaming typ1, Option.map typ2_opt ~f:(Internal_sort.apply_renaming renaming)), [])
    | Val typ ->
      (Val (Internal_sort.apply_renaming renaming typ), [])
    | Modl (bound_modl_name, sigture) ->
      let modl_var = Modl.Var.create bound_modl_name in
      (Modl (modl_var, With_renaming.apply_renaming renaming sigture), [modl_var])

  let subst sort value var t =
    match t with
    | Typ (typ_var, kind) ->
      Typ (typ_var, Kind.subst sort value var kind)
    | Tag (typ1, typ2_opt) ->
      Tag
        (Typ.subst sort value var typ1,
         Option.map typ2_opt ~f:(Typ.subst sort value var))
    | Val typ ->
      Val (Typ.subst sort value var typ)
    | Modl (modl_var, sigture) ->
      Modl (modl_var, Sigture.subst sort value var sigture)
end

and Decls : sig
  type oper
  type t = oper With_renaming.t [@@deriving sexp_of]

  type view =
    | End
    | Cons of ((String.t * Decl.t) * Decls.t)
  [@@deriving sexp_of]

  val end_ : unit -> t
  val cons : ((String.t * Decl.t), Decls.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | End
    | Cons of ((String.t * Decl.internal) * Decls.t)

  type t = oper With_renaming.t

  type view =
    | End
    | Cons of ((String.t * Decl.t) * Decls.t)

  let into (view : view) =
    let oper : oper =
      match view with
      | End -> End
      | Cons ((field_name, decl), decls) ->
        let (decl', decl_vars) = Decl.into decl in
        Cons ((field_name, decl'), With_renaming.apply_renaming (Renaming.bind' decl_vars) decls)
    in
    (Renaming.ident, oper)

  let out (renaming, oper) : view =
    match (oper : oper) with
    | End -> End
    | Cons ((field_name, decl), decls) ->
      let (decl', decl_vars) = Decl.out (With_renaming.apply_renaming renaming decl) in
      Cons
        ((field_name, decl'),
         With_renaming.apply_renaming
           (Renaming.compose renaming (Renaming.unbind' decl_vars))
           decls)

  let end_ () = into End
  let cons arg = into (Cons arg)

  let rec to_list (t : t) =
    match out t with
    | End -> []
    | Cons ((name, decl), decls) -> (name, decl) :: to_list decls

  let sexp_of_t t =
    [%sexp_of: (String.t * Decl.t) list] (to_list t)

  let sexp_of_view view = [%sexp_of: t] (into view)

  let subst sort_kind sort var t =
    match out t with
    | End -> end_ ()
    | Cons ((field_name, decl), decls) ->
      cons
        ((field_name, Decl.subst sort_kind sort var decl),
         Decls.subst sort_kind sort var decls)
end

and Sigture : sig
  type oper
  type t = oper With_renaming.t [@@deriving sexp_of]

  type view =
    | Arrow of ((Modl.Var.t * Sigture.t) * Sigture.t)
    | Proj_arrow of ((Modl.Var.t * Sigture.t) * Sigture.t)
    | Body of Decls.t
    | Rec of (Modl.Var.t * Sigture.t)
  [@@deriving sexp_of]

  val arrow : ((Modl.Var.t * Sigture.t), Sigture.t) bind -> t
  val proj_arrow : ((Modl.Var.t * Sigture.t), Sigture.t) bind -> t
  val body : Decls.t -> t
  val rec_ : (Modl.Var.t, Sigture.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | Arrow of ((string compare_ignore * Sigture.t) * Sigture.t)
    | Proj_arrow of ((string compare_ignore * Sigture.t) * Sigture.t)
    | Body of Decls.t
    | Rec of (string compare_ignore * Sigture.t)

  type t = oper With_renaming.t

  type view =
    | Arrow of ((Modl.Var.t * Sigture.t) * Sigture.t)
    | Proj_arrow of ((Modl.Var.t * Sigture.t) * Sigture.t)
    | Body of Decls.t
    | Rec of (Modl.Var.t * Sigture.t)
  [@@deriving sexp_of]

  let into (view : view) =
    let oper : oper =
      match view with
      | Arrow ((modl_var, sigture1), sigture2) ->
        Arrow
          ((Modl.Var.name modl_var, sigture1),
           With_renaming.apply_renaming (Renaming.bind modl_var) sigture2)
      | Proj_arrow ((modl_var, sigture1), sigture2) ->
        Proj_arrow
          ((Modl.Var.name modl_var, sigture1),
           With_renaming.apply_renaming (Renaming.bind modl_var) sigture2)
      | Body decls ->
        Body decls
      | Rec (modl_var, sigture) ->
        Rec (Modl.Var.name modl_var, With_renaming.apply_renaming (Renaming.bind modl_var) sigture)
    in
    (Renaming.ident, oper)

  let out (renaming, oper) : view =
    match (oper : oper) with
    | Arrow ((bound_modl_name, sigture1), sigture2) ->
      let modl_var = Modl.Var.create bound_modl_name in
      Arrow
        ((modl_var, With_renaming.apply_renaming renaming sigture1),
         With_renaming.apply_renaming
           (Renaming.compose renaming (Renaming.unbind modl_var))
           sigture2)
    | Proj_arrow ((bound_modl_name, sigture1), sigture2) ->
      let modl_var = Modl.Var.create bound_modl_name in
      Proj_arrow
        ((modl_var, With_renaming.apply_renaming renaming sigture1),
         With_renaming.apply_renaming
           (Renaming.compose renaming (Renaming.unbind modl_var))
           sigture2)
    | Body decls ->
      Body (With_renaming.apply_renaming renaming decls)
    | Rec (bound_modl_name, sigture) ->
      let modl_var = Modl.Var.create bound_modl_name in
      Rec
        (modl_var,
         With_renaming.apply_renaming
           (Renaming.compose renaming (Renaming.unbind modl_var))
           sigture)

  let arrow arg = into (Arrow arg)
  let proj_arrow arg = into (Proj_arrow arg)
  let body arg = into (Body arg)
  let rec_ arg = into (Rec arg)

  let sexp_of_t t =
    [%sexp_of: view] (out t)

  let subst sort value var (t : t) : t =
    let view = out t in
    let (view' : view) =
      match view with
      | Arrow ((modl_var, sigture1), sigture2) ->
        Arrow
          ((modl_var, Sigture.subst sort value var sigture1),
           Sigture.subst sort value var sigture2)
      | Proj_arrow ((modl_var, sigture1), sigture2) ->
        Proj_arrow
          ((modl_var, Sigture.subst sort value var sigture1),
           Sigture.subst sort value var sigture2)
      | Body decls ->
        Body (Decls.subst sort value var decls)
      | Rec (modl_var, sigture) ->
        Rec (modl_var, Sigture.subst sort value var sigture)
    in
    into view'
end

and Tag : sig
  type oper
  type t = oper Internal_sort.t [@@deriving sexp_of]
  module Var = Temp

  type view =
    | Var of Tag.Var.t
    | Modl_proj of (Modl.t * string)
    | In of (int * int)
    | Destr of Term.t
  [@@deriving sexp_of]

  val var : Tag.Var.t -> t
  val modl_proj : Modl.t * string -> t
  val in_ : int * int -> t
  val destr : Term.t -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  module Var = Temp

  type oper =
    | Modl_proj of (Modl.t * String.t)
    | In of (Int.t * Int.t)
    | Destr of Term.t

  type t = oper Internal_sort.t

  type view =
    | Var of Tag.Var.t
    | Modl_proj of (Modl.t * string)
    | In of (int * int)
    | Destr of Term.t
  [@@deriving sexp_of]

  let into (view : view) : t =
    match view with
    | Var var -> Var (Free_var var)
    | Modl_proj (modl1, string1) ->
      Oper (Renaming.ident, Modl_proj (modl1, string1))
    | In (int1, int2) ->
      Oper (Renaming.ident, In (int1, int2))
    | Destr term1 ->
      Oper (Renaming.ident, Destr term1)

  let out (t : t) : view =
    match t with
    | Var (Bound_var _) -> raise_s [%message "Internal Abbot error."]
    | Var (Free_var var) -> Var var
    | Oper (renaming, oper) ->
      match oper with
      | Modl_proj (modl1, string1) ->
        Modl_proj (Internal_sort.apply_renaming renaming modl1, string1)
      | In (int1, int2) -> In (int1, int2)
      | Destr term1 -> Destr (Internal_sort.apply_renaming renaming term1)

  let sexp_of_t t =
    [%sexp_of: view] (out t)

  let var arg = into (Var arg)
  let modl_proj arg = into (Modl_proj arg)
  let in_ arg = into (In arg)
  let destr arg = into (Destr arg)

  let subst
        (type var)
        (type sort)
        (sort : (var, sort) Sort.t)
        (value : sort)
        (var : var)
        (t : t)
    : t =
    let view = out t in
    let (view' : view) =
      match view with
      | Var var' ->
        (match sort with
         | Sort.Tag ->
           if Temp.equal var var'
           then Tag.out value
           else Var var'
         | _ ->
           Var var')
      | Modl_proj (modl, string) ->
        Modl_proj (Modl.subst sort value var modl, string)
      | In (n, i) -> In (n, i)
      | Destr term -> Destr (Term.subst sort value var term)
    in
    into view'
end

and Pat : sig
  type oper
  type internal = oper With_renaming.t

  type t =
    | Wild
    | Var of Term.Var.t
    | Record of Pat.t String_map.t
    | Tag of (Tag.t * Pat.t Option.t)
    | Number of Int64.t
    | String of String.t
    | Ascribe of (Pat.t * Typ.t)
  [@@deriving sexp_of]

  val into : t -> internal * Temp.t list
  val out : internal -> t * Temp.t list

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | Wild
    | Var of string compare_ignore
    | Record of Pat.internal String_map.t
    | Tag of (Tag.t * Pat.internal Option.t)
    | Number of Int64.t
    | String of String.t
    | Ascribe of (Pat.internal * Typ.t)

  type internal = oper With_renaming.t

  type t =
    | Wild
    | Var of Term.Var.t
    | Record of Pat.t String_map.t
    | Tag of (Tag.t * Pat.t Option.t)
    | Number of Int64.t
    | String of String.t
    | Ascribe of (Pat.t * Typ.t)
  [@@deriving sexp_of]

  let into (t : t) : internal * Temp.t list =
    let ((oper : oper), vars) =
      match t with
      | Wild -> (Wild, [])
      | Var term_var -> (Var (Term.Var.name term_var), [term_var])
      | Record fields ->
        let (fields', rev_field_vars) =
          Map.fold fields ~init:(String.Map.empty, [])
            ~f:(fun ~key:field_name ~data:pat (fields', rev_field_vars) ->
              let (pat', pat_vars) = Pat.into pat in
              (Map.set fields' ~key:field_name ~data:pat',
               List.rev_append pat_vars rev_field_vars))
        in
        (Record fields', List.rev rev_field_vars)
      | Tag (tag, pat_opt) ->
        let (pat_opt', pat_opt_vars) =
          match pat_opt with
          | None -> (None, [])
          | Some pat ->
            let (pat', pat_vars) = Pat.into pat in
            (Some pat', pat_vars)
        in
        (Tag (tag, pat_opt'), pat_opt_vars)
      | Number n -> (Number n, [])
      | String string -> (String string, [])
      | Ascribe (pat, typ) ->
        let (pat', pat_vars) = Pat.into pat in
        (Ascribe (pat', typ), pat_vars)
    in
    ((Renaming.ident, oper), vars)

  let out (renaming, oper) : t * Temp.t list =
    match (oper : oper) with
    | Wild -> (Wild, [])
    | Var bound_term_name ->
      let term_var = Term.Var.create bound_term_name in
      (Var term_var, [term_var])
    | Record fields ->
      let (fields', rev_field_vars) =
        Map.fold fields ~init:(String.Map.empty, [])
          ~f:(fun ~key:field_name ~data:pat (fields', rev_field_vars) ->
            let (pat', pat_vars) = Pat.out (With_renaming.apply_renaming renaming pat) in
            (Map.set fields' ~key:field_name ~data:pat',
             List.rev_append pat_vars rev_field_vars))
      in
      (Record fields', List.rev rev_field_vars)
    | Tag (tag, pat_opt) ->
      let (pat_opt', pat_opt_vars) =
        match pat_opt with
        | None -> (None, [])
        | Some pat ->
          let (pat', pat_vars) = Pat.out (With_renaming.apply_renaming renaming pat) in
          (Some pat', pat_vars)
      in
      (Tag (Internal_sort.apply_renaming renaming tag, pat_opt'), pat_opt_vars)
    | Number n -> (Number n, [])
    | String string -> (String string, [])
    | Ascribe (pat, typ) ->
      let (pat', pat_vars) = Pat.out (With_renaming.apply_renaming renaming pat) in
      (Ascribe (pat', Internal_sort.apply_renaming renaming typ), pat_vars)

  let subst sort value var t =
    match t with
    | Wild -> Wild
    | Var term_var -> Var term_var
    | Record fields ->
      Record (String_map.map fields ~f:(Pat.subst sort value var))
    | Tag (tag, pat_opt) ->
      Tag
        (Tag.subst sort value var tag,
         Option.map pat_opt ~f:(Pat.subst sort value var))
    | Number n -> Number n
    | String string -> String string
    | Ascribe (pat, typ) ->
      Ascribe (Pat.subst sort value var pat, Typ.subst sort value var typ)
end

and Term : sig
  type oper
  type t = oper Internal_sort.t [@@deriving sexp_of]
  module Var = Temp

  type view =
    | Var of Var.t
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Pat.t list * Typ.t Option.t) * Term.t)
    | Typ_fun of ((Typ.Var.t * Kind.t) * Term.t)
    | Ap of (Term.t * Term.t)
    | Typ_ap of (Term.t * Typ.t)
    | Record of Term.t String_map.t
    | In of (Int.t * Int.t * Term.t)
    | Match of (Term.t * (Pat.t * Term.t) list)
    | Number of Int64.t
    | Char of Char.t
    | String of String.t
    | Built_in of (String.t * Typ.t)
    | Let of (Defn.t * Term.t)
    | Ascribe of (Term.t * Typ.t)
  [@@deriving sexp_of]

  val var : Term.Var.t -> t
  val modl_proj : Modl.t * string -> t
  val fun_ : (Pat.t list * Typ.t option, Term.t) bind -> t
  val typ_fun : (Typ.Var.t * Kind.t, Term.t) bind -> t
  val ap : Term.t * Term.t -> t
  val typ_ap : Term.t * Typ.t -> t
  val record : Term.t String.Map.t -> t
  val in_ : int * int * Term.t -> t
  val match_ : Term.t * (Pat.t, Term.t) bind list -> t
  val number : Int64.t -> t
  val char : char -> t
  val string : string -> t
  val built_in : string * Typ.t -> t
  val let_ : (Defn.t, Term.t) bind -> t
  val ascribe : Term.t * Typ.t -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  module Var = Temp

  type oper =
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Pat.internal list * Typ.t Option.t) * Term.t)
    | Typ_fun of ((string compare_ignore * Kind.t) * Term.t)
    | Ap of (Term.t * Term.t)
    | Typ_ap of (Term.t * Typ.t)
    | Record of Term.t String_map.t
    | In of (Int.t * Int.t * Term.t)
    | Match of (Term.t * (Pat.internal * Term.t) list)
    | Number of Int64.t
    | Char of Char.t
    | String of String.t
    | Built_in of (String.t * Typ.t)
    | Let of (Defn.internal * Term.t)
    | Ascribe of (Term.t * Typ.t)

  type t = oper Internal_sort.t

  type view =
    | Var of Var.t
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Pat.t list * Typ.t Option.t) * Term.t)
    | Typ_fun of ((Typ.Var.t * Kind.t) * Term.t)
    | Ap of (Term.t * Term.t)
    | Typ_ap of (Term.t * Typ.t)
    | Record of Term.t String_map.t
    | In of (Int.t * Int.t * Term.t)
    | Match of (Term.t * (Pat.t * Term.t) list)
    | Number of Int64.t
    | Char of Char.t
    | String of String.t
    | Built_in of (String.t * Typ.t)
    | Let of (Defn.t * Term.t)
    | Ascribe of (Term.t * Typ.t)
  [@@deriving sexp_of]

  let into (view : view) : t =
    match view with
    | Var term_var -> Var (Free_var term_var)
    | Modl_proj (modl, string) -> Oper (Renaming.ident, Modl_proj (modl, string))
    | Fun ((args, typ_opt), body) ->
      let (rev_args', rev_arg_vars) =
        List.fold args ~init:([], []) ~f:(fun (rev_args, rev_arg_vars) pat ->
          let (pat', pat_vars) = Pat.into pat in
          (pat' :: rev_args, List.rev_append pat_vars rev_arg_vars))
      in
      let body' = Internal_sort.apply_renaming (Renaming.bind' (List.rev rev_arg_vars)) body in
      Oper (Renaming.ident, Fun ((List.rev rev_args', typ_opt), body'))
    | Typ_fun ((arg_var, kind), body) ->
      let body' = Internal_sort.apply_renaming (Renaming.bind arg_var) body in
      Oper (Renaming.ident, Typ_fun ((Typ.Var.name arg_var, kind), body'))
    | Ap (term1, term2) -> Oper (Renaming.ident, Ap (term1, term2))
    | Typ_ap (term, typ) -> Oper (Renaming.ident, Typ_ap (term, typ))
    | Record fields -> Oper (Renaming.ident, Record fields)
    | In (n, i, term) -> Oper (Renaming.ident, In (n, i, term))
    | Match (term, cases) ->
      Oper
        (Renaming.ident,
         Match
           (term,
            List.map cases ~f:(fun (pat, term) ->
              let (pat', pat_vars) = Pat.into pat in
              let term' = Internal_sort.apply_renaming (Renaming.bind' pat_vars) term in
              (pat', term'))))
    | Number n -> Oper (Renaming.ident, Number n)
    | Char c -> Oper (Renaming.ident, Char c)
    | String string -> Oper (Renaming.ident, String string)
    | Built_in (string, typ) -> Oper (Renaming.ident, Built_in (string, typ))
    | Let (defn, term) ->
      let (defn', defn_vars) = Defn.into defn in
      let term' = Internal_sort.apply_renaming (Renaming.bind' defn_vars) term in
      Oper (Renaming.ident, Let (defn', term'))
    | Ascribe (term, typ) -> Oper (Renaming.ident, Ascribe (term, typ))

  let out (t : t) : view =
    match t with
    | Var (Bound_var _) -> raise_s [%message "Internal Abbot error."]
    | Var (Free_var var) -> Var var
    | Oper (renaming, oper) ->
      match oper with
      | Modl_proj (modl, string) ->
        Modl_proj (Internal_sort.apply_renaming renaming modl, string)
      | Fun ((args, typ_opt), body) ->
        let (rev_args', rev_arg_vars) =
          List.fold args ~init:([], []) ~f:(fun (rev_args, rev_arg_vars) pat ->
            let (pat', pat_vars) = Pat.out (With_renaming.apply_renaming renaming pat) in
            (pat' :: rev_args, List.rev_append pat_vars rev_arg_vars))
        in
        let body' =
          Internal_sort.apply_renaming
            (Renaming.compose renaming (Renaming.unbind' (List.rev rev_arg_vars)))
            body
        in
        Fun
          ((List.rev rev_args', Option.map typ_opt ~f:(Internal_sort.apply_renaming renaming)),
           body')
      | Typ_fun ((arg_name, kind), body) ->
        let arg_var = Typ.Var.create arg_name in
        Typ_fun
          ((arg_var, With_renaming.apply_renaming renaming kind),
           Internal_sort.apply_renaming (Renaming.compose renaming (Renaming.unbind arg_var)) body)
      | Ap (term1, term2) ->
        Ap
          (Internal_sort.apply_renaming renaming term1,
           Internal_sort.apply_renaming renaming term2)
      | Typ_ap (term, typ) ->
        Typ_ap
          (Internal_sort.apply_renaming renaming term,
           Internal_sort.apply_renaming renaming typ)
      | Record fields ->
        Record (Map.map fields ~f:(Internal_sort.apply_renaming renaming))
      | In (n, i, term) ->
        In (n, i, Internal_sort.apply_renaming renaming term)
      | Match (term, cases) ->
        Match
          (Internal_sort.apply_renaming renaming term,
           List.map cases ~f:(fun (pat, term) ->
             let (pat', pat_vars) = Pat.out (With_renaming.apply_renaming renaming pat) in
             (pat',
              Internal_sort.apply_renaming
                (Renaming.compose renaming (Renaming.unbind' pat_vars))
                term)))
      | Number n ->
        Number n
      | Char c ->
        Char c
      | String string ->
        String string
      | Built_in (string, typ) ->
        Built_in (string, Internal_sort.apply_renaming renaming typ)
      | Let (defn, term) ->
        let (defn', defn_vars) = Defn.out (With_renaming.apply_renaming renaming defn) in
        Let
          (defn',
           Internal_sort.apply_renaming
             (Renaming.compose renaming (Renaming.unbind' defn_vars))
             term)
      | Ascribe (term, typ) ->
        Ascribe (Internal_sort.apply_renaming renaming term, Internal_sort.apply_renaming renaming typ)

  let sexp_of_t t =
    [%sexp_of: view] (out t)

  let var arg = into (Var arg)
  let modl_proj arg = into (Modl_proj arg)
  let fun_ arg = into (Fun arg)
  let typ_fun arg = into (Typ_fun arg)
  let ap arg = into (Ap arg)
  let typ_ap arg = into (Typ_ap arg)
  let record arg = into (Record arg)
  let in_ arg = into (In arg)
  let match_ arg = into (Match arg)
  let number arg = into (Number arg)
  let char arg = into (Char arg)
  let string arg = into (String arg)
  let built_in arg = into (Built_in arg)
  let let_ arg = into (Let arg)
  let ascribe arg = into (Ascribe arg)

  let subst
        (type var)
        (type sort)
        (sort : (var, sort) Sort.t)
        (value : sort)
        (var : var)
        (t : t)
    : t =
    let view = out t in
    let view' =
      match view with
      | Var var' ->
        (match sort with
         | Sort.Term ->
           if Temp.equal var var'
           then Term.out value
           else Var var'
         | _ ->
           Var var')
      | Modl_proj (modl, string) ->
        Modl_proj (Modl.subst sort value var modl, string)
      | Fun ((args, typ_opt), body) ->
        Fun
          ((List.map args ~f:(Pat.subst sort value var),
            Option.map typ_opt ~f:(Typ.subst sort value var)),
           Term.subst sort value var body)
      | Typ_fun ((arg_var, kind), body) ->
        Typ_fun
          ((arg_var, Kind.subst sort value var kind),
           Term.subst sort value var body)
      | Ap (term1, term2) ->
        Ap
          (Term.subst sort value var term1,
           Term.subst sort value var term2)
      | Typ_ap (term, typ) ->
        Typ_ap
          (Term.subst sort value var term,
           Typ.subst sort value var typ)
      | Record fields ->
        Record (String_map.map fields ~f:(Term.subst sort value var))
      | In (n, i, term) ->
        In (n, i, Term.subst sort value var term)
      | Match (term, cases) ->
        Match
          (Term.subst sort value var term,
           List.map cases ~f:(fun (pat, term) ->
             (Pat.subst sort value var pat,
              Term.subst sort value var term)))
      | Number n ->
        Number n
      | Char c ->
        Char c
      | String string ->
        String string
      | Built_in (string, typ) ->
        Built_in (string, Typ.subst sort value var typ)
      | Let (defn, term) ->
        Let (Defn.subst sort value var defn, Term.subst sort value var term)
      | Ascribe (term, typ) ->
        Ascribe
          (Term.subst sort value var term,
           Typ.subst sort value var typ)
    in
    into view'
end

and Defn : sig
  type oper
  type internal = oper With_renaming.t

  type t =
    | Typ of (Typ.Var.t * Typ.t)
    | Tag of (Tag.Var.t * Tag.t)
    | Val of (Term.Var.t * Term.t)
    | Modl of (Modl.Var.t * Modl.t)
  [@@deriving sexp_of]

  val into : t -> internal * Temp.t list
  val out : internal -> t * Temp.t list

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | Typ of (string compare_ignore * Typ.t)
    | Tag of (string compare_ignore * Tag.t)
    | Val of (string compare_ignore * Term.t)
    | Modl of (string compare_ignore * Modl.t)

  type internal = oper With_renaming.t

  type t =
    | Typ of (Typ.Var.t * Typ.t)
    | Tag of (Tag.Var.t * Tag.t)
    | Val of (Term.Var.t * Term.t)
    | Modl of (Modl.Var.t * Modl.t)
  [@@deriving sexp_of]

  let into (t : t) : internal * Temp.t list =
    let ((oper : oper), vars) =
      match t with
      | Typ (typ_var, typ) ->
        (Typ (Typ.Var.name typ_var, typ), [typ_var])
      | Tag (tag_var, tag) ->
        (Tag (Typ.Var.name tag_var, tag), [tag_var])
      | Val (term_var, term) ->
        (Val (Term.Var.name term_var, term), [term_var])
      | Modl (modl_var, modl) ->
        (Modl (Typ.Var.name modl_var, modl), [modl_var])
    in
    ((Renaming.ident, oper), vars)

  let out (renaming, oper) : t * Temp.t list =
    match (oper : oper) with
    | Typ (bound_typ_name, typ) ->
      let typ_var = Typ.Var.create bound_typ_name in
      (Typ (typ_var, Internal_sort.apply_renaming renaming typ), [typ_var])
    | Tag (bound_tag_name, tag) ->
      let tag_var = Tag.Var.create bound_tag_name in
      (Tag (tag_var, Internal_sort.apply_renaming renaming tag), [tag_var])
    | Val (bound_term_name, term) ->
      let term_var = Term.Var.create bound_term_name in
      (Val (term_var, Internal_sort.apply_renaming renaming term), [term_var])
    | Modl (bound_modl_name, modl) ->
      let modl_var = Modl.Var.create bound_modl_name in
      (Modl (modl_var, Internal_sort.apply_renaming renaming modl), [modl_var])

  let subst sort value var t =
    match t with
    | Typ (typ_var, typ) ->
      Typ (typ_var, Typ.subst sort value var typ)
    | Tag (tag_var, tag) ->
      Tag (tag_var, Tag.subst sort value var tag)
    | Val (term_var, term) ->
      Val (term_var, Term.subst sort value var term)
    | Modl (modl_var, modl) ->
      Modl (modl_var, Modl.subst sort value var modl)
end

and Defns : sig
  type oper
  type t = oper With_renaming.t [@@deriving sexp_of]

  type view =
    | End
    | Cons of ((String.t * Defn.t) * Defns.t)
  [@@deriving sexp_of]

  val end_ : unit -> t
  val cons : ((String.t * Defn.t), Defns.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | End
    | Cons of ((String.t * Defn.internal) * Defns.t)

  type t = oper With_renaming.t

  type view =
    | End
    | Cons of ((String.t * Defn.t) * Defns.t)

  let into (view : view) =
    let oper : oper =
      match view with
      | End -> End
      | Cons ((field_name, defn), defns) ->
        let (defn', defn_vars) = Defn.into defn in
        Cons ((field_name, defn'), With_renaming.apply_renaming (Renaming.bind' defn_vars) defns)
    in
    (Renaming.ident, oper)

  let out (renaming, oper) : view =
    match (oper : oper) with
    | End -> End
    | Cons ((field_name, defn), defns) ->
      let (defn', defn_vars) = Defn.out (With_renaming.apply_renaming renaming defn) in
      Cons
        ((field_name, defn'),
         With_renaming.apply_renaming
           (Renaming.compose renaming (Renaming.unbind' defn_vars))
           defns)

  let end_ () = into End
  let cons arg = into (Cons arg)

  let rec to_list (t : t) =
    match out t with
    | End -> []
    | Cons ((name, defn), defns) -> (name, defn) :: to_list defns

  let sexp_of_t t =
    [%sexp_of: (String.t * Defn.t) list] (to_list t)

  let sexp_of_view view = [%sexp_of: t] (into view)

  let subst sort_kind sort var t =
    match out t with
    | End -> end_ ()
    | Cons ((field_name, defn), defns) ->
      cons
        ((field_name, Defn.subst sort_kind sort var defn),
         Defns.subst sort_kind sort var defns)
end

and Modl_field : sig
  type oper
  type internal = oper With_renaming.t

  type t =
    | Typ of Typ.t
    | Tag of Tag.t
    | Val of Term.t
    | Modl of Modl.t
  [@@deriving sexp_of]

  val into : t -> internal * Temp.t list
  val out : internal -> t * Temp.t list

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  type oper =
    | Typ of Typ.t
    | Tag of Tag.t
    | Val of Term.t
    | Modl of Modl.t
  [@@deriving sexp_of]

  type internal = oper With_renaming.t

  type t =
    | Typ of Typ.t
    | Tag of Tag.t
    | Val of Term.t
    | Modl of Modl.t
  [@@deriving sexp_of]

  let into (t : t) =
    let (oper : oper) =
      match t with
      | Typ typ -> Typ typ
      | Tag tag -> Tag tag
      | Val term -> Val term
      | Modl modl -> Modl modl
    in
    ((Renaming.ident, oper), [])

  let out (renaming, oper) : t * Temp.t list =
      match (oper : oper) with
      | Typ typ -> (Typ (Internal_sort.apply_renaming renaming typ), [])
      | Tag tag -> (Tag (Internal_sort.apply_renaming renaming tag), [])
      | Val term -> (Val (Internal_sort.apply_renaming renaming term), [])
      | Modl modl -> (Modl (Internal_sort.apply_renaming renaming modl), [])

  let subst sort value var t =
    match t with
    | Typ typ1 -> Typ (Typ.subst sort value var typ1)
    | Tag tag1 -> Tag (Tag.subst sort value var tag1)
    | Val term1 -> Val (Term.subst sort value var term1)
    | Modl modl1 -> Modl (Modl.subst sort value var modl1)
end

and Modl : sig
  type oper
  type t = oper Internal_sort.t [@@deriving sexp_of]
  module Var = Temp

  type view =
    | Var of Var.t
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Modl.Var.t * Sigture.t) * Modl.t)
    | Proj_fun of ((Modl.Var.t * Sigture.t) * Modl.t)
    | Ap of (Modl.t * Modl.t)
    | Proj_ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t)
    | Rec of ((Modl.Var.t * Sigture.t) * Modl.t)
    | Body of ((String.t * Modl_field.t) list)
    | Dep_body of Defns.t
    | Let of (Defn.t * Modl.t)
  [@@deriving sexp_of]

  val var : Modl.Var.t -> t
  val modl_proj : Modl.t * string -> t
  val fun_ : (Modl.Var.t * Sigture.t, Modl.t) bind -> t
  val proj_fun : (Modl.Var.t * Sigture.t, Modl.t) bind -> t
  val ap : Modl.t * Modl.t -> t
  val proj_ap : Modl.t * Modl.t -> t
  val ascribe : Modl.t * Sigture.t -> t
  val rec_ : (Modl.Var.t * Sigture.t, Modl.t) bind -> t
  val body : (string * Modl_field.t) list -> t
  val dep_body : Defns.t -> t
  val let_ : (Defn.t, Modl.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end = struct
  module Var = Temp

  type oper =
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((string compare_ignore * Sigture.t) * Modl.t)
    | Proj_fun of ((string compare_ignore * Sigture.t) * Modl.t)
    | Ap of (Modl.t * Modl.t)
    | Proj_ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t)
    | Rec of ((string compare_ignore * Sigture.t) * Modl.t)
    | Body of ((String.t * Modl_field.internal) list)
    | Dep_body of Defns.t
    | Let of (Defn.internal * Modl.t)

  type t = oper Internal_sort.t

  type view =
    | Var of Var.t
    | Modl_proj of (Modl.t * String.t)
    | Fun of ((Modl.Var.t * Sigture.t) * Modl.t)
    | Proj_fun of ((Modl.Var.t * Sigture.t) * Modl.t)
    | Ap of (Modl.t * Modl.t)
    | Proj_ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t)
    | Rec of ((Modl.Var.t * Sigture.t) * Modl.t)
    | Body of ((String.t * Modl_field.t) list)
    | Dep_body of Defns.t
    | Let of (Defn.t * Modl.t)
  [@@deriving sexp_of]

  let into (view : view) : t =
    match view with
    | Var var -> Var (Free_var var)
    | Modl_proj (modl, string) ->
      Oper (Renaming.ident, Modl_proj (modl, string))
    | Fun ((modl_var, sigture), modl) ->
      Oper
        (Renaming.ident,
         Fun
           ((Modl.Var.name modl_var, sigture),
            Internal_sort.apply_renaming (Renaming.bind modl_var) modl))
    | Proj_fun ((modl_var, sigture), modl) ->
      Oper
        (Renaming.ident,
         Proj_fun
           ((Modl.Var.name modl_var, sigture),
            Internal_sort.apply_renaming (Renaming.bind modl_var) modl))
    | Ap (modl1, modl2) ->
      Oper (Renaming.ident, Ap (modl1, modl2))
    | Proj_ap (modl1, modl2) ->
      Oper (Renaming.ident, Proj_ap (modl1, modl2))
    | Ascribe (modl, sigture) ->
      Oper (Renaming.ident, Ascribe (modl, sigture))
    | Rec ((modl_var, sigture), modl) ->
      Oper
        (Renaming.ident,
         Rec
           ((Modl.Var.name modl_var, sigture),
            Internal_sort.apply_renaming (Renaming.bind modl_var) modl))
    | Body fields ->
      Oper
        (Renaming.ident,
         Body
           (List.map fields ~f:(fun (field_name, modl_field) ->
              let (modl_field', _modl_field_vars) = Modl_field.into modl_field in
              (field_name, modl_field'))))
    | Dep_body defns ->
      Oper (Renaming.ident, Dep_body defns)
    | Let (defn, modl) ->
      let (defn', defn_vars) = Defn.into defn in
      Oper (Renaming.ident, Let (defn', Internal_sort.apply_renaming (Renaming.bind' defn_vars) modl))

  let out (t : t) : view =
    match t with
    | Var (Bound_var _) -> raise_s [%message "Internal Abbot error."]
    | Var (Free_var var) -> Var var
    | Oper (renaming, oper) ->
      match oper with
      | Modl_proj (modl, string) ->
        Modl_proj (Internal_sort.apply_renaming renaming modl, string)
      | Fun ((bound_modl_name, sigture), modl) ->
        let modl_var = Modl.Var.create bound_modl_name in
        Fun
          ((modl_var, With_renaming.apply_renaming renaming sigture),
           Internal_sort.apply_renaming (Renaming.compose renaming (Renaming.unbind modl_var)) modl)
      | Proj_fun ((bound_modl_name, sigture), modl) ->
        let modl_var = Modl.Var.create bound_modl_name in
        Proj_fun
          ((modl_var, With_renaming.apply_renaming renaming sigture),
           Internal_sort.apply_renaming (Renaming.compose renaming (Renaming.unbind modl_var)) modl)
      | Ap (modl1, modl2) ->
        Ap (Internal_sort.apply_renaming renaming modl1, Internal_sort.apply_renaming renaming modl2)
      | Proj_ap (modl1, modl2) ->
        Proj_ap
          (Internal_sort.apply_renaming renaming modl1, Internal_sort.apply_renaming renaming modl2)
      | Ascribe (modl, sigture) ->
        Ascribe
          (Internal_sort.apply_renaming renaming modl, With_renaming.apply_renaming renaming sigture)
      | Rec ((bound_modl_name, sigture), modl) ->
        let modl_var = Modl.Var.create bound_modl_name in
        Rec
          ((modl_var, With_renaming.apply_renaming renaming sigture),
           Internal_sort.apply_renaming (Renaming.compose renaming (Renaming.unbind modl_var)) modl)
      | Body fields ->
        Body
          (List.map fields ~f:(fun (field_name, modl_field) ->
             let (modl_field', _modl_field_vars) = Modl_field.out modl_field in
             (field_name, modl_field')))
      | Dep_body defns ->
        Dep_body (With_renaming.apply_renaming renaming defns)
      | Let (defn, modl) ->
        let (defn', defn_vars) = Defn.out (With_renaming.apply_renaming renaming defn) in
        Let
          (defn',
           Internal_sort.apply_renaming
             (Renaming.compose renaming (Renaming.unbind' defn_vars))
             modl)

  let var arg = into (Var arg)
  let modl_proj arg = into (Modl_proj arg)
  let fun_ arg = into (Fun arg)
  let proj_fun arg = into (Proj_fun arg)
  let ap arg = into (Ap arg)
  let proj_ap arg = into (Proj_ap arg)
  let ascribe arg = into (Ascribe arg)
  let rec_ arg = into (Rec arg)
  let body arg = into (Body arg)
  let dep_body arg = into (Dep_body arg)
  let let_ arg = into (Let arg)

  let sexp_of_t t =
    [%sexp_of: view] (out t)

  let subst
        (type var)
        (type sort)
        (sort : (var, sort) Sort.t)
        (value : sort)
        (var : var)
        (t : t)
    : t =
    let view = out t in
    let view' =
      match view with
      | Var var' ->
        (match sort with
         | Sort.Modl ->
           if Temp.equal var var'
           then Modl.out value
           else Var var'
         | _ ->
           Var var')
      | Modl_proj (modl, string) ->
        Modl_proj (Modl.subst sort value var modl, string)
      | Fun ((modl_var, sigture), modl) ->
        Fun
          ((modl_var, Sigture.subst sort value var sigture),
           Modl.subst sort value var modl)
      | Proj_fun ((modl_var, sigture), modl) ->
        Proj_fun
          ((modl_var, Sigture.subst sort value var sigture),
           Modl.subst sort value var modl)
      | Ap (modl1, modl2) ->
        Ap
          (Modl.subst sort value var modl1,
           Modl.subst sort value var modl2)
      | Proj_ap (modl1, modl2) ->
        Proj_ap
          (Modl.subst sort value var modl1,
           Modl.subst sort value var modl2)
      | Ascribe (modl, sigture) ->
        Ascribe
          (Modl.subst sort value var modl,
           Sigture.subst sort value var sigture)
      | Rec ((modl_var, sigture), modl) ->
        Rec
          ((modl_var, Sigture.subst sort value var sigture),
           Modl.subst sort value var modl)
      | Body fields ->
        Body
          (List.map fields ~f:(fun (string, modl_field) ->
             (string, Modl_field.subst sort value var modl_field)))
      | Dep_body defns ->
        Dep_body (Defns.subst sort value var defns)
      | Let (defn, modl) ->
        Let
          (Defn.subst sort value var defn,
           Modl.subst sort value var modl)
    in
    into view'
end

and Sort : sig
  type (_, _) t =
    | Typ : (Typ.Var.t, Typ.t) t
    | Tag : (Tag.Var.t, Tag.t) t
    | Term : (Term.Var.t, Term.t) t
    | Modl : (Modl.Var.t, Modl.t) t
end = struct
  type (_, _) t =
    | Typ : (Typ.Var.t, Typ.t) t
    | Tag : (Tag.Var.t, Tag.t) t
    | Term : (Term.Var.t, Term.t) t
    | Modl : (Modl.Var.t, Modl.t) t
end
