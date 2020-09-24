open! Core
open! Abbot_runtime

type ('a, 'b) bind = 'a * 'b

module rec Kind : sig
  type t [@@deriving sexp_of]

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
end

and Typ : sig
  type t [@@deriving sexp_of]

  module Var : Temp_intf.S

  (* [unification_node] and [unification_var] are exposed
     only for use by [Type_checker.Unification]. *)
  type 'a unification_node =
    | Tip of int
    | Node of 'a

  type 'a unification_var = int * 'a unification_node ref

  type view =
    | Var of Typ.Var.t
    | UVar of Typ.t unification_var
    | Modl_proj of (Modl.t * string)
    | Fun of (Typ.Var.t * Kind.t, Typ.t) bind
    | Ap of (Typ.t * Typ.t)
    | Arrow of (Typ.t * Typ.t)
    | Forall of (Typ.Var.t * Kind.t, Typ.t) bind
    | Record of Typ.t String.Map.t
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
end

and Decl : sig
  type t =
    | Typ of (Typ.Var.t * Kind.t)
    | Tag of (Typ.t * Typ.t option)
    | Val of Typ.t
    | Modl of (Modl.Var.t * Sigture.t)
  [@@deriving sexp_of]

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Decls : sig
  type t [@@deriving sexp_of]

  type view =
    | End
    | Cons of (string * Decl.t, Decls.t) bind
  [@@deriving sexp_of]

  val end_ : unit -> t
  val cons : (string * Decl.t, Decls.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Sigture : sig
  type t [@@deriving sexp_of]

  type view =
    | Arrow of (Modl.Var.t * Sigture.t, Sigture.t) bind
    | Proj_arrow of (Modl.Var.t * Sigture.t, Sigture.t) bind
    | Body of Decls.t
    | Rec of (Modl.Var.t, Sigture.t) bind
  [@@deriving sexp_of]

  val arrow : (Modl.Var.t * Sigture.t, Sigture.t) bind -> t
  val proj_arrow : (Modl.Var.t * Sigture.t, Sigture.t) bind -> t
  val body : Decls.t -> t
  val rec_ : (Modl.Var.t, Sigture.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Tag : sig
  type t [@@deriving sexp_of]

  module Var : Temp_intf.S

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
end

and Pat : sig
  type t =
    | Wild
    | Var of Term.Var.t
    | Record of Pat.t String.Map.t
    | Tag of (Tag.t * Pat.t option)
    | Number of Int64.t
    | String of string
    | Ascribe of (Pat.t * Typ.t)
  [@@deriving sexp_of]

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Term : sig
  type t [@@deriving sexp_of]

  module Var : Temp_intf.S

  type view =
    | Var of Term.Var.t
    | Modl_proj of (Modl.t * string)
    | Fun of (Pat.t list * Typ.t option, Term.t) bind
    | Typ_fun of (Typ.Var.t * Kind.t, Term.t) bind
    | Ap of (Term.t * Term.t)
    | Typ_ap of (Term.t * Typ.t)
    | Record of Term.t String.Map.t
    | In of (int * int * Term.t)
    | Match of (Term.t * (Pat.t, Term.t) bind list)
    | Number of Int64.t
    | Char of char
    | String of string
    | Built_in of (string * Typ.t)
    | Let of (Defn.t, Term.t) bind
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
end

and Defn : sig
  type t =
    | Typ of (Typ.Var.t * Typ.t)
    | Tag of (Tag.Var.t * Tag.t)
    | Val of (Term.Var.t * Term.t)
    | Modl of (Modl.Var.t * Modl.t)
  [@@deriving sexp_of]

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Defns : sig
  type t [@@deriving sexp_of]

  type view =
    | End
    | Cons of (string * Defn.t, Defns.t) bind
  [@@deriving sexp_of]

  val end_ : unit -> t
  val cons : (string * Defn.t, Defns.t) bind -> t

  val into : view -> t
  val out : t -> view

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Modl_field : sig
  type t =
    | Typ of Typ.t
    | Tag of Tag.t
    | Val of Term.t
    | Modl of Modl.t
  [@@deriving sexp_of]

  val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
end

and Modl : sig
  type t [@@deriving sexp_of]

  module Var : Temp_intf.S

  type view =
    | Var of Modl.Var.t
    | Modl_proj of (Modl.t * string)
    | Fun of (Modl.Var.t * Sigture.t, Modl.t) bind
    | Proj_fun of (Modl.Var.t * Sigture.t, Modl.t) bind
    | Ap of (Modl.t * Modl.t)
    | Proj_ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t)
    | Rec of (Modl.Var.t * Sigture.t, Modl.t) bind
    | Body of (string * Modl_field.t) list
    | Dep_body of Defns.t
    | Let of (Defn.t, Modl.t) bind
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
end

and Sort : sig
  type (_, _) t =
    | Typ : (Typ.Var.t, Typ.t) t
    | Tag : (Tag.Var.t, Tag.t) t
    | Term : (Term.Var.t, Term.t) t
    | Modl : (Modl.Var.t, Modl.t) t
end
