open! Core
open! Import

module U = Unbound
module T = Typed

module rec Fixity : sig
  type t =
    { infix_typs : Parse_infix.precedence String.Map.t String.Map.t
    ; infix_terms : Parse_infix.precedence String.Map.t String.Map.t
    ; sigtures : Fixity_sigture.t String.Map.t
    ; modls : Fixity_sigture.t String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t

  val add_infix_typ : t -> string -> t
  val add_infix_typ_precedence : t -> string -> precedes:string -> t
  val add_infix_term : t -> string -> t
  val add_infix_term_precedence : t -> string -> precedes:string -> t
  val add_sigture : t -> string -> Fixity_sigture.t -> t
  val add_modl : t -> string -> Fixity_sigture.t -> t
  val merge : t -> t -> t
end

and Fixity_sigture : sig
  type t =
    | Body of Fixity.t
    | Arrow of t
  [@@deriving sexp_of]
end

type 'a generalized = [ `Specialize ] -> 'a

module rec Elab : sig
  type t =
    { typs : T.Typ.t String.Map.t
    ; tags : T.Tag.t generalized String.Map.t
    ; terms : T.Term.t generalized String.Map.t
    ; sigtures : (T.Sigture.t * Foo_sigture.t) String.Map.t
    ; modls : (T.Modl.t generalized * Elab_sigture.t) String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> string -> T.Typ.t -> t
  val add_tag : t -> string -> T.Tag.t -> t
  val add_general_tag : t -> string -> T.Tag.t generalized -> t
  val add_term : t -> string -> T.Term.t -> t
  val add_general_term : t -> string -> T.Term.t generalized -> t
  val add_sigture : t -> string -> T.Sigture.t * Foo_sigture.t -> t
  val add_modl : t -> string -> T.Modl.t * Elab_sigture.t -> t
  val add_general_modl : t -> string -> T.Modl.t generalized * Elab_sigture.t -> t
  val merge : t -> t -> t
end

(* ??? Name this much better *)
and Foo : sig
  type t =
    { typs : String.Set.t
    ; tags : String.Set.t
    ; terms : String.Set.t
    ; sigtures : Foo_sigture.t String.Map.t
    ; modls : Foo_sigture.t String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> string -> t
  val add_tag : t -> string -> t
  val add_term : t -> string -> t
  val add_sigture : t -> string -> Foo_sigture.t -> t
  val add_modl : t -> string -> Foo_sigture.t -> t
  val merge : t -> t -> t
end

and Elab_creator : sig
  type t =
    { typs : (T.Modl.t -> T.Typ.t) String.Map.t
    ; tags : (T.Modl.t -> T.Tag.t generalized) String.Map.t
    ; terms : (T.Modl.t -> T.Term.t generalized) String.Map.t
    ; sigtures : ((T.Modl.t -> T.Sigture.t) * Foo_sigture.t) String.Map.t
    ; modls : ((T.Modl.t -> T.Modl.t generalized) * Elab_sigture.t) String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> string -> (T.Modl.t -> T.Typ.t) -> t
  val add_tag : t -> string -> (T.Modl.t -> T.Tag.t) -> t
  val add_general_tag : t -> string -> (T.Modl.t -> T.Tag.t generalized) -> t
  val add_term : t -> string -> (T.Modl.t -> T.Term.t) -> t
  val add_general_term : t -> string -> (T.Modl.t -> T.Term.t generalized) -> t
  val add_sigture : t -> string -> ((T.Modl.t -> T.Sigture.t) * Foo_sigture.t) -> t
  val add_modl : t -> string -> ((T.Modl.t -> T.Modl.t) * Elab_sigture.t) -> t
  val add_general_modl : t -> string -> ((T.Modl.t -> T.Modl.t generalized) * Elab_sigture.t) -> t
  val merge : t -> t -> t
  val apply : t -> T.Modl.t -> Elab.t
end

and Elab_sigture : sig
  type t =
    | Body of Elab_creator.t
    | Arrow of Foo_sigture.t * t
  [@@deriving sexp_of]
end

and Foo_sigture : sig
  type t =
    | Body of Foo.t
    | Arrow of t * t
  [@@deriving sexp_of]
end

module Internal : sig
  type t =
    { typs : T.Kind.t T.Typ.Var.Map.t
    ; tags : (T.Typ.t * T.Typ.t option) T.Tag.Var.Map.t
    ; terms : T.Typ.t T.Term.Var.Map.t
    ; modls : T.Sigture.t T.Modl.Var.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> T.Typ.Var.t -> T.Kind.t -> t
  val add_tag : t -> T.Tag.Var.t -> T.Typ.t * T.Typ.t option -> t
  val add_term : t -> T.Term.Var.t -> T.Typ.t -> t
  val add_modl : t -> T.Modl.Var.t -> T.Sigture.t -> t
  val merge : t -> t -> t
end

type t =
  { fixity : Fixity.t
  ; elab : Elab.t
  ; internal : Internal.t
  }
[@@deriving sexp_of]

val empty : t

val merge : t -> t -> t

val merge_maps : ('a, 'b, 'c) Map.t -> ('a, 'b, 'c) Map.t -> ('a, 'b, 'c) Map.t
