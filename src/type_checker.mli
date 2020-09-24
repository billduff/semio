open! Core
open! Import
open Typed
module Context = Context.Internal

module Field_sort : sig
  type _ t =
    | Typ : Kind.t t
    | Val : Typ.t t
    | Tag : (Typ.t * Typ.t option) t
    | Modl : Sigture.t t
end

val weak_normalize : Context.t -> Typ.t -> Typ.t

module Uvar_set : Set.S_plain with type Elt.t = Typ.t Unification.Var.t

val uvars_in_sigture : Sigture.t -> Uvar_set.t

val uvars_in_kind : Kind.t -> Uvar_set.t

val uvars_in_typ : Typ.t -> Uvar_set.t

val subkind : Context.t -> Kind.t -> Kind.t -> bool

val typ_equiv : Context.t -> Typ.t -> Typ.t -> Kind.t -> bool

val lookup_field_in_decls : Modl.t -> Decls.t -> 'a Field_sort.t -> string -> 'a

val singleton : Typ.t -> Kind.t -> Kind.t

val subsigture : Context.t -> Sigture.t -> Sigture.t -> bool

val check_term : Context.t -> Term.t -> Typ.t

val check_typ : Context.t -> Typ.t -> Kind.t

val check_tag : Context.t -> Tag.t -> Typ.t * Typ.t option

val check_sigture : Context.t -> Sigture.t -> unit

val check_modl : Context.t -> Modl.t -> Purity.t * Sigture.t
