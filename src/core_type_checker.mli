open! Core
open! Import
open Core_ir

module Length_context : sig
  type t

  val empty : t
end

module Typ_context : sig
  type t

  val empty : t
end

module Term_context : sig
  type t

  val empty : t
end

val synth_typ : Length_context.t -> Typ_context.t -> Typ.t -> Kind.t
val check_typ : Length_context.t -> Typ_context.t -> Typ.t -> Kind.t -> unit

val synth_term : Typ_context.t -> Term_context.t -> Term.t -> Typ.t
val check_term : Typ_context.t -> Term_context.t -> Term.t -> Typ.t -> unit
