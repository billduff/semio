open! Core
open! Import

exception MatchFailure

val eval : Typed.Term.t -> Typed.Term.t
