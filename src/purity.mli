open! Core
open! Import

type t =
  | Pure
  | Impure
[@@deriving sexp]

include Comparable.S with type t := t
