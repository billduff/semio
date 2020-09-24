open! Core
open! Import

type t =
  | Print
  | String_init
  | String_length
  | String_unsafe_nth
  (* CR wduff:
  | Array_init
  | Array_length
  | Array_unsafe_nth*)
  | Number_compare
  | Char_compare
[@@deriving compare, enumerate, sexp]

include Stringable.S with type t := t
