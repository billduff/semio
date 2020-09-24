open! Core
open! Import

module T = struct
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
end

include T
include Sexpable.To_stringable (T)
