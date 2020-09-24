open! Core
open! Import

type precedence =
  | Less
  | Greater
[@@deriving sexp]

val parse_infix
  :  ('a -> Sexp.t)
  -> is_infix:('a -> bool)
  -> precedence:('a -> 'a -> precedence option)
  -> convert:('a -> 'b)
  -> ap:('b -> 'b -> 'b)
  -> 'a list
  -> 'b
