open! Core
open! Import

module T = struct
  type t =
    | Pure
    | Impure
  [@@deriving sexp]

  let compare purity1 purity2 =
    match (purity1, purity2) with
    | (Pure, Pure) -> 0
    | (Pure, Impure) -> -1
    | (Impure, Pure) -> 1
    | (Impure, Impure) -> 0
end

include T

include Comparable.Make (T)
