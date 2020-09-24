open! Core
open! Import

module Var : sig
  type 'a t [@@deriving sexp_of]

  val compare_tips : _ t -> _ t -> int

  val fold_map : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'a) -> 'acc * 'a t
end

val newvar : unit -> _ Var.t

val tip_or_non_uvar_value
  :  value_of_uvar:('a Var.t -> 'a)
  -> value_is_uvar:('a -> 'a Var.t option)
  -> 'a Var.t
  -> [ `Tip of 'a Var.t  | `Non_uvar_value of 'a ]

val unify
  :  value_of_uvar:('a Var.t -> 'a)
  -> value_is_uvar:('a -> 'a Var.t option)
  -> occurs:(tip:'a Var.t -> in_:'a -> bool)
  -> 'a
  -> 'a
  -> [ `Ok | `These_must_be_equal of 'a * 'a ]
