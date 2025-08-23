open! Core
open! Import

module Label : sig
  type t [@@deriving compare, equal, hash, sexp_of]

  include Comparable.S_plain with type t := t
  include Hashable.S_plain with type t := t
end

module Heap_loc : sig
  type t [@@deriving compare, equal, hash, sexp_of]

  val create : unit -> t

  include Comparable.S_plain with type t := t
  include Hashable.S_plain with type t := t
end

include Core_ir_functor_intf.S with module Label := Label and module Heap_loc := Heap_loc
