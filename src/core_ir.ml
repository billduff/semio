open! Core
open! Import

module Label = struct
  module T = struct
    type t = string [@@deriving compare, equal, hash, sexp_of]
  end

  include T
  include Comparable.Make_plain (T)
  include Hashable.Make_plain (T)
end

module Heap_loc = Unique_id.Int ()

include Core_ir_functor.Make (Label) (Heap_loc)
