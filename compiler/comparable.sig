signature Comparable = sig
  type t

  val compare : t -> t -> order
end
