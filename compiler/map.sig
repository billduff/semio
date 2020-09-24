signature Map = sig
  module Key : Comparable

  type t a

  val empty : (a : type) -> t a

  val singleton : (a : type) -> Key.t -> a -> t a

  val set : (a : type) -> t a -> Key.t -> a -> t a

  val fold : (a : type) -> (b : type) -> t a -> b -> (Key.t -> a -> b -> b) -> b
end
