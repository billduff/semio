signature Dynamics = sig
  module Typed : Typed

  val eval : Typed.Term.t -> Typed.Term.t
end
