open! Core
open! Import

module Typed : Typed_functor_intf.S with type 'a Unification_var.t := 'a Unification.Var.t = struct
  module Unification_var = Unification.Var
  include Typed_functor.Make (Unification_var)
end
