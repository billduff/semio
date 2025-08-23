open! Core
open! Import

(* CR wduff: This no longer actually does any knot-tying, so maybe we can remove it and inline the
   functor application into typed.ml. *)
module Typed : Typed_functor_intf.S with type 'a Unification_var.t := 'a Unification.Var.t = struct
  module Unification_var = Unification.Var
  include Typed_functor.Make (Unification_var)
end
