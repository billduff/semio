open! Core
open! Import

(* CR wduff: This whole module is horrendous. Can semio do better? *)

module Typed
  : Typed_functor_intf.S
    with type 'a Unification_var.t := 'a Unification.Var.t
= struct
  module Unification_var = struct
    include Unification.Var
    let fold_map t = Obj.magic fold_map t
  end
  include Typed_functor.Make (Unification_var)
end
