open! Core
open! Import

module Id : sig
  type t [@@deriving compare, hash, sexp_of]

  include Comparable.S_plain with type t := t
  include Hashable.S_plain with type t := t

  val create : unit -> t
end = struct
  module T = struct
    type t = int [@@deriving compare, hash, sexp_of]
  end

  include T
  include Comparable.Make_plain (T)
  include Hashable.Make_plain (T)

  let counter = ref 0
  let create () =
    incr counter;
    !counter
end

module Tip = struct
  type t =
    { id : Id.t; rank : int }
  [@@deriving sexp_of]
end

module Node = struct
  type 'a t =
    | Tip of Tip.t
    | Value of 'a
  [@@deriving sexp_of]
end

module Var = struct
  type 'a t = 'a Node.t ref [@@deriving sexp_of]

  let compare_tips (t1 : _ t) (t2 : _ t) =
    match (!t1, !t2) with
    | (Tip { id = id1; rank = _ }, Tip { id = id2; rank = _ }) ->
      Id.compare id1 id2
    | (Value _, _) | (_, Value _) ->
      (* CR wduff: Better error message. *)
      raise_s [%message]
  ;;

  (* CR wduff: Does this actually make sense? Is it safe to swap out the ref like this? *)
  let fold_map (t : 'a t) ~(init : 'acc) ~(f : 'acc -> 'a -> 'acc * 'b) : 'acc * 'b t =
    match !t with
    | Tip tip -> init, { contents = Tip tip }
    | Value value ->
      let (acc, value) = f init value in
      acc, { contents = Value value }
  ;;
end

let newvar () =
  ref (Node.Tip { id = Id.create (); rank = 0 })
;;

let rec find ~value_of_uvar ~value_is_uvar (uvar : 'a Var.t) =
  match !uvar with
  | Tip tip -> `Tip (uvar, tip)
  | Value value ->
    let result = follow_value ~value_of_uvar ~value_is_uvar value in
    let value =
    match result with
    | `Non_uvar_value value ->
      value
    | `Tip (uvar, (_ : Tip.t)) ->
      value_of_uvar uvar
    in
    uvar := Value value;
    result

and follow_value ~value_of_uvar ~value_is_uvar value =
  match value_is_uvar value with
  | None -> `Non_uvar_value value
  | Some uvar ->
    find ~value_of_uvar ~value_is_uvar uvar
;;

let tip_or_non_uvar_value ~value_of_uvar ~value_is_uvar (uvar : _ Var.t) =
  match find ~value_of_uvar ~value_is_uvar uvar with
  | `Tip (uvar, (_ : Tip.t)) -> `Tip uvar
  | `Non_uvar_value value -> `Non_uvar_value value
;;

let unify ~value_of_uvar ~value_is_uvar ~occurs (value1 : 'a) (value2 : 'a) =
  (* CR wduff: I think this is a bit wrong performance-wise because it sometimes leaves an
     indirection through one extra uvar between most uvars that are getting set and the typ
     they end up pointing to, instead of collapsing the entire chain. *)
  match
    (follow_value ~value_of_uvar ~value_is_uvar value1,
     follow_value ~value_of_uvar ~value_is_uvar value2)
  with
  | (`Tip (uvar1, { id = id1; rank = rank1 }), `Tip (uvar2, { id = _; rank = rank2 })) ->
    begin
      match Ordering.of_int (Int.compare rank1 rank2) with
      | Less ->
        uvar1 := Value (value_of_uvar uvar2)
      | Greater ->
        uvar2 := Value (value_of_uvar uvar1)
      | Equal ->
        uvar2 := Value (value_of_uvar uvar1);
        uvar1 := Tip { id = id1; rank = rank1 + 1 }
    end;
    `Ok
  | (`Tip (uvar, (_ : Tip.t)), `Non_uvar_value value)
  | (`Non_uvar_value value, `Tip (uvar, (_ : Tip.t)))
    ->
    (* CR wduff: Improve the occurs check error message. *)
    assert (not (occurs ~tip:uvar ~in_:value));
    uvar := Value value;
    `Ok
  | (`Non_uvar_value value1, `Non_uvar_value value2) ->
    `These_must_be_equal (value1, value2)
;;
