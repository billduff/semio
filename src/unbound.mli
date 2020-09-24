(* Unbound contains trees that represent unbound expressions of each sort. *)
open! Core
open! Import

module With_positions : sig
  type 'a t =
    { start_pos : Source_code_position.t
    ; end_pos : Source_code_position.t
    ; without_positions : 'a
    }
  [@@deriving sexp_of]
end

module rec Typ : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Ap of Typ.t list
    | Record of (string * Typ.t) list
    | Forall of (string * Typ.t) (* ??? allow kinds? *)

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Decl : sig
  type untagged =
    | InfixTyp of string
    | InfixTerm of string
    | Typ of (string * string list * Typ.t option)
    | Tag of (string * Typ.t * Typ.t option)
    | Val of (string * Typ.t)
    | Sigture of (string * Sigture.t) (* ??? not yet in il *)
    | Modl of (string * Sigture.t)
    | Include of Sigture.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Sigture : sig
  (* ??? Add sigture calculus operations. *)
  type untagged =
    | Var of (Source_code_position.t * string) (* ??? not yet in il *)
    | Modl_proj of (Modl.t * string) (* ??? not yet in il *)
    | Arrow of ((string * Sigture.t) * Sigture.t) (* ??? not yet in parser *)
    | Body of Decl.t list
    | With_type of Sigture.t * (string list * string) * Typ.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Tag : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string)
    | Destr of Term.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Pat : sig
  type untagged =
    | Wild
    | Var of (Source_code_position.t * string)
    | Record of (string * Pat.t) list
    | Tag of (Tag.t * Pat.t option)
    | Number of Int64.t
    | String of string
    | Ascribe of (Pat.t * Typ.t) (**)

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Term : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string) (* ??? only for modl vars for now *)
    | Fun of (Pat.t list * Typ.t option * Term.t)
    | Ap of Term.t list
    | Record of (string * Term.t) list (* ??? fields could possibly be in modules *)
    | Match of (Term.t * (Pat.t * Term.t) list)
    | Number of Int64.t
    | String of string
    | Built_in of (string * Typ.t)
    | Let of (Defn.t list * Term.t)
    | Ascribe of (Term.t * Typ.t) (**)

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Defn : sig
  type untagged =
    | InfixTyp of string
    | InfixTerm of string
    | TypAlias of (string * string list * Typ.t)
    | SumTyp of (string * string list * (string * Typ.t option) list)
    | Tag of (string * (Typ.t * Typ.t option) option * Tag.t)
    | Val of (Pat.t * Term.t)
    | Fun of (string * Pat.t list * Typ.t option * Term.t)
    | Sigture of (string * Sigture.t)
    | Modl of (string * (string * Sigture.t) option * Sigture.t option * Modl.t)
    | Include of Modl.t

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end

and Modl : sig
  type untagged =
    | Var of (Source_code_position.t * string)
    | Modl_proj of (Modl.t * string) (* ??? only for modl vars for now *)
    | Ap of (Modl.t * Modl.t)
    | Ascribe of (Modl.t * Sigture.t) (* ??? not yet in parser *)
    | Body of Defn.t list

  type t = untagged With_positions.t [@@deriving sexp_of]

  val to_string : t -> string
end
