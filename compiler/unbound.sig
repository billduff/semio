(* CR wduff: Add [to_string] functions. *)

signature Unbound = sig
  module Typ : sig
    type untagged

    val Var : Source_code_position.t * String.t -> untagged
    pat Var : untagged => Source_code_position.t * String.t

    val Modl_proj : Modl.t * String.t -> untagged
    pat Modl_proj : untagged => Modl.t * String.t

    val Ap : List.t Typ.t -> untagged
    pat Ap : untagged => List.t Typ.t

    val Record : List.t (String.t * Typ.t) -> untagged
    pat Record : untagged => List.t (String.t * Typ.t)

    val Forall : String.t * Typ.t -> untagged
    pat Forall : untagged => String.t * Typ.t

    type t = With_positions.t untagged
  end

  module Decl : sig
    type untagged

    val InfixTyp : String.t -> untagged
    pat InfixTyp : untagged => String.t

    val InfixTerm : String.t -> untagged
    pat InfixTerm : untagged => String.t

    val Typ : String.t * List.t String.t * Optional.t Typ.t -> untagged
    pat Typ : untagged => String.t * List.t String.t * Optional.t Typ.t

    val Tag : String.t * Typ.t * Optional.t Typ.t -> untagged
    pat Tag : untagged => String.t * Typ.t * Optional.t Typ.t

    val Val : String.t * Typ.t -> untagged
    pat Val : untagged => String.t * Typ.t

    val Sigture : String.t * Sigture.t -> untagged
    pat Sigture : untagged => String.t * Sigture.t

    val Modl : String.t * Sigture.t -> untagged
    pat Modl : untagged => String.t * Sigture.t

    val Include : Sigture.t -> untagged
    pat Include : untagged => Sigture.t

    type t = With_positions.t untagged
  end

  module Sigture : sig
    type untagged

    val Var : Source_code_position.t * String.t -> untagged
    pat Var : untagged => Source_code_position.t * String.t

    val Modl_proj : Modl.t * String.t -> untagged
    pat Modl_proj : untagged => Modl.t * String.t

    val Arrow : (String.t * Sigture.t) * Sigture.t -> untagged
    pat Arrow : untagged => (String.t * Sigture.t) * Sigture.t

    val Body : List.t Decl.t -> untagged
    pat Body : untagged => List.t Decl.t

    type t = With_positions.t untagged
  end

  module Tag : sig
    type untagged

    val Var : Source_code_position.t * String.t -> untagged
    pat Var : untagged => Source_code_position.t * String.t

    val Modl_proj : Modl.t * String.t -> untagged
    pat Modl_proj : untagged => Modl.t * String.t

    val Destr : Term.t -> untagged
    pat Destr : untagged => Term.t

    type t = With_positions.t untagged
  end

  module Pat : sig
    type untagged

    val Wild : t
    pat Wild : t

    val Var : Source_code_position.t * String.t -> untagged
    pat Var : untagged => Source_code_position.t * String.t

    val Record : List.t (String.t * Pat.t) -> untagged
    pat Record : untagged => List.t (String.t * Pat.t)

    val Tag : Tag.t * Optional.t Pat.t -> untagged
    pat Tag : untagged => Tag.t * Optional.t Pat.t

    val Number : Number.t -> untagged
    pat Number : untagged => Number.t

    val String : String.t -> untagged
    pat String : untagged => String.t

    val Ascribe : Pat.t * Typ.t -> untagged
    pat Ascribe : untagged => Pat.t * Typ.t

    type t = With_positions.t untagged
  end

  module Term : sig
    type untagged

    val Var : Source_code_position.t * String.t -> untagged
    pat Var : untagged => Source_code_position.t * String.t

    val Modl_proj : Modl.t * String.t -> untagged
    pat Modl_proj : untagged => Modl.t * String.t

    val Fun : List.t Pat.t * Optional.t Typ.t * Term.t -> untagged
    pat Fun : untagged => List.t Pat.t * Optional.t Typ.t * Term.t

    val Ap : List.t Term.t -> untagged
    pat Ap : untagged => List.t Term.t

    val Record : List.t (String.t * Term.t) -> untagged
    pat Record : untagged => List.t (String.t * Term.t)

    val Match : Term.t * List.t (Pat.t * Term.t) -> untagged
    pat Match : untagged => Term.t * List.t (Pat.t * Term.t)

    val Number : Number.t -> untagged
    pat Number : untagged => Number.t

    val String : String.t -> untagged
    pat String : untagged => String.t

    val Built_in : String.t * Typ.t -> untagged
    pat Built_in : untagged => String.t * Typ.t

    val Let : List.t Defn.t * Term.t -> untagged
    pat Let : untagged => List.t Defn.t * Term.t

    val Ascribe : Term.t * Typ.t -> untagged
    pat Ascribe : untagged => Term.t * Typ.t

    type t = With_positions.t untagged
  end

  module Defn : sig
    type untagged

    val InfixTyp : String.t -> untagged
    pat InfixTyp : untagged => String.t

    val InfixTerm : String.t -> untagged
    pat InfixTerm : untagged => String.t

    val TypAlias : String.t * List.t String.t * Typ.t -> untagged
    pat TypAlias : untagged => String.t * List.t String.t * Typ.t

    val SumTyp : String.t * List.t String.t * List.t (String.t * Optional.t Typ.t) -> untagged
    pat SumTyp : untagged => String.t * List.t String.t * List.t (String.t * Optional.t Typ.t)

    val Tag : String.t * Optional.t (Typ.t * Optional.t Typ.t) * Tag.t -> untagged
    pat Tag : untagged => String.t * Optional.t (Typ.t * Optional.t Typ.t) * Tag.t

    val Val : Pat.t * Term.t -> untagged
    pat Val : untagged => Pat.t * Term.t

    val Fun : String.t * List.t Pat.t * Optional.t Typ.t * Term.t -> untagged
    pat Fun : untagged => String.t * List.t Pat.t * Optional.t Typ.t * Term.t

    val Sigture : String.t * Sigture.t -> untagged
    pat Sigture : untagged => String.t * Sigture.t

    val Modl : String.t * Optional.t (String.t * Sigture.t) * Optional.t Sigture.t * Modl.t -> untagged
    pat Modl : untagged => String.t * Optional.t (String.t * Sigture.t) * Optional.t Sigture.t * Modl.t

    val Include : Modl.t -> untagged
    pat Include : untagged => Modl.t

    type t = With_positions.t untagged
  end

  module Modl : sig
    type untagged

    val Var : Source_code_position.t * String.t -> untagged
    pat Var : untagged => Source_code_position.t * String.t

    val Modl_proj : Modl.t * String.t -> untagged
    pat Modl_proj : untagged => Modl.t * String.t

    val Ap : Modl.t * Modl.t -> untagged
    pat Ap : untagged => Modl.t * Modl.t

    val Ascribe : Modl.t * Sigture.t -> untagged
    pat Ascribe : untagged => Modl.t * Sigture.t

    val Body : List.t Defn.t -> untagged
    pat Body : untagged => List.t Defn.t

    type t = With_positions.t untagged
  end
end
