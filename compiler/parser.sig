signature Parser = sig
  module Token : sig
    type t =
      | Type
      | Let
      | In
      | Fn
      | Match
      | With
      | Of
      | Lparen
      | Rparen
      | Lbrace
      | Rbrace
      | End
      | Val
      | Fun
      | Infix
      | Include
      | Module
      | Signature
      | Sig
      | Mod
      | Pat
      | Built_in
      | Equal
      | Eqarrow
      | Arrow
      | Bar
      | Colon
      | Comma
      | Dot
      | Wild
      | Number of Number.t
      | String of String.t
      | Name of String.t
      | Big_name of String.t
  end

  val parse : Token.t list -> Unbound.t
end
