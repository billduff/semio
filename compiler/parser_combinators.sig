signature Parser_combinator = sig
  type t a

  val append : t a * t b -> t (a * b)

  val append_list : List.t (t a) -> t (List.t a)
end
