signature ORDER = sig
  type t
  type order = t
  pat Less : order
  pat Equal : order
  pat Greater : order
  val Less : order
  val Equal : order
  val Greater : order
end
