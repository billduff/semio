module type S = sig
  type before
  type after
  val translate : before -> after
end
