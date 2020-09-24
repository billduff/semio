signature Var = sig
  type t

  (* Creates a new, globally unique variable. *)
  val new : string -> t

  (* Tests whether two variables are equal. *)
  val equal : t -> t -> bool

  (* Compares two variables. *)
  val compare : t -> t -> number

  (* Provides a hash representation of the variable. *)
  val hash : t -> number

  (* Provides the string used to create the variable. *)
  val to_string : t -> string

  module Map : Map with type Key.t = t
end

signature Typed = sig
  module Sigture : sig
    type t

    (* (X : sigma1) -> sigma2 *)
    val Arrow : (Modl.Var.t * Sigture.t) * Sigture.t -> t
    pat Arrow : t => (Modl.Var.t * Sigture.t) * Sigture.t

    (* ??? *)
    val ProjArrow : (Modl.Var.t * Sigture.t) * Sigture.t -> t
    pat ProjArrow : t => (Modl.Var.t * Sigture.t) * Sigture.t

    (* sig ... end *)
    val Body : Decls.t -> t
    pat Body : t => Decls.t

    (* ??? *)
    val Rec : Modl.Var.t * Sigture.t -> t
    pat Rec : t => Modl.Var.t * Sigture.t

    val aequiv : t * t -> bool

    (* [tau / t] sigture *)
    val substTyp : Typ.t -> Typ.Var.t -> Sigture.t -> Sigture.t

    (* [M / X] sigture *)
    val substModl : Modl.t -> Modl.Var.t -> Sigture.t -> Sigture.t
  end

  module Pat : sig
    type t

    (* _ *)
    val Wild : t
    pat Wild : t

    (* x *)
    val Var : (Term.Var.t) -> t
    pat Var : t => (Term.Var.t)

    (* (p1, ..., pn) *)
    val Tuple : (list (Pat.t)) -> t
    pat Tuple : t => (list (Pat.t))

    (* Theta p *)
    val Tag : (Tag.t * optional Pat.t) -> t
    pat Tag : t => (Tag.t * optional Pat.t)

    (* (p : tau) *)
    val Ascribe : (Pat.t * Typ.t) -> t
    pat Ascribe : t => (Pat.t * Typ.t)

    val aequiv : t * t -> bool
  end

  module Modl_field : sig
    type t

    (* type ? = tau *)
    val Typ : (Typ.t) -> t
    pat Typ : t => (Typ.t)

    (* tag ? = Theta *)
    val Tag : (Tag.t) -> t
    pat Tag : t => (Tag.t)

    (* val ? = e *)
    val Val : (Term.t) -> t
    pat Val : t => (Term.t)

    (* module ? = M *)
    val Modl : (Modl.t) -> t
    pat Modl : t => (Modl.t)

    val aequiv : t * t -> bool
  end

  module Kind : sig
    type t

    (* type *)
    val Typ : t
    pat Typ : t

    (* S(tau) *)
    val Sing : (Typ.t) -> t
    pat Sing : t => (Typ.t)

    (* (t : k1) -> k2 *)
    val Arrow : (Typ.Var.t * Kind.t) * Kind.t -> t
    pat Arrow : t => (Typ.Var.t * Kind.t) * Kind.t

    val aequiv : t * t -> bool

    val substTyp : Typ.t -> Typ.Var.t -> Kind.t -> Kind.t
    val substModl : Modl.t -> Modl.Var.t -> Kind.t -> Kind.t
  end

  module Defn : sig
    type t

    (* type t = tau *)
    val Typ : (Typ.Var.t * Typ.t) -> t
    pat Typ : t => (Typ.Var.t * Typ.t)

    (* tag T = Theta *)
    val Tag : (Tag.Var.t * Tag.t) -> t
    pat Tag : t => (Tag.Var.t * Tag.t)

    (* val p = e *)
    val Val : (Pat.t * Term.t) -> t
    pat Val : t => (Pat.t * Term.t)

    (* module X = M *)
    val Modl : (Modl.Var.t * Modl.t) -> t
    pat Modl : t => (Modl.Var.t * Modl.t)

    val aequiv : t * t -> bool
  end

  module Decls : sig
    type t

    (* *)
    val End : t
    pat End : t

      (* name = decl in ... *)
    val Cons : (string * Decl.t) * Decls.t -> t
    pat Cons : t => (string * Decl.t) * Decls.t

    val aequiv : t * t -> bool

    (* [tau / t] decls *)
    val substTyp : Typ.t -> Typ.Var.t -> Decls.t -> Decls.t

    (* [M / X] decls *)
    val substModl : Modl.t -> Modl.Var.t -> Decls.t -> Decls.t
  end

  module Decl : sig
    type t

    (* type t : k *)
    val Typ : (Typ.Var.t * Kind.t) -> t
    pat Typ : t => (Typ.Var.t * Kind.t)

    (* tag ? : tau1 => tau2 or tag ? : tau *)
    val Tag : (Typ.t * optional Typ.t) -> t
    pat Tag : t => (Typ.t * optional Typ.t)

    (* val ? : tau *)
    val Val : (Typ.t) -> t
    pat Val : t => (Typ.t)

    (* module X : sigma *)
    val Modl : (Modl.Var.t * Sigture.t) -> t
    pat Modl : t => (Modl.Var.t * Sigture.t)

    val aequiv : t * t -> bool
  end

  module Typ : sig
    type t

    module Var : Var

    (* [unification_node] is exposed only for [Type_checker.Unification]. *)
    type unification_node
    val Tip : number -> unification_node
    pat Tip : unification_node => number
    val Node : t -> unification_node
    pat Node : unification_node => t

    val Var : (Typ.Var.t) -> t
    pat Var : t => (Typ.Var.t)

    (* u *)
    val UVar : number * ref unification_node -> t
    pat UVar : t => number * ref unification_node

    (* M.t *)
    val ModlProj : (Modl.t * string) -> t
    pat ModlProj : t => (Modl.t * string)

    (* fn (t : k) => tau *)
    val Fun : (Typ.Var.t * Kind.t) * Typ.t -> t
    pat Fun : t => (Typ.Var.t * Kind.t) * Typ.t

    (* tau1 tau2 *)
    val Ap : (Typ.t * Typ.t) -> t
    pat Ap : t => (Typ.t * Typ.t)

    (* tau1 -> tau2 *)
    val Arrow : (Typ.t * Typ.t) -> t
    pat Arrow : t => (Typ.t * Typ.t)

    (* tau1 * ... * taun *)
    val Prod : (list Typ.t) -> t
    pat Prod : t => (list Typ.t)

    (* In[n,1] : tau1 | ... In[n,n] of taun *)
    (* tau1 + ... + taun *)
    val Sum : (list Typ.t) -> t
    pat Sum : t => (list Typ.t)

    (* number *)
    val Number : t
    pat Number : t

    (* string *)
    val String : t
    val String : t

    val aequiv : Typ.t * Typ.t -> bool

    (* [tau1 / t] tau2 *)
    val subst : Typ.t -> Typ.Var.t -> Typ.t -> Typ.t

    (* Following two functions are autogenerated by
       Abbot but do not make sense semantically *)
    (* [e / x] tau *)
    val substTerm : Term.t -> Term.Var.t -> Typ.t -> Typ.t
    (* [Theta / T] tau *)
    val substTag : Tag.t -> Tag.Var.t -> Typ.t -> Typ.t

    (* [M / X] tau *)
    val substModl : Modl.t -> Modl.Var.t -> Typ.t -> Typ.t
  end

  module Term : sig
    type t

    module Var : Var

    (* x *)
    val Var : (Term.Var.t) -> t
    pat Var : t => (Term.Var.t)

    (* M.x *)
    val ModlProj : (Modl.t * string) -> t
    pat ModlProj : t => (Modl.t * string)

    (* fn p1 p2 : tau => e *)
    val Fun : (list Pat.t * optional Typ.t) * Term.t -> t
    pat Fun : t => (list Pat.t * optional Typ.t) * Term.t

    (* e1 e2 *)
    val Ap : (Term.t * Term.t) -> t
    pat Ap : t => (Term.t * Term.t)

    (* (e1, ..., en) *)
    val Tuple : (list Term.t) -> t
    pat Tuple : t => (list Term.t)

    (* In[n,i] e *)
    val In : (number * number * Term.t) -> t
    pat In : t => (number * number * Term.t)

    (* match e with p1 => e1 | ... | pn => en *)
    val Match : (Term.t * list (Pat.t * Term.t)) -> t
    pat Match : t => (Term.t * list (Pat.t * Term.t))

    (* example: 7 *)
    val Number : number -> t
    pat Number : t => number

    (* example: "hello, world" *)
    val String : (string) -> t
    pat String : t => (string)

    (* let defn in e *)
    val Let : Defn.t * Term.t -> t
    pat Let : t => Defn.t * Term.t

    (* (e : tau) *)
    val Ascribe : (Term.t * Typ.t) -> t
    pat Ascribe : t => (Term.t * Typ.t)

    val aequiv : Term.t * Term.t -> bool

    (* [tau / t] e *)
    val substTyp : Typ.t -> Typ.Var.t -> Term.t -> Term.t

    (* [e1 / x] e2 *)
    val subst : Term.t -> Term.Var.t -> Term.t -> Term.t

    (* [Theta / T] e *)
    val substTag : Tag.t -> Tag.Var.t -> Term.t -> Term.t

    (* [M / X] e *)
    val substModl : Modl.t -> Modl.Var.t -> Term.t -> Term.t
  end

  module Tag : sig
    type t

    module Var : Var

    (* T *)
    val Var : (Tag.Var.t) -> t
    pat Var : t => (Tag.Var.t)

    (* M.T *)
    val ModlProj : (Modl.t * string) -> t
    pat ModlProj : t => (Modl.t * string)

    (* In[n,i] *)
    val In : (number * number) -> t
    pat In : t => (number * number)

    (* destr(e) *)
    val Destr : (Term.t) -> t
    pat Destr : t => (Term.t)

    val aequiv : Tag.t * Tag.t -> bool

    (* [tau / t] Theta *)
    val substTyp : Typ.t -> Typ.Var.t -> Tag.t -> Tag.t

    (* [e / x] Theta *)
    val substTerm : Term.t -> Term.Var.t -> Tag.t -> Tag.t

    (* [Theta1 / T] Theta2 *)
    val subst : Tag.t -> Tag.Var.t -> Tag.t -> Tag.t

    (* [M / X] Theta *)
    val substModl : Modl.t -> Modl.Var.t -> Tag.t -> Tag.t
  end

  module Modl : sig
    type t

    module Var : Var

    (* X *)
    val Var : (Modl.Var.t) -> t
    pat Var : t => (Modl.Var.t)

    (* M.X *)
    val ModlProj : (Modl.t * string) -> t
    pat ModlProj : t => (Modl.t * string)

    (* Fn (X : sigma) => M *)
    val Fun : (Modl.Var.t * Sigture.t) * Modl.t -> t
    pat Fun : t => (Modl.Var.t * Sigture.t) * Modl.t

    (* ??? *)
    val ProjFun : (Modl.Var.t * Sigture.t) * Modl.t -> t
    pat ProjFun : t => (Modl.Var.t * Sigture.t) * Modl.t

    (* M1 M2 *)
    val Ap : (Modl.t * Modl.t) -> t
    pat Ap : t => (Modl.t * Modl.t)

    (* M1 M2 *)
    val ProjAp : (Modl.t * Modl.t) -> t
    pat ProjAp : t => (Modl.t * Modl.t)

    (* (M : sigma *)
    val Ascribe : (Modl.t * Sigture.t) -> t
    pat Ascribe : t => (Modl.t * Sigture.t)

    (* Fix (X : sigma) is M *)
    val Rec : (Modl.Var.t * Sigture.t) * Modl.t -> t
    pat Rec : t => (Modl.Var.t * Sigture.t) * Modl.t

    (* mod name1 = field1 ... namen = fieldn end*)
    val Body : (list (string * Modl_field.t)) -> t
    pat Body : t => (list (string * Modl_field.t))

    (* let defn in M *)
    val Let : Defn.t * Modl.t -> t
    pat Let : t => Defn.t * Modl.t

    val aequiv : Modl.t * Modl.t -> bool

    (* [tau / t] M *)
    val substTyp : Typ.t -> Typ.Var.t -> Modl.t -> Modl.t

    (* [e / x] M *)
    val substTerm : Term.t -> Term.Var.t -> Modl.t -> Modl.t

    (* [Theta / T] M *)
    val substTag : Tag.t -> Tag.Var.t -> Modl.t -> Modl.t

    (* [M1 / X] M2 *)
    val subst : Modl.t -> Modl.Var.t -> Modl.t -> Modl.t
  end
end
