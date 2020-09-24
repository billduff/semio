open! Core
open! Import

module U = Unbound
module T = Typed

let merge_maps map1 map2 =
  Map.merge map1 map2
    ~f:(fun ~key:_ -> function
      | (`Left x | `Right x | `Both (_, x)) ->
        (* CR wduff: Disallow shadowing. *)
        Some x)
;;

module rec Fixity : sig
  type t =
    { infix_typs : Parse_infix.precedence String.Map.t String.Map.t
    ; infix_terms : Parse_infix.precedence String.Map.t String.Map.t
    ; sigtures : Fixity_sigture.t String.Map.t
    ; modls : Fixity_sigture.t String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t

  val add_infix_typ : t -> string -> t
  val add_infix_typ_precedence : t -> string -> precedes:string -> t
  val add_infix_term : t -> string -> t
  val add_infix_term_precedence : t -> string -> precedes:string -> t
  val add_sigture : t -> string -> Fixity_sigture.t -> t
  val add_modl : t -> string -> Fixity_sigture.t -> t
  val merge : t -> t -> t
end = struct
  type t =
    { infix_typs : Parse_infix.precedence String.Map.t String.Map.t
    ; infix_terms : Parse_infix.precedence String.Map.t String.Map.t
    ; sigtures : Fixity_sigture.t String.Map.t
    ; modls : Fixity_sigture.t String.Map.t
    }
  [@@deriving sexp_of]

  let empty =
    { infix_typs = String.Map.empty
    ; infix_terms = String.Map.empty
    ; sigtures = String.Map.empty
    ; modls = String.Map.empty
    }
  ;;

  let add_infix_typ t key =
    { t with infix_typs = String.Map.set t.infix_typs ~key ~data:String.Map.empty }
  ;;

  let add_infix_typ_precedence _t _name1 ~precedes:_name2 = failwith "unimpl"

  let add_infix_term t key =
    { t with infix_terms = String.Map.set t.infix_terms ~key ~data:String.Map.empty }
  ;;

  let add_infix_term_precedence _t _name1 ~precedes:_name2 = failwith "unimpl"

  let add_sigture t key data =
    { t with sigtures = String.Map.set t.sigtures ~key ~data }
  ;;

  let add_modl t key data =
    { t with modls = String.Map.set t.modls ~key ~data }
  ;;

  (* ??? propagate new infix implications, could fail if a loop is formed *)
  let merge t1 t2 =
    { infix_typs = merge_maps t1.infix_typs t2.infix_typs
    ; infix_terms = merge_maps t1.infix_terms t2.infix_terms
    ; sigtures = merge_maps t1.sigtures t2.sigtures
    ; modls = merge_maps t1.modls t2.modls
    }
  ;;
end

and Fixity_sigture : sig
  type t =
    | Body of Fixity.t
    | Arrow of t
  [@@deriving sexp_of]
end = struct
  type t =
    | Body of Fixity.t
    | Arrow of t
  [@@deriving sexp_of]
end

type 'a generalized = [ `Specialize ] -> 'a

let sexp_of_generalized sexp_of_a generalized =
  sexp_of_a (generalized `Specialize)
;;

module rec Elab : sig
  type t =
    { typs : T.Typ.t String.Map.t
    ; tags : T.Tag.t generalized String.Map.t
    ; terms : T.Term.t generalized String.Map.t
    ; sigtures : (T.Sigture.t * Foo_sigture.t) String.Map.t
    ; modls : (T.Modl.t generalized * Elab_sigture.t) String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> string -> T.Typ.t -> t
  val add_tag : t -> string -> T.Tag.t -> t
  val add_general_tag : t -> string -> T.Tag.t generalized -> t
  val add_term : t -> string -> T.Term.t -> t
  val add_general_term : t -> string -> T.Term.t generalized -> t
  val add_sigture : t -> string -> T.Sigture.t * Foo_sigture.t -> t
  val add_modl : t -> string -> T.Modl.t * Elab_sigture.t -> t
  val add_general_modl : t -> string -> T.Modl.t generalized * Elab_sigture.t -> t
  val merge : t -> t -> t
end = struct
  type t =
    { typs : T.Typ.t String.Map.t
    ; tags : T.Tag.t generalized String.Map.t
    ; terms : T.Term.t generalized String.Map.t
    ; sigtures : (T.Sigture.t * Foo_sigture.t) String.Map.t
    ; modls : (T.Modl.t generalized * Elab_sigture.t) String.Map.t
    }
  [@@deriving sexp_of]

  let empty =
    { typs = String.Map.empty
    ; tags = String.Map.empty
    ; terms = String.Map.empty
    ; sigtures = String.Map.empty
    ; modls = String.Map.empty
    }
  ;;

  let add_typ t key data =
    { t with typs = Map.set t.typs ~key ~data }
  ;;

  let add_tag t key data =
    { t with tags = Map.set t.tags ~key ~data:(const data) }
  ;;

  let add_general_tag t key data =
    { t with tags = Map.set t.tags ~key ~data }
  ;;

  let add_term t key data =
    { t with terms = Map.set t.terms ~key ~data:(const data) }
  ;;

  let add_general_term t key data =
    { t with terms = Map.set t.terms ~key ~data }
  ;;

  let add_sigture t key data =
    { t with sigtures = Map.set t.sigtures ~key ~data }
  ;;

  let add_modl t key (modl, elab_sigture) =
    { t with modls = Map.set t.modls ~key ~data:(const modl, elab_sigture) }
  ;;

  let add_general_modl t key data =
    { t with modls = Map.set t.modls ~key ~data }
  ;;

  let merge t1 t2 =
    { typs = merge_maps t1.typs t2.typs
    ; tags = merge_maps t1.tags t2.tags
    ; terms = merge_maps t1.terms t2.terms
    ; modls = merge_maps t1.modls t2.modls
    ; sigtures = merge_maps t1.sigtures t2.sigtures
    }
  ;;
end

and Foo : sig
  type t =
    { typs : String.Set.t
    ; tags : String.Set.t
    ; terms : String.Set.t
    ; sigtures : Foo_sigture.t String.Map.t
    ; modls : Foo_sigture.t String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> string -> t
  val add_tag : t -> string -> t
  val add_term : t -> string -> t
  val add_sigture : t -> string -> Foo_sigture.t -> t
  val add_modl : t -> string -> Foo_sigture.t -> t
  val merge : t -> t -> t
end = struct
  type t =
    { typs : String.Set.t
    ; tags : String.Set.t
    ; terms : String.Set.t
    ; sigtures : Foo_sigture.t String.Map.t
    ; modls : Foo_sigture.t String.Map.t
    }
  [@@deriving sexp_of]

  let empty =
    { typs = String.Set.empty
    ; tags = String.Set.empty
    ; terms = String.Set.empty
    ; sigtures = String.Map.empty
    ; modls = String.Map.empty
    }
  ;;

  let add_typ t key =
    { t with typs = Set.add t.typs key }
  ;;

  let add_tag t key =
    { t with tags = Set.add t.tags key }
  ;;

  let add_term t key =
    { t with terms = Set.add t.terms key }
  ;;

  let add_sigture t key data =
    { t with sigtures = Map.set t.sigtures ~key ~data }
  ;;

  let add_modl t key data =
    { t with modls = Map.set t.modls ~key ~data }
  ;;

  let merge t1 t2 =
    { typs = Set.union t1.typs t2.typs
    ; tags = Set.union t1.tags t2.tags
    ; terms = Set.union t1.terms t2.terms
    ; modls = merge_maps t1.modls t2.modls
    ; sigtures = merge_maps t1.sigtures t2.sigtures
    }
  ;;
end

(* ??? Name this better *)
and Elab_creator : sig
  type t =
    { typs : (T.Modl.t -> T.Typ.t) String.Map.t
    ; tags : (T.Modl.t -> T.Tag.t generalized) String.Map.t
    ; terms : (T.Modl.t -> T.Term.t generalized) String.Map.t
    ; sigtures : ((T.Modl.t -> T.Sigture.t) * Foo_sigture.t) String.Map.t
    ; modls : ((T.Modl.t -> T.Modl.t generalized) * Elab_sigture.t) String.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> string -> (T.Modl.t -> T.Typ.t) -> t
  val add_tag : t -> string -> (T.Modl.t -> T.Tag.t) -> t
  val add_general_tag : t -> string -> (T.Modl.t -> T.Tag.t generalized) -> t
  val add_term : t -> string -> (T.Modl.t -> T.Term.t) -> t
  val add_general_term : t -> string -> (T.Modl.t -> T.Term.t generalized) -> t
  val add_sigture : t -> string -> ((T.Modl.t -> T.Sigture.t) * Foo_sigture.t) -> t
  val add_modl : t -> string -> ((T.Modl.t -> T.Modl.t) * Elab_sigture.t) -> t
  val add_general_modl : t -> string -> ((T.Modl.t -> T.Modl.t generalized) * Elab_sigture.t) -> t
  val merge : t -> t -> t
  val apply : t -> T.Modl.t -> Elab.t
end = struct
  type t =
    { typs : (T.Modl.t -> T.Typ.t) String.Map.t
    ; tags : (T.Modl.t -> T.Tag.t generalized) String.Map.t
    ; terms : (T.Modl.t -> T.Term.t generalized) String.Map.t
    ; sigtures : ((T.Modl.t -> T.Sigture.t) * Foo_sigture.t) String.Map.t
    ; modls : ((T.Modl.t -> T.Modl.t generalized) * Elab_sigture.t) String.Map.t
    }
  [@@deriving sexp_of]

  let empty =
    { typs = String.Map.empty
    ; tags = String.Map.empty
    ; terms = String.Map.empty
    ; sigtures = String.Map.empty
    ; modls = String.Map.empty
    }
  ;;

  let add_typ t key data =
    { t with typs = Map.set t.typs ~key ~data }
  ;;

  let add_tag t key data =
    { t with tags = Map.set t.tags ~key ~data:(fun modl -> const (data modl)) }
  ;;

  let add_general_tag t key data =
    { t with tags = Map.set t.tags ~key ~data }
  ;;

  let add_term t key data =
    { t with terms = Map.set t.terms ~key ~data:(fun modl -> const (data modl)) }
  ;;

  let add_general_term t key data =
    { t with terms = Map.set t.terms ~key ~data }
  ;;

  let add_sigture t key data =
    { t with sigtures = Map.set t.sigtures ~key ~data }
  ;;

  let add_modl t key (f, elab_creator) =
    { t with modls = Map.set t.modls ~key ~data:((fun modl -> const (f modl)), elab_creator) }
  ;;

  let add_general_modl t key data =
    { t with modls = Map.set t.modls ~key ~data }
  ;;

  let merge t1 t2 =
    { typs = merge_maps t1.typs t2.typs
    ; tags = merge_maps t1.tags t2.tags
    ; terms = merge_maps t1.terms t2.terms
    ; sigtures = merge_maps t1.sigtures t2.sigtures
    ; modls = merge_maps t1.modls t2.modls
    }
  ;;

  let apply t modl =
    { Elab.
      typs = Map.map ~f:(fun f -> f modl) t.typs
    ; tags = Map.map ~f:(fun f -> f modl) t.tags
    ; terms = Map.map ~f:(fun f -> f modl) t.terms
    ; sigtures =
        Map.map ~f:(fun (f, foo_sigture) -> (f modl, foo_sigture)) t.sigtures
    ; modls =
        Map.map ~f:(fun (f, elab_sigture) -> (f modl, elab_sigture)) t.modls
    }
  ;;
end

and Elab_sigture : sig
  type t =
    | Body of Elab_creator.t
    | Arrow of Foo_sigture.t * t
  [@@deriving sexp_of]
end = struct
  type t =
    | Body of Elab_creator.t
    | Arrow of Foo_sigture.t * t
  [@@deriving sexp_of]
end

and Foo_sigture : sig
  type t =
    | Body of Foo.t
    | Arrow of t * t
  [@@deriving sexp_of]
end = struct
  type t =
    | Body of Foo.t
    | Arrow of t * t
  [@@deriving sexp_of]
end

module Internal : sig
  type t =
    { typs : T.Kind.t T.Typ.Var.Map.t
    ; tags : (T.Typ.t * T.Typ.t option) T.Tag.Var.Map.t
    ; terms : T.Typ.t T.Term.Var.Map.t
    ; modls : T.Sigture.t T.Modl.Var.Map.t
    }
  [@@deriving sexp_of]

  val empty : t
  val add_typ : t -> T.Typ.Var.t -> T.Kind.t -> t
  val add_tag : t -> T.Tag.Var.t -> T.Typ.t * T.Typ.t option -> t
  val add_term : t -> T.Term.Var.t -> T.Typ.t -> t
  val add_modl : t -> T.Modl.Var.t -> T.Sigture.t -> t
  val merge : t -> t -> t
end = struct
  type t =
    { typs : T.Kind.t T.Typ.Var.Map.t
    ; tags : (T.Typ.t * T.Typ.t option) T.Tag.Var.Map.t
    ; terms : T.Typ.t T.Term.Var.Map.t
    ; modls : T.Sigture.t T.Modl.Var.Map.t
    }
  [@@deriving sexp_of]

  let empty =
    { typs = T.Typ.Var.Map.empty
    ; tags = T.Tag.Var.Map.empty
    ; terms = T.Term.Var.Map.empty
    ; modls = T.Modl.Var.Map.empty
    }
  ;;

  let add_typ t key data =
    { t with typs = Map.set t.typs ~key ~data }
  ;;

  let add_tag t key data =
    { t with tags = Map.set t.tags ~key ~data }
  ;;

  let add_term t key data =
    { t with terms = Map.set t.terms ~key ~data }
  ;;

  let add_modl t key data =
    { t with modls = Map.set t.modls ~key ~data }
  ;;

  let merge t1 t2 =
    { typs = merge_maps t1.typs t2.typs
    ; tags = merge_maps t1.tags t2.tags
    ; terms = merge_maps t1.terms t2.terms
    ; modls = merge_maps t1.modls t2.modls
    }
  ;;
end

type t =
  { fixity : Fixity.t
  ; elab : Elab.t
  ; internal : Internal.t
  }
[@@deriving sexp_of]

let empty =
  { fixity = Fixity.empty
  ; elab = Elab.empty
  ; internal = Internal.empty
  }
;;

let merge t1 t2 =
  { fixity = Fixity.merge t1.fixity t2.fixity
  ; elab = Elab.merge t1.elab t2.elab
  ; internal = Internal.merge t1.internal t2.internal
  }
;;
