open Core
include Int.Replace_polymorphic_compare

let unzip3 l =
  List.fold_right l ~init:([], [], [])
    ~f:(fun (x, y, z) (l1, l2, l3) -> (x::l1, y::l2, z::l3))
;;

let unzip4 l =
  List.fold_right l ~init:([], [], [], [])
    ~f:(fun (x1, x2, x3, x4) (l1, l2, l3, l4) ->
      (x1::l1, x2::l2, x3::l3, x4::l4))
;;
