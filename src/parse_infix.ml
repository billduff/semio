open! Core
open! Import

exception Internal_error

type precedence =
  | Less
  | Greater
[@@deriving sexp]

let group_infix
      (type a)
      (sexp_of_a : a -> Sexp.t)
      (is_infix : a -> bool)
      (convert : a -> 'b)
      (ap : 'b -> 'b -> 'b)
      (l : a list)
  : 'b list * a list =
  let (groups, ops) =
    List.partition_map
      ~f:(function
        | [x] ->
          if is_infix x
          then Second x
          else First [x]
        | l -> First l)
      (List.group l
         ~break:(fun x y ->
           if is_infix x && is_infix y
           then failwith "???replace with a better error message1"
           else is_infix x || is_infix y))
  in
  match Int.equal (List.length groups) (List.length ops + 1) with
  | true ->
    (List.map groups
       ~f:(fun group -> List.reduce_exn ~f:ap (List.map ~f:convert group)),
     ops)
  | false ->
    raise_s
      [%message
        "???replace with a better error message2"
          (l : a list)
          (groups : a list list)
          (ops : a list)]
;;

type 'a tree =
  | Empty
  | Node of 'a tree * 'a * 'a tree

let parse_infix
      (sexp_of_a : 'a -> Sexp.t)
      ~(is_infix : 'a -> bool)
      ~(precedence : 'a -> 'a -> precedence option)
      ~(convert : 'a -> 'b)
      ~(ap : 'b -> 'b -> 'b)
      (l : 'a list)
  : 'b =
  let (l', ops) = group_infix sexp_of_a is_infix convert ap l in
  let trees = List.map ops ~f:(fun op -> Node (Empty, op, Empty)) in
  let rec merge l r =
    match (l, r) with
    | (Empty, t) | (t, Empty) -> t
    | (Node (ll, lop, lr), Node (rl, rop, rr)) ->
      (match precedence lop rop with
       | None -> failwith "???replace with a better error message3"
       | Some Less -> Node (ll, lop, merge lr r)
       | Some Greater -> Node (merge l rl, rop, rr))
  in
  let tree = List.fold_right ~f:merge ~init:Empty trees in
  let rec apply_tree t es =
    match (t, es) with
    | (Empty, []) -> raise Internal_error
    | (Empty, e::es) -> (e, es)
    | (Node (l, op, r), es) ->
      let (le, es') = apply_tree l es in
      let (re, es'') = apply_tree r es' in
      (ap (ap (convert op) le) re, es'')
  in
  let (e, _) = apply_tree tree l' in
  e
;;

let%expect_test _ =
  let is_atomic e =
    not (String.mem e ' ')
  in
  let module E = struct
    type op = Plus | Minus | Times | Div | Exp
    let op_of_string = function
      | "+" -> Plus
      | "-" -> Minus
      | "*" -> Times
      | "/" -> Div
      | "^" -> Exp
      | _ -> failwith "invalid op"
    let string_of_op = function
      | Plus -> "+"
      | Minus -> "-"
      | Times -> "*"
      | Div -> "/"
      | Exp -> "^"
    type t =
      | Op of op
      | Ap1 of op * t
      | Ap2 of op * t * t
      | Other of string
    let rec to_string t =
      match t with
      | Op _ | Ap1 _ -> assert false
      | Other s -> s
      | Ap2 (op, t1, t2) ->
        sprintf "%s %s %s"
          (let s1 = to_string t1 in
           if is_atomic s1
           then s1
           else sprintf "(%s)" s1)
          (string_of_op op)
          (let s2 = to_string t2 in
           if is_atomic s2
           then s2
           else sprintf "(%s)" s2)
  end
  in
  parse_infix
    [%sexp_of: string]
    ~is_infix:(fun e ->
      try ignore (E.op_of_string e : E.op); true
      with _ -> false)
    ~precedence:(fun l r ->
      match (l, r) with
      | (("+" | "-"), ("+" | "-")) -> Some Greater
      | (("+" | "-"), _) -> Some Less
      | (("*" | "/"), "^") -> Some Less
      | (("*" | "/"), _) -> Some Greater
      | ("^", _) -> Some Greater
      | _ -> assert false)
    ~convert:(fun e ->
      try E.Op (E.op_of_string e)
      with _ -> Other e)
    ~ap:(fun f x ->
      match f with
      | Op op -> Ap1 (op, x)
      | Ap1 (op, y) -> Ap2 (op, y, x)
      | _ -> assert false)
    (String.split ~on:' ' "a + b * c / d ^ n - 5 - 2 ^ 2")
  |> E.to_string
  |> printf "%s\n%!";
  [%expect {| ((a + ((b * c) / (d ^ n))) - 5) - (2 ^ 2) |}]
;;

let%expect_test _ =
  let fixity =
    String.Map.of_alist_exn
      [ ("->", String.Map.of_alist_exn [("->", Less); ("*", Less)])
      ; ("*", String.Map.of_alist_exn [("->", Greater); ("*", Greater)])
      ]
  in
  parse_infix
    [%sexp_of: string]
    ~is_infix:(String.Map.mem fixity)
    ~precedence:(fun name1 name2 ->
      String.Map.find (String.Map.find_exn fixity name1) name2)
    ~convert:(ident)
    ~ap:(fun l r -> sprintf "(%s %s)" l r)
    ["t"; "a"; "->"; "Key.t"; "->"; "a"; "->"; "t"; "a"]
  |> printf "%s\n%!";
  [%expect {| ((-> (t a)) ((-> Key.t) ((-> a) (t a)))) |}]
;;
