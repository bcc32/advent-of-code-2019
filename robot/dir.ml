open! Core
open! Import

type t =
  | N
  | E
  | S
  | W
[@@deriving enumerate, equal, sexp_of]

let opp = function
  | N -> S
  | E -> W
  | S -> N
  | W -> E
;;

let turn t which_way =
  match which_way with
  | `Left ->
    (match t with
     | N -> W
     | W -> S
     | S -> E
     | E -> N)
  | `Right ->
    (match t with
     | N -> E
     | E -> S
     | S -> W
     | W -> N)
;;

let of_char_urdl_exn = function
  | 'U' -> N
  | 'R' -> E
  | 'D' -> S
  | 'L' -> W
  | char -> raise_s [%message "Invalid URDL direction" (char : char)]
;;
