open! Core
open! Import

type t = int * int [@@deriving compare, equal, hash, sexp_of]

val dist_euclidean : t -> t -> float
val dist_manhattan : t -> t -> int
val add : t -> Dir.t -> t
val adjacent : t -> t list
