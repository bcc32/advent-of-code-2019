open! Core
open! Async
open! Import
open Intcode

let input () = Reader.file_contents "input" >>| Program.of_string

let a () =
  let%bind program = input () in
  Pipe.create_reader ~close_on_exception:true (fun writer ->
    Program.run program ~input:(Pipe.of_list [ 1 ]) ~output:writer)
  |> Pipe.iter_without_pushback ~f:(printf "%d\n")
;;

let%expect_test "a" =
  let%bind () = a () in
  [%expect {| 2662308295 |}]
;;

let b () =
  let%bind program = input () in
  Pipe.create_reader ~close_on_exception:true (fun writer ->
    Program.run program ~input:(Pipe.of_list [ 2 ]) ~output:writer)
  |> Pipe.iter_without_pushback ~f:(printf "%d\n")
;;

let%expect_test "b" =
  let%bind () = b () in
  [%expect {| 63441 |}]
;;