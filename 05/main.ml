open! Core
open! Async
open! Import
open Intcode

let a () =
  let%bind program = Reader.file_contents "input" >>| Program.of_string in
  match Program.Async.run program with
  | { input; output; done_ } ->
    Pipe.write_without_pushback input 1;
    let%bind () = Pipe.iter_without_pushback output ~f:(printf "%d\n") in
    done_
;;

let%expect_test "a" =
  let%bind () = a () in
  [%expect {|
    0
    0
    0
    0
    0
    0
    0
    0
    0
    15426686 |}]
;;

let b () =
  let%bind program = Reader.file_contents "input" >>| Program.of_string in
  match Program.Async.run program with
  | { input; output; done_ } ->
    Pipe.write_without_pushback input 5;
    let%bind () = Pipe.iter_without_pushback output ~f:(printf "%d\n") in
    done_
;;

let%expect_test "b" =
  let%bind () = b () in
  [%expect {| 11430197 |}]
;;
