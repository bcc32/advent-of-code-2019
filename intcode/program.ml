open! Core
open! Async
open! Import

(* Use 64-bit ints as memory. *)
let sizeof_elt = 8

type t =
  { mutable memory : Bigstring.Hexdump.t
  ; mutable relative_base : int
  ; mutable pc : int
  ; input : int Queue.t
  }
[@@deriving sexp_of]

module Snapshot = struct
  type program = t

  type t =
    { memory : Bigstring.t
    ; relative_base : int
    ; pc : int
    }
  [@@deriving sexp_of]

  let instantiate { memory; relative_base; pc } : program =
    { memory = Bigstring.copy memory; relative_base; pc; input = Queue.create () }
  ;;
end

let of_string source_code =
  let memory_array =
    source_code
    |> String.strip
    |> String.split ~on:','
    |> Array.of_list_map ~f:Int.of_string
  in
  let memory = Bigstring.create (Array.length memory_array * sizeof_elt) in
  Array.iteri memory_array ~f:(fun i x ->
    Bigstring.unsafe_set_int64_le memory ~pos:(i * sizeof_elt) x);
  { memory; relative_base = 0; pc = 0; input = Queue.create () }
;;

(* TODO: Loosen restrictions on pending input for backup and restore. *)
let snapshot t : Snapshot.t =
  if not (Queue.is_empty t.input)
  then raise_s [%message "Program.copy: tried to copy a program with pending input"];
  { memory = Bigstring.copy t.memory; relative_base = t.relative_base; pc = t.pc }
;;

let restore dst ~from:(src : Snapshot.t) =
  if not (Queue.is_empty dst.input)
  then raise_s [%message "Program.restore: tried to restore a program with pending input"];
  let gap = Bigstring.length dst.memory - Bigstring.length src.memory in
  (match Int.sign gap with
   | Neg -> dst.memory <- Bigstring.copy src.memory
   | Zero | Pos ->
     Bigstring.unsafe_blit
       ~src:src.memory
       ~src_pos:0
       ~dst:dst.memory
       ~dst_pos:0
       ~len:(Bigstring.length src.memory);
     Bigstring.memset dst.memory ~pos:(Bigstring.length src.memory) ~len:gap '\x00');
  dst.pc <- src.pc;
  dst.relative_base <- src.relative_base
;;

module Infix = struct
  let ( .$() ) t pos = Bigstring.get_int64_le_exn t.memory ~pos:(pos * sizeof_elt)
  let ( .$()<- ) t pos x = Bigstring.set_int64_le t.memory ~pos:(pos * sizeof_elt) x
end

open Infix

module Insn = struct
  let[@inline always] opcode t = t mod 100
  let[@inline always] mode1 t = t / 100 mod 10
  let[@inline always] mode2 t = t / 1000 mod 10
  let[@inline always] mode3 t = t / 10_000 mod 10
end

let[@inline always] get t ~arg ~mode =
  let try_get index =
    try t.$(index) with
    | _ -> 0
  in
  match mode with
  | 0 -> try_get arg
  | 1 -> arg
  | 2 -> try_get (arg + t.relative_base)
  | mode -> invalid_argf "get: invalid mode: %d" mode ()
;;

let[@cold] raise_set_invalid_addressing_mode ~mode =
  raise_s [%message "Cannot set using addressing mode" (mode : int)]
;;

let set t ~arg ~mode ~value =
  let grow index =
    let new_array =
      let len = Int.max ((index + 1) * sizeof_elt) (Bigstring.length t.memory * 2) in
      Bigstring.create len
    in
    Bigstring.blit
      ~src:t.memory
      ~src_pos:0
      ~dst:new_array
      ~dst_pos:0
      ~len:(Bigstring.length t.memory);
    t.memory <- new_array
  in
  let try_set index value =
    try t.$(index) <- value with
    | _ ->
      grow index;
      t.$(index) <- value
  in
  match mode with
  | 0 -> try_set arg value
  | 1 -> raise_set_invalid_addressing_mode ~mode
  | 2 -> try_set (arg + t.relative_base) value
  | mode -> invalid_argf "set: invalid mode: %d" mode ()
;;

module Sync = struct
  module Step_result = struct
    type t =
      | Done
      | Need_input
      | Output of int
  end

  let[@cold] raise_unrecognized_opcode t ~code =
    raise_s [%message "unrecognized opcode" (code : int) (t : t)]
  ;;

  let rec step ({ memory = _; relative_base; pc; input } as t) : Step_result.t =
    let insn = t.$(pc) in
    let[@inline always] x () =
      let arg = t.$(pc + 1) in
      get t ~arg ~mode:(Insn.mode1 insn)
    in
    let[@inline always] y () =
      let arg = t.$(pc + 2) in
      get t ~arg ~mode:(Insn.mode2 insn)
    in
    let[@inline always] set_z value =
      let arg = t.$(pc + 3) in
      set t ~arg ~mode:(Insn.mode3 insn) ~value
    in
    match Insn.opcode insn with
    | 1 ->
      set_z (x () + y ());
      t.pc <- pc + 4;
      step t
    | 2 ->
      set_z (x () * y ());
      t.pc <- pc + 4;
      step t
    | 3 ->
      let arg1 = t.$(pc + 1) in
      (match Queue.dequeue input with
       | None -> Need_input
       | Some input ->
         set t ~arg:arg1 ~mode:(Insn.mode1 insn) ~value:input;
         t.pc <- pc + 2;
         step t)
    | 4 ->
      let x = x () in
      t.pc <- pc + 2;
      Output x
    | 5 ->
      t.pc <- (if x () <> 0 then y () else pc + 3);
      step t
    | 6 ->
      t.pc <- (if x () = 0 then y () else pc + 3);
      step t
    | 7 ->
      set_z (Bool.to_int (x () < y ()));
      t.pc <- pc + 4;
      step t
    | 8 ->
      set_z (Bool.to_int (x () = y ()));
      t.pc <- pc + 4;
      step t
    | 9 ->
      t.relative_base <- relative_base + x ();
      t.pc <- pc + 2;
      step t
    | 99 -> Done
    | code -> raise_unrecognized_opcode t ~code
  ;;

  let run_without_input_exn t ~f =
    let rec loop () =
      match step t with
      | Done -> ()
      | Need_input -> raise_s [%message "Program.Sync.run_without_input_exn: need input"]
      | Output x ->
        f x;
        loop ()
    in
    loop ()
  ;;

  let provide_input' t ~from = Queue.blit_transfer () ~src:from ~dst:t.input
  let provide_input t input = Queue.enqueue t.input input
end

module Async = struct
  open Eager_deferred.Let_syntax

  module Run = struct
    type t =
      { input : int Pipe.Writer.t
      ; output : int Pipe.Reader.t
      ; done_ : unit Deferred.t
      }
  end

  let run t =
    let input_r, input_w = Pipe.create () in
    let output_r, output_w = Pipe.create () in
    let done_ =
      Deferred.repeat_until_finished () (fun () ->
        match Sync.step t with
        | Done -> return (`Finished ())
        | Need_input ->
          (match%map Pipe.read' input_r with
           | `Eof ->
             raise_s [%message "Program.Async.run: Program received EOF on input"]
           | `Ok queue ->
             Sync.provide_input' t ~from:queue;
             `Repeat ())
        | Output x ->
          let%map () = Pipe.write output_w x in
          `Repeat ())
    in
    don't_wait_for
      (let%map () = done_ in
       Pipe.close_read input_r;
       Pipe.close output_w);
    { Run.input = input_w; output = output_r; done_ }
  ;;
end
