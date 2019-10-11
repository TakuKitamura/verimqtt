module Main

module B = LowStar.Buffer
module M = LowStar.Modifies
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open LowStar.BufferOps
open LowStar.Printf

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8

// debug tool
assume val print_hex (i: U8.t{ 0 <= U8.v i /\ U8.v i <= 255}): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))
// ---

val normal_loop: src:B.buffer U8.t -> len:U32.t -> Stack C.exit_code
  (requires fun h0 -> B.live h0 src /\ B.length src = U32.v len )
  (ensures fun _ _ _ -> true)
let normal_loop src len =
  let inv h (i: nat) = B.live h src in
  let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v len }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let v : U8.t = src.(i) in
      print_hex v
  in
  C.Loops.for 0ul len inv body;
  (* return *) C.EXIT_SUCCESS

val parse (request: B.buffer U8.t) (len: U32.t):
  Stack C.exit_code 
    (requires (fun h ->
      B.live h request /\
      B.length request = U32.v len  ))
    (ensures (fun h0 _ h1 ->
      B.live h1 request))

let parse request len =
    push_frame ();
    let r = normal_loop request len in
    pop_frame ();
    C.EXIT_SUCCESS
