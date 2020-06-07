module Playground

module B = LowStar.Buffer
module UT = Utils
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack.ST
open LowStar.BufferOps
open LowStar.Printf
open FStar.Int.Cast
open C.String
open C

val min_packet_size: U32.t
let min_packet_size = 2ul

val max_packet_size: U32.t
let max_packet_size = 268435460ul

val max_request_size: U32.t
let max_request_size = 268435461ul

type type_packet_size =
  packet_size:
    U32.t{U32.v packet_size >= U32.v min_packet_size && U32.v packet_size <= U32.v max_packet_size}

#set-options "--initial_fuel 10000 --initial_ifuel 10000"
val loop (x: B.buffer U8.t) (index: U32.t{U32.v index <= 11})  : U32.t
let rec loop x index = 
  if U32.eq index 11ul then
    0ul
  else if U32.(index <=^ 10ul) then
    let abc: (index: U32.t{U32.v index <= 11}) = U32.(index +^ 1ul) in
    if U32.(abc <=^ 11ul) then
      loop x abc
    else
      3ul
  else
    1ul


val playground (request: B.buffer U8.t) (packet_size: type_packet_size):
  Stack C.exit_code
    (requires (fun h ->
      B.live h request /\
      B.length request <= U32.v max_request_size /\
      UT.zero_terminated_buffer_u8 h request /\
      (B.length request - 1) = U32.v packet_size))
    (ensures (fun h0 _ h1 -> B.live h0 request /\ B.live h1 request))
let playground request packet_size =
  push_frame ();
  let v = request.(0ul) in
  print_u8 v;
  pop_frame ();
  C.EXIT_SUCCESS