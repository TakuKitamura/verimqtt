module TestSliceByte

open Main
open FStar.HyperStack.ST
open LowStar.Printf
open LowStar.BufferOps

module T = Testing
module B = LowStar.Buffer
module U8 = FStar.UInt8

#set-options "--max_ifuel 0 --max_fuel 0 --z3rlimit 30"

inline_for_extraction noextract
let (!$) = C.String.of_literal

val main : u:unit -> Stack C.exit_code
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let main () =
    T.test_start !$"TestSliceByte";
    let ex1: U8.t = 0b01010101uy in
    let v:U8.t = slice_byte ex1 0uy 8uy in
        T.eq_u8 !$"v[0:8]" 0b01010101uy v;
    let v:U8.t = slice_byte ex1 1uy 7uy in
        T.eq_u8 !$"v[1:7]" 0b00101010uy v;
    let v:U8.t = slice_byte ex1 2uy 6uy in
        T.eq_u8 !$"v[2:6]" 0b00000101uy v;
    let v:U8.t = slice_byte ex1 3uy 5uy in
        T.eq_u8 !$"v[3:5]" 0b00000010uy v;
    let v:U8.t = slice_byte ex1 3uy 5uy in
        T.eq_u8 !$"v[3:5]" 0b11111111uy v;
    T.test_end ();
    C.EXIT_SUCCESS