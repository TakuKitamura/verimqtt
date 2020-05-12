module TestDecodingPackets

open Main
open FStar.HyperStack.ST
open LowStar.Printf
open LowStar.BufferOps

module T = Testing
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32

#set-options "--max_ifuel 0 --max_fuel 0 --z3rlimit 30"

inline_for_extraction noextract
let (!$) = C.String.of_literal

val main : u:unit -> St C.exit_code
let main () =
    T.test_start !$"TestDecodingPackets";
    let decoding_packets: B.buffer U8.t = B.malloc HyperStack.root 0uy 4ul in
    let bytes_length: U8.t = 1uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0x00" 0ul r;

    decoding_packets.(0ul) <- 0x7fuy;
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0x7F" 127ul r;

    decoding_packets.(0ul) <- 0x80uy;
    decoding_packets.(1ul) <- 0x01uy;
    let bytes_length: U8.t = 2uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0x80, 0x01" 128ul r;

    decoding_packets.(0ul) <- 0xffuy;
    decoding_packets.(1ul) <- 0x7fuy;
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0xFF, 0x7F" 16383ul r;

    decoding_packets.(0ul) <- 0x80uy;
    decoding_packets.(1ul) <- 0x80uy;
    decoding_packets.(2ul) <- 0x01uy;
    let bytes_length: U8.t = 3uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0x80, 0x80, 0x01" 16384ul r;


    decoding_packets.(0ul) <- 0xffuy;
    decoding_packets.(1ul) <- 0xffuy;
    decoding_packets.(2ul) <- 0x7fuy;
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0xFF, 0xFF, 0x7F" 2097151ul r;

    decoding_packets.(0ul) <- 0x80uy;
    decoding_packets.(1ul) <- 0x80uy;
    decoding_packets.(2ul) <- 0x80uy;
    decoding_packets.(3ul) <- 0x01uy;
    let bytes_length: U8.t = 4uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0x80, 0x80, 0x80, 0x01" 2097152ul r;

    decoding_packets.(0ul) <- 0xffuy;
    decoding_packets.(1ul) <- 0xffuy;
    decoding_packets.(2ul) <- 0xffuy;
    decoding_packets.(3ul) <- 0x7fuy;
    let bytes_length: U8.t = 4uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"valid: 0xFF, 0xFF, 0xFF, 0x7F" 268435455ul r;

    let decoding_packets: B.buffer U8.t = B.malloc HyperStack.root 0uy 4ul in
    decoding_packets.(0ul) <- 0x80uy;
    let bytes_length: U8.t = 1uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"invalid: 0x80" max_u32 r;

    decoding_packets.(0ul) <- 0x80uy;
    decoding_packets.(1ul) <- 0x00uy;
    let bytes_length: U8.t = 2uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"invalid: 0x80, 0x00" max_u32 r;

    decoding_packets.(0ul) <- 0x7fuy;
    decoding_packets.(1ul) <- 0x01uy;
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"invalid: 0x7F, 0x01" max_u32 r;

    decoding_packets.(0ul) <- 0xffuy;
    decoding_packets.(1ul) <- 0x80uy;
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"invalid: 0xFF, 0x80" max_u32 r;

    decoding_packets.(0ul) <- 0x80uy;
    decoding_packets.(1ul) <- 0x7fuy;
    decoding_packets.(2ul) <- 0x01uy;
    let bytes_length: U8.t = 3uy in
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"invalid: 0x8F, 0x7F, 0x01" max_u32 r;

    decoding_packets.(0ul) <- 0xffuy;
    decoding_packets.(1ul) <- 0xffuy;
    decoding_packets.(2ul) <- 0x80uy;
    let r: U32.t =
        decodeing_variable_bytes decoding_packets bytes_length in
    T.eq_u32 !$"invalid: 0xFF, 0xFF, 0x80" max_u32 r;

    T.test_end ();
    C.EXIT_SUCCESS