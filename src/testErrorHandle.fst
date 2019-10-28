module TestErrorHandle

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

val remaining_length_error_check1: u:unit -> St unit
let remaining_length_error_check1 u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 5ul in
        request.(0ul) <- 0x30uy;
        request.(1ul) <- 0xD4uy;
        request.(2ul) <- 0x01uy;
        request.(3ul) <- 0x00uy;
        request.(4ul) <- 0x0Auy;

    let s : struct_fixed_header = parse request 5ul in
        T.eq_str !$"remaining_length error check1" !$"remaining_length is invalid." s.error_message;
B.free request

val remaining_length_error_check2: u:unit -> St unit
let remaining_length_error_check2 u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 1ul in

    let s : struct_fixed_header = parse request 1ul in
        T.eq_str !$"remaining_length error check2" !$"remaining_length is invalid." s.error_message;
B.free request

val message_type_error_check: u:unit -> St unit
let message_type_error_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0x00uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"message_type_error_check" !$"message_type is invalid." s.error_message;
B.free request

// val message_name_error_check: u:unit -> St unit
// let message_name_error_check u =
//     let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 2ul in
//         request.(0ul) <- 0x00uy;
//         request.(1ul) <- 0x00uy;

//     let s : struct_fixed_header = parse request 2ul in
//         T.eq_str !$"message_name_error_check" !$"message_name is invalid." s.error_message;
// B.free request

val flag_error_check: u:unit -> St unit
let flag_error_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 17ul in
        request.(0ul) <- 0x80uy;
        request.(1ul) <- 0x0Fuy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x01uy;
        request.(4ul) <- 0x00uy;
        request.(5ul) <- 0x0Auy;
        request.(6ul) <- 0x74uy;
        request.(7ul) <- 0x65uy;
        request.(8ul) <- 0x73uy;
        request.(9ul) <- 0x74uy;
        request.(10ul) <- 0x2Fuy;
        request.(11ul) <- 0x74uy;
        request.(12ul) <- 0x6Fuy;
        request.(13ul) <- 0x70uy;
        request.(14ul) <- 0x69uy;
        request.(15ul) <- 0x63uy;
        request.(16ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 17ul in
        T.eq_str !$"invalid Packet error_message check" !$"flag is invalid." s.error_message;
B.free request

val main : u:unit -> St C.exit_code
let main () =
    T.test_start !$"TestErrorHandle";
    remaining_length_error_check1 ();
    remaining_length_error_check2 ();
    message_type_error_check ();
    // message_name_error_check ();
    flag_error_check ();

    T.test_end ();
    C.EXIT_SUCCESS