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

val message_type_error_check1: u:unit -> St unit
let message_type_error_check1 u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0x00uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"message type_error check1" define_error_message_type_invalid s.error.message;
B.free request

val message_type_error_check2: u:unit -> St unit
let message_type_error_check2 u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 1ul in

    let s : struct_fixed_header = parse request 1ul in
        T.eq_str !$"message type_error check2" define_error_message_type_invalid s.error.message;
B.free request


val invalid_pubrel_flag_check: u:unit -> St unit
let invalid_pubrel_flag_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 4ul in
            request.(0ul) <- 0x60uy;
            request.(1ul) <- 0x02uy;
            request.(2ul) <- 0x00uy;
            request.(3ul) <- 0x01uy;
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"pubrel flag is invalid" define_error_flag_invalid s.error.message;
    B.free request

val invalid_subscribe_flag_check: u:unit -> St unit
let invalid_subscribe_flag_check u =
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
        T.eq_str !$"subscribe flag is invalid" define_error_flag_invalid s.error.message;
B.free request

val invalid_unsubscribe_flag_check: u:unit -> St unit
let invalid_unsubscribe_flag_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 16ul in
        request.(0ul) <- 0xA0uy;
        request.(1ul) <- 0x0Euy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x02uy;
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

    let s : struct_fixed_header = parse request 16ul in
        T.eq_str !$"unsubscribe flag is invalid" define_error_flag_invalid s.error.message;
B.free request

val invalid_unsuback_flag_check: u:unit -> St unit
let invalid_unsuback_flag_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0xB2uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x02uy;

    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"unsuback flag is invalid" define_error_flag_invalid s.error.message;
B.free request

val remaining_length_error_check: u:unit -> St unit
let remaining_length_error_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 5ul in
        request.(0ul) <- 0x30uy;
        request.(1ul) <- 0xD4uy;
        request.(2ul) <- 0x01uy;
        request.(3ul) <- 0x00uy;
        request.(4ul) <- 0x0Auy;

    let s : struct_fixed_header = parse request 5ul in
        T.eq_str !$"remaining_length error check" define_error_remaining_length_invalid s.error.message;
B.free request

val invalid_qos_flag_check: u:unit -> St unit
let invalid_qos_flag_check u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 24ul in
        request.(0ul) <- 0x3Fuy;
        request.(1ul) <- 0x16uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x0Auy;
        request.(4ul) <- 0x74uy;
        request.(5ul) <- 0x65uy;
        request.(6ul) <- 0x73uy;
        request.(7ul) <- 0x74uy;
        request.(8ul) <- 0x2Fuy;
        request.(9ul) <- 0x74uy;
        request.(10ul) <- 0x6Fuy;
        request.(11ul) <- 0x70uy;
        request.(12ul) <- 0x69uy;
        request.(13ul) <- 0x63uy;
        request.(14ul) <- 0x68uy;
        request.(15ul) <- 0x65uy;
        request.(16ul) <- 0x6Cuy;
        request.(17ul) <- 0x6Cuy;
        request.(18ul) <- 0x6Fuy;
        request.(19ul) <- 0x20uy;
        request.(20ul) <- 0x6Duy;
        request.(21ul) <- 0x71uy;
        request.(22ul) <- 0x74uy;
        request.(23ul) <- 0x74uy;
    let s : struct_fixed_header = parse request 24ul in
        T.eq_str !$"invalid qos flag check" define_error_qos_flag_invalid s.error.message;
    B.free request

val main : u:unit -> St C.exit_code
let main () =
    T.test_start !$"TestErrorHandle";
    message_type_error_check1 ();
    message_type_error_check2 ();
    invalid_pubrel_flag_check ();
    invalid_subscribe_flag_check ();
    invalid_unsubscribe_flag_check ();
    invalid_unsuback_flag_check ();
    remaining_length_error_check ();
    invalid_qos_flag_check ();

    T.test_end ();
    C.EXIT_SUCCESS