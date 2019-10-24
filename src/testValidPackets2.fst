module TestValidPackets2

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

let valid_subscribe_packet_test u =
    let request = B.malloc HyperStack.root 0uy 17ul in
        request.(0ul) <- 0x82uy;
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

        T.eq_str !$"Valid SUBSCRIBE Packet message_name check" !$"SUBSCRIBE" s.message_name;
        T.eq_u8 !$"Valid SUBSCRIBE Packet message_type check" 8uy s.message_type;
        T.eq_u8 !$"Valid SUBSCRIBE Packet flag check" 2uy s.flags.flag;
        T.eq_u8 !$"Valid SUBSCRIBE Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid SUBSCRIBE Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid SUBSCRIBE Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid SUBSCRIBE Packet remaining_length check" 15ul s.remaining_length;
        T.eq_str !$"Valid SUBSCRIBE Packet error_message check" !$"" s.error_message;

    B.free request

let valid_suback_packet_test u =
    let request = B.malloc HyperStack.root 0uy 5ul in
        request.(0ul) <- 0x90uy;
        request.(1ul) <- 0x03uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x01uy;
        request.(4ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 5ul in
        T.eq_str !$"Valid SUBACK Packet message_name check" !$"SUBACK" s.message_name;
        T.eq_u8 !$"Valid SUBACK Packet message_type check" 9uy s.message_type;
        T.eq_u8 !$"Valid SUBACK Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid SUBACK Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid SUBACK Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid SUBACK Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid SUBACK Packet remaining_length check" 3ul s.remaining_length;
        T.eq_str !$"Valid SUBACK Packet error_message check" !$"" s.error_message;

    B.free request

let valid_pingreq_packet_test u =
    let request = B.malloc HyperStack.root 0uy 2ul in
        request.(0ul) <- 0xC0uy;
        request.(1ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 2ul in
        T.eq_str !$"Valid PINGREQ Packet message_name check" !$"PINGREQ" s.message_name;
        T.eq_u8 !$"Valid PINGREQ Packet message_type check" 12uy s.message_type;
        T.eq_u8 !$"Valid PINGREQ Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PINGREQ Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PINGREQ Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PINGREQ Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PINGREQ Packet remaining_length check" 0ul s.remaining_length;
        T.eq_str !$"Valid PINGREQ Packet error_message check" !$"" s.error_message;

    B.free request

let valid_pingresp_packet_test u =
    let request = B.malloc HyperStack.root 0uy 2ul in
        request.(0ul) <- 0xD0uy;
        request.(1ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 2ul in
        T.eq_str !$"Valid PINGRESP Packet message_name check" !$"PINGRESP" s.message_name;
        T.eq_u8 !$"Valid PINGRESP Packet message_type check" 13uy s.message_type;
        T.eq_u8 !$"Valid PINGRESP Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PINGRESP Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PINGRESP Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PINGRESP Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PINGRESP Packet remaining_length check" 0ul s.remaining_length;
        T.eq_str !$"Valid PINGRESP Packet error_message check" !$"" s.error_message;

    B.free request

let valid_disconnect_packet_test u =
    let request = B.malloc HyperStack.root 0uy 2ul in
        request.(0ul) <- 0xE0uy;
        request.(1ul) <- 0x00uy;

    let s : struct_fixed_header = parse request 2ul in
        T.eq_str !$"Valid DISCONNECT Packet message_name check" !$"DISCONNECT" s.message_name;
        T.eq_u8 !$"Valid DISCONNECT Packet message_type check" 14uy s.message_type;
        T.eq_u8 !$"Valid DISCONNECT Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid DISCONNECT Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid DISCONNECT Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid DISCONNECT Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid DISCONNECT Packet remaining_length check" 1ul s.remaining_length;
        T.eq_str !$"Valid DISCONNECT Packet error_message check" !$"" s.error_message;

    B.free request

val main : u:unit -> St C.exit_code
let main () =
    T.test_start !$"TestValidPackets2";
    valid_subscribe_packet_test ();
    valid_suback_packet_test ();
    valid_pingreq_packet_test ();
    valid_pingresp_packet_test ();
    valid_disconnect_packet_test ();
    T.test_end ();
    C.EXIT_SUCCESS