module TestValidPackets1

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

// let new_line () = print_string "\n"
// let print x =  C.String.print x

// val print_struct_fixed_header: s:struct_fixed_header -> St unit
// let print_struct_fixed_header s =
//     print !$"message_name: "; print s.message_name; new_line ();
//     print !$"message_type: 0x"; print_hex s.message_type; new_line ();
//     print !$"flag: 0x"; print_hex s.flags.flag; new_line ();
//     print !$"dup_flag: 0x"; print_hex s.flags.dup_flag; new_line ();
//     print !$"qos_flag: 0x"; print_hex s.flags.qos_flag; new_line ();
//     print !$"retain_flag: 0x"; print_hex s.flags.retain_flag; new_line ();
//     print !$"remaining_length: "; print_u32 s.remaining_length; new_line ();
//     print !$"error_message: "; print s.error_message; new_line ()

val valid_connect_packet_test: u:unit -> St unit
let valid_connect_packet_test u =
    let request = B.malloc HyperStack.root 0uy 37ul in
        request.(0ul) <- 0x10uy;
        request.(1ul) <- 0x23uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x04uy;
        request.(4ul) <- 0x4Duy;
        request.(5ul) <- 0x51uy;
        request.(6ul) <- 0x54uy;
        request.(7ul) <- 0x54uy;
        request.(8ul) <- 0x04uy;
        request.(9ul) <- 0x02uy;
        request.(10ul) <- 0x00uy;
        request.(11ul) <- 0x3Cuy;
        request.(12ul) <- 0x00uy;
        request.(13ul) <- 0x17uy;
        request.(14ul) <- 0x6Duy;
        request.(15ul) <- 0x6Fuy;
        request.(16ul) <- 0x73uy;
        request.(17ul) <- 0x71uy;
        request.(18ul) <- 0x2Duy;
        request.(19ul) <- 0x6Auy;
        request.(20ul) <- 0x41uy;
        request.(21ul) <- 0x77uy;
        request.(22ul) <- 0x6Buy;
        request.(23ul) <- 0x70uy;
        request.(24ul) <- 0x43uy;
        request.(25ul) <- 0x56uy;
        request.(26ul) <- 0x6Buy;
        request.(27ul) <- 0x39uy;
        request.(28ul) <- 0x4Duy;
        request.(29ul) <- 0x71uy;
        request.(30ul) <- 0x76uy;
        request.(31ul) <- 0x41uy;
        request.(32ul) <- 0x54uy;
        request.(33ul) <- 0x42uy;
        request.(34ul) <- 0x4Duy;
        request.(35ul) <- 0x58uy;
        request.(36ul) <- 0x62uy;
    let s : struct_fixed_header = parse request 37ul in
        T.eq_str !$"Valid CONNECT Packet message_name check" !$"CONNECT" s.message_name;
        T.eq_u8 !$"Valid CONNECT Packet message_type check" 1uy s.message_type;
        T.eq_u8 !$"Valid CONNECT Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid CONNECT Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid CONNECT Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid CONNECT Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid CONNECT Packet remaining_length check" 35ul s.remaining_length;
        T.eq_str !$"Valid CONNECT Packet error_message check" !$"" s.error_message;
    B.free request

val valid_connack_packet_test: u:unit -> St unit
let valid_connack_packet_test u =
    let request = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0x20uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x00uy;
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid CONNACK Packet message_name check" !$"CONNACK" s.message_name ;
        T.eq_u8 !$"Valid CONNACK Packet message_type check" 2uy s.message_type;
        T.eq_u8 !$"Valid CONNACK Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid CONNACK Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid CONNACK Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid CONNACK Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid CONNACK Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid CONNACK Packet error_message check" !$"" s.error_message;
    B.free request

val valid_publish_packet_test: u:unit -> St unit
let valid_publish_packet_test u =
    let request = B.malloc HyperStack.root 0uy 24ul in
        request.(0ul) <- 0x30uy;
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
        T.eq_str !$"Valid PUBLISH Packet message_name check" !$"PUBLISH" s.message_name;
        T.eq_u8 !$"Valid PUBLISH Packet message_type check" 3uy s.message_type;
        T.eq_u8 !$"Valid PUBLISH Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBLISH Packet dup_flag check" 0uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBLISH Packet qos_flag check" 0uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBLISH Packet retain_flag check" 0uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBLISH Packet remaining_length check" 22ul s.remaining_length;
        T.eq_str !$"Valid PUBLISH Packet error_message check" !$"" s.error_message;
    B.free request

let valid_puback_packet_test u =
    let request = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0x40uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x01uy;

    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBACK Packet message_name check" !$"PUBACK" s.message_name;
        T.eq_u8 !$"Valid PUBACK Packet message_type check" 4uy s.message_type;
        T.eq_u8 !$"Valid PUBACK Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBACK Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBACK Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBACK Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBACK Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBACK Packet error_message check" !$"" s.error_message;
    B.free request

let valid_pubrec_packet_test u =
    let request = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0x50uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x01uy;
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBREC Packet message_name check" !$"PUBREC" s.message_name;
        T.eq_u8 !$"Valid PUBREC Packet message_type check" 5uy s.message_type;
        T.eq_u8 !$"Valid PUBREC Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBREC Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBREC Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBREC Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBREC Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBREC Packet error_message check" !$"" s.error_message;
    B.free request

let valid_pubrel_packet_test u =
    let request = B.malloc HyperStack.root 0uy 4ul in
            request.(0ul) <- 0x62uy;
            request.(1ul) <- 0x02uy;
            request.(2ul) <- 0x00uy;
            request.(3ul) <- 0x01uy;
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBREL Packet message_name check" !$"PUBREL" s.message_name;
        T.eq_u8 !$"Valid PUBREL Packet message_type check" 6uy s.message_type;
        T.eq_u8 !$"Valid PUBREL Packet flag check" 2uy s.flags.flag;
        T.eq_u8 !$"Valid PUBREL Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBREL Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBREL Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBREL Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBREL Packet error_message check" !$"" s.error_message;
    B.free request

let valid_pubcomp_packet_test u =
    let request = B.malloc HyperStack.root 0uy 4ul in
        request.(0ul) <- 0x70uy;
        request.(1ul) <- 0x02uy;
        request.(2ul) <- 0x00uy;
        request.(3ul) <- 0x01uy;
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBCOMP Packet message_name check" !$"PUBCOMP" s.message_name;
        T.eq_u8 !$"Valid PUBCOMP Packet message_type check" 7uy s.message_type;
        T.eq_u8 !$"Valid PUBCOMP Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBCOMP Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBCOMP Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBCOMP Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBCOMP Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBCOMP Packet error_message check" !$"" s.error_message;
    B.free request

let aaa u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy 24ul in
        request.(0ul) <- 0x30uy;
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
        T.eq_str !$"abc message_name check" !$"???" s.message_name;
        T.eq_u8 !$"abc message_type check" 0uy s.message_type;
        T.eq_u8 !$"abc flag check" 0uy s.flags.flag;
        T.eq_u8 !$"abc dup_flag check" 0uy s.flags.dup_flag;
        T.eq_u8 !$"abc qos_flag check" 0uy s.flags.qos_flag;
        T.eq_u8 !$"abc retain_flag check" 0uy s.flags.retain_flag;
        T.eq_u32 !$"abc remaining_length check" 0ul s.remaining_length;
        T.eq_str !$"abc error_message check" !$"???" s.error_message;
B.free request

val main : u:unit -> St C.exit_code
let main () =
    T.test_start !$"TestValidPackets1";
    valid_connect_packet_test ();
    valid_connack_packet_test ();
    valid_publish_packet_test ();
    valid_puback_packet_test ();
    valid_pubrec_packet_test ();
    valid_pubrel_packet_test ();
    valid_pubcomp_packet_test ();
    T.test_end ();
    C.EXIT_SUCCESS