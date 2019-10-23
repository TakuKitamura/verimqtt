module Test

open Main
open FStar.HyperStack.ST
open LowStar.Printf

module T = Testing
module B = LowStar.Buffer
module U8 = FStar.UInt8

#set-options "--max_ifuel 0 --max_fuel 0 --z3rlimit 100"

inline_for_extraction noextract
let (!$) = C.String.of_literal

let new_line () = print_string "\n"
let print x =  C.String.print x

val print_struct_fixed_header: s:struct_fixed_header -> Stack unit
    (fun _ -> true)
    (fun _ _ _ -> true)
let print_struct_fixed_header s =
    print !$"message_name: "; print s.message_name; new_line ();
    print !$"message_type: 0x"; print_hex s.message_type; new_line ();
    print !$"flag: 0x"; print_hex s.flags.flag; new_line ();
    print !$"dup_flag: 0x"; print_hex s.flags.dup_flag; new_line ();
    print !$"qos_flag: 0x"; print_hex s.flags.qos_flag; new_line ();
    print !$"retain_flag: 0x"; print_hex s.flags.retain_flag; new_line ();
    print !$"remaining_length: "; print_u32 s.remaining_length; new_line ();
    print !$"error_message: "; print s.error_message; new_line ()

val valid_connect_packet_test: u:unit -> Stack unit
    (fun _ -> true)
    (fun _ _ _ -> true)
let valid_connect_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x10uy; 0x23uy; 0x00uy; 0x04uy; 0x4Duy; 0x51uy; 0x54uy; 0x54uy; 0x04uy; 0x02uy; 0x00uy; 0x3Cuy; 0x00uy; 0x17uy; 0x6Duy; 0x6Fuy; 0x73uy; 0x71uy; 0x2Duy; 0x6Auy; 0x41uy; 0x77uy; 0x6Buy; 0x70uy; 0x43uy; 0x56uy; 0x6Buy; 0x39uy; 0x4Duy; 0x71uy; 0x76uy; 0x41uy; 0x54uy; 0x42uy; 0x4Duy; 0x58uy; 0x62uy; ] in
    let s : struct_fixed_header = parse request 37ul in
        T.eq_str !$"Valid CONNECT Packet message_name check" !$"CONNECT" s.message_name;
        T.eq_u8 !$"Valid CONNECT Packet message_type check" 1uy s.message_type;
        T.eq_u8 !$"Valid CONNECT Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid CONNECT Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid CONNECT Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid CONNECT Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid CONNECT Packet remaining_length check" 35ul s.remaining_length;
        T.eq_str !$"Valid CONNECT Packet error_message check" !$"" s.error_message;
    pop_frame ()

val valid_connack_packet_test: u:unit -> Stack unit
    (fun _ -> true)
    (fun _ _ _ -> true)
let valid_connack_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x20uy; 0x02uy; 0x00uy; 0x00uy; ] in
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid CONNACK Packet message_name check" !$"CONNACK" s.message_name ;
        T.eq_u8 !$"Valid CONNACK Packet message_type check" 2uy s.message_type;
        T.eq_u8 !$"Valid CONNACK Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid CONNACK Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid CONNACK Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid CONNACK Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid CONNACK Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid CONNACK Packet error_message check" !$"" s.error_message;
    pop_frame ()

val valid_publish_packet_test: u:unit -> Stack unit
    (fun _ -> true)
    (fun _ _ _ -> true)
let valid_publish_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x30uy; 0x16uy; 0x00uy; 0x0Auy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x2Fuy; 0x74uy; 0x6Fuy; 0x70uy; 0x69uy; 0x63uy; 0x68uy; 0x65uy; 0x6Cuy; 0x6Cuy; 0x6Fuy; 0x20uy; 0x6Duy; 0x71uy; 0x74uy; 0x74uy; ] in
    let s : struct_fixed_header = parse request 24ul in
        T.eq_str !$"Valid PUBLISH Packet message_name check" !$"PUBLISH" s.message_name;
        T.eq_u8 !$"Valid PUBLISH Packet message_type check" 3uy s.message_type;
        T.eq_u8 !$"Valid PUBLISH Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBLISH Packet dup_flag check" 0uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBLISH Packet qos_flag check" 0uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBLISH Packet retain_flag check" 0uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBLISH Packet remaining_length check" 22ul s.remaining_length;
        T.eq_str !$"Valid PUBLISH Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_puback_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x40uy; 0x02uy; 0x00uy; 0x01uy; ] in
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBACK Packet message_name check" !$"PUBACK" s.message_name;
        T.eq_u8 !$"Valid PUBACK Packet message_type check" 4uy s.message_type;
        T.eq_u8 !$"Valid PUBACK Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBACK Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBACK Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBACK Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBACK Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBACK Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_pubrec_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x50uy; 0x02uy; 0x00uy; 0x01uy; ] in
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBREC Packet message_name check" !$"PUBREC" s.message_name;
        T.eq_u8 !$"Valid PUBREC Packet message_type check" 5uy s.message_type;
        T.eq_u8 !$"Valid PUBREC Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBREC Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBREC Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBREC Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBREC Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBREC Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_pubrel_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x62uy; 0x02uy; 0x00uy; 0x01uy; ] in
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBREL Packet message_name check" !$"PUBREL" s.message_name;
        T.eq_u8 !$"Valid PUBREL Packet message_type check" 6uy s.message_type;
        T.eq_u8 !$"Valid PUBREL Packet flag check" 2uy s.flags.flag;
        T.eq_u8 !$"Valid PUBREL Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBREL Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBREL Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBREL Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBREL Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_pubcomp_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x70uy; 0x02uy; 0x00uy; 0x01uy; ] in
    let s : struct_fixed_header = parse request 4ul in
        T.eq_str !$"Valid PUBCOMP Packet message_name check" !$"PUBCOMP" s.message_name;
        T.eq_u8 !$"Valid PUBCOMP Packet message_type check" 7uy s.message_type;
        T.eq_u8 !$"Valid PUBCOMP Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PUBCOMP Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PUBCOMP Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PUBCOMP Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PUBCOMP Packet remaining_length check" 2ul s.remaining_length;
        T.eq_str !$"Valid PUBCOMP Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_subscribe_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x82uy; 0x0Fuy; 0x00uy; 0x01uy; 0x00uy; 0x0Auy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x2Fuy; 0x74uy; 0x6Fuy; 0x70uy; 0x69uy; 0x63uy; 0x00uy; ] in
    let s : struct_fixed_header = parse request 17ul in
        T.eq_str !$"Valid SUBSCRIBE Packet message_name check" !$"SUBSCRIBE" s.message_name;
        T.eq_u8 !$"Valid SUBSCRIBE Packet message_type check" 8uy s.message_type;
        T.eq_u8 !$"Valid SUBSCRIBE Packet flag check" 2uy s.flags.flag;
        T.eq_u8 !$"Valid SUBSCRIBE Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid SUBSCRIBE Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid SUBSCRIBE Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid SUBSCRIBE Packet remaining_length check" 15ul s.remaining_length;
        T.eq_str !$"Valid SUBSCRIBE Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_suback_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0x90uy; 0x03uy; 0x00uy; 0x01uy; 0x00uy; ] in
    let s : struct_fixed_header = parse request 5ul in
        T.eq_str !$"Valid SUBACK Packet message_name check" !$"SUBACK" s.message_name;
        T.eq_u8 !$"Valid SUBACK Packet message_type check" 9uy s.message_type;
        T.eq_u8 !$"Valid SUBACK Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid SUBACK Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid SUBACK Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid SUBACK Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid SUBACK Packet remaining_length check" 3ul s.remaining_length;
        T.eq_str !$"Valid SUBACK Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_pingreq_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0xC0uy; 0x00uy; ] in
    let s : struct_fixed_header = parse request 2ul in
        T.eq_str !$"Valid PINGREQ Packet message_name check" !$"PINGREQ" s.message_name;
        T.eq_u8 !$"Valid PINGREQ Packet message_type check" 12uy s.message_type;
        T.eq_u8 !$"Valid PINGREQ Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PINGREQ Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PINGREQ Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PINGREQ Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PINGREQ Packet remaining_length check" 0ul s.remaining_length;
        T.eq_str !$"Valid PINGREQ Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_pingresp_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0xD0uy; 0x00uy; ] in
    let s : struct_fixed_header = parse request 2ul in
        T.eq_str !$"Valid PINGRESP Packet message_name check" !$"PINGRESP" s.message_name;
        T.eq_u8 !$"Valid PINGRESP Packet message_type check" 13uy s.message_type;
        T.eq_u8 !$"Valid PINGRESP Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid PINGRESP Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid PINGRESP Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid PINGRESP Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid PINGRESP Packet remaining_length check" 0ul s.remaining_length;
        T.eq_str !$"Valid PINGRESP Packet error_message check" !$"" s.error_message;
    pop_frame ()

let valid_disconnect_packet_test u =
    push_frame ();
    let request : B.buffer U8.t = B.alloca_of_list [0xE0uy; 0x00uy; ] in
    let s : struct_fixed_header = parse request 2ul in
        T.eq_str !$"Valid DISCONNECT Packet message_name check" !$"DISCONNECT" s.message_name;
        T.eq_u8 !$"Valid DISCONNECT Packet message_type check" 14uy s.message_type;
        T.eq_u8 !$"Valid DISCONNECT Packet flag check" 0uy s.flags.flag;
        T.eq_u8 !$"Valid DISCONNECT Packet dup_flag check" 255uy s.flags.dup_flag;
        T.eq_u8 !$"Valid DISCONNECT Packet qos_flag check" 255uy s.flags.qos_flag;
        T.eq_u8 !$"Valid DISCONNECT Packet retain_flag check" 255uy s.flags.retain_flag;
        T.eq_u32 !$"Valid DISCONNECT Packet remaining_length check" 0ul s.remaining_length;
        T.eq_str !$"Valid DISCONNECT Packet error_message check" !$"" s.error_message;
    pop_frame ()

val main : u:unit -> Stack C.exit_code (fun _ -> True) (fun _ _ _ -> True)
let main () =
    T.test_start ();
    // push_frame ();
    valid_connect_packet_test ();
    valid_connack_packet_test ();
    valid_publish_packet_test ();
    valid_puback_packet_test ();
    valid_pubrec_packet_test ();
    valid_pubrel_packet_test ();
    valid_pubcomp_packet_test ();
    valid_subscribe_packet_test ();
    valid_suback_packet_test ();
    valid_pingreq_packet_test ();
    valid_pingresp_packet_test ();
    valid_disconnect_packet_test ();

    // pop_frame ();
    T.test_end ();
    C.EXIT_SUCCESS