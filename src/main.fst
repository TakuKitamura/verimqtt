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

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901022
// 2.1.2 MQTT Control Packet type
// Table 2‑1 MQTT Control Packet types
type type_mqtt_control_packets = U8.t // Base 10

let define_mqtt_control_packet_RESERVED : type_mqtt_control_packets = 0uy
let define_mqtt_control_packet_CONNECT : type_mqtt_control_packets = 1uy
let define_mqtt_control_packet_CONNACK : type_mqtt_control_packets = 2uy
let define_mqtt_control_packet_PUBLISH : type_mqtt_control_packets = 3uy
let define_mqtt_control_packet_PUBACK : type_mqtt_control_packets = 4uy
let define_mqtt_control_packet_PUBREC : type_mqtt_control_packets = 5uy
let define_mqtt_control_packet_PUBREL : type_mqtt_control_packets = 6uy
let define_mqtt_control_packet_PUBCOMP : type_mqtt_control_packets = 7uy
let define_mqtt_control_packet_SUBSCRIBE : type_mqtt_control_packets = 8uy
let define_mqtt_control_packet_SUBACK : type_mqtt_control_packets = 9uy
let define_mqtt_control_packet_UNSUBSCRIBE : type_mqtt_control_packets = 10uy
let define_mqtt_control_packet_UNSUBACK : type_mqtt_control_packets = 11uy
let define_mqtt_control_packet_PINGREQ : type_mqtt_control_packets = 12uy
let define_mqtt_control_packet_PINGRESP : type_mqtt_control_packets = 13uy
let define_mqtt_control_packet_DISCONNECT : type_mqtt_control_packets = 14uy
let define_mqtt_control_packet_AUTH : type_mqtt_control_packets = 15uy

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901022
// 2.1.3 Flags
// Table 2‑2 Flag Bits
type type_flags = U8.t // Base 2

let define_flag_CONNECT : type_flags = 0b0000uy
let define_flag_CONNACK : type_flags = 0b0000uy 
// PUBLISH は下記に記述
let define_flag_PUBACK : type_flags = 0b0000uy
let define_flag_PUBREC : type_flags = 0b0000uy
let define_flag_PUBREL : type_flags = 0b0010uy
let define_flag_PUBCOMP : type_flags = 0b0000uy
let define_flag_SUBSCRIBE : type_flags = 0b0010uy
let define_flag_SUBACK : type_flags = 0b0000uy
let define_flag_UNSUBSCRIBE : type_flags = 0b0010uy
let define_flag_UNSUBACK : type_flags = 0b0000uy
let define_flag_PINGREQ : type_flags = 0b0000uy
let define_flag_PINGRESP : type_flags = 0b0000uy
let define_flag_DISCONNECT : type_flags = 0b0000uy
let define_flag_AUTH : type_flags = 0b0000uy

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.1 DUP
type type_dup_flags = U8.t // Base 10

let define_dup_flag_first_delivery : type_dup_flags = 0uy
let define_dup_flag_re_delivery : type_dup_flags = 1uy 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.2 QoS
// Table 3‑2 - QoS definitions
type type_qos_flags = U8.t // Base 2

let define_qos_flag_at_most_once_delivery : type_qos_flags = 0b00uy
let define_qos_flag_at_least_once_delivery : type_qos_flags = 0b01uy
let define_qos_flag_exactly_once_delivery : type_qos_flags = 0b10uy
let define_qos_flag_reserved : type_qos_flags = 0b11uy

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html
// 3.3.1.3 RETAIN
type type_retain_flags = U8.t // Base 10

let define_retain_flag_must_not_store_application_message : type_retain_flags = 0uy
let define_retain_flag_must_store_application_message : type_retain_flags = 1uy 


// debug tool
assume val extern_print_hex (i: U8.t{ 0 <= U8.v i /\ U8.v i <= 255}): Stack unit
  (requires (fun h -> true))
  (ensures (fun h0 ret h1 -> true))

// ex. 0xab -> 0x0a TODO: rの定義域を追加
val get_most_significant_four_bit: i:U8.t -> r:U8.t
let get_most_significant_four_bit i = U8.shift_right i 4ul

// ex. 0xab -> 0x0b TODO: rの定義域を追加
val get_least_significant_four_bit: i:U8.t -> r:U8.t
let get_least_significant_four_bit i = U8.logand i 0x0fuy

val bytes_loop: src:B.buffer U8.t -> len:U32.t -> Stack C.exit_code
  (requires fun h0 -> B.live h0 src /\ B.length src = U32.v len )
  (ensures fun _ _ _ -> true)
let bytes_loop src len =
  let inv h (i: nat) = B.live h src in
  let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v len }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let oneByte : U8.t = src.(i) in
      let most_significant_four_bit = get_most_significant_four_bit in 
      let least_significant_four_bit = get_least_significant_four_bit in 
      extern_print_hex (oneByte);
      extern_print_hex (get_most_significant_four_bit oneByte);
      extern_print_hex (get_least_significant_four_bit oneByte)
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
    let r = bytes_loop request len in
    pop_frame ();
    C.EXIT_SUCCESS
