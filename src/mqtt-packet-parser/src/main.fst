module Main

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open LowStar.BufferOps
open LowStar.Printf
open FStar.Int.Cast
open C.String
open FFI
open C

open Const
open Common
open Publish
open Connect
open Disconnect
open Debug

val mqtt_packet_parse (packet_data: B.buffer U8.t) (packet_size: type_packet_size):
  Stack struct_fixed_header
    (requires (fun h ->
      B.live h packet_data /\
      B.length packet_data <= U32.v max_request_size /\
      zero_terminated_buffer_u8 h packet_data /\
      (B.length packet_data - 1) = U32.v packet_size))
    (ensures (fun h0 _ h1 -> B.live h0 packet_data /\ B.live h1 packet_data))
let mqtt_packet_parse packet_data packet_size =
  let share_common_data_check: struct_share_common_data_check =
     share_common_data_check packet_data packet_size in
  if (share_common_data_check.share_common_data_have_error) then
    (
      share_common_data_check.share_common_data_error
    )
  else
    (
      let share_common_data: struct_share_common_data = share_common_data_check.share_common_data in
      if (U8.eq share_common_data.common_message_type define_mqtt_control_packet_PUBLISH) then
        (
          publish_packet_parse_result share_common_data
        )
      else if (U8.eq share_common_data.common_message_type define_mqtt_control_packet_CONNECT) then
        (
          connect_packet_parse_result share_common_data
        )
      else if (U8.eq share_common_data.common_message_type define_mqtt_control_packet_DISCONNECT) then
        (
          disconnect_packet_parse_result share_common_data
        )
      else
        (
          let error_struct: struct_error_struct =
            {
                code = define_error_message_type_invalid_code;
                message = define_error_message_type_invalid;
            } in
          unimplemented "Unknown Packet type.\n";
          error_struct_fixed_header error_struct
        )
    )
