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

#reset-options "--z3rlimit 500 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val mqtt_packet_parse (request: B.buffer U8.t) (packet_size: type_packet_size):
  Stack struct_fixed_header
    (requires (fun h ->
      B.live h request /\
      B.length request <= U32.v max_request_size /\
      zero_terminated_buffer_u8 h request /\
      (B.length request - 1) = U32.v packet_size))
    (ensures (fun h0 _ h1 -> B.live h0 request /\ B.live h1 request))
let mqtt_packet_parse request packet_size =
  push_frame ();
  let message_type_bits: U8.t = slice_byte request.(0ul) 0uy 4uy in
  let message_type: type_mqtt_control_packets_restrict = get_message_type message_type_bits in
  let ptr_is_break: B.buffer bool = B.alloca false 1ul in
  let ptr_fixed_header_first_one_byte: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_message_type: B.buffer type_mqtt_control_packets_restrict
    = B.alloca max_u8 1ul in
  let ptr_is_searching_remaining_length: B.buffer bool = B.alloca true 1ul in
  let ptr_for_decoding_packets: B.buffer U8.t = B.alloca 0uy 4ul in
  let ptr_remaining_length: B.buffer type_remaining_length =
   B.alloca 0ul 1ul in
  let ptr_variable_header_index: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_for_topic_length: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_topic_length: B.buffer type_topic_length_restrict = B.alloca max_u32 1ul in
  let ptr_topic_name_u8: B.buffer U8.t = B.alloca 0uy 65536ul in
  let ptr_topic_name: B.buffer type_topic_name_restrict = B.alloca !$"" 1ul in
  let ptr_topic_name_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_topic_name_order_mark_check: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_property_length: B.buffer type_property_length = B.alloca 0ul 1ul in
  let ptr_is_searching_property_length: B.buffer bool = B.alloca true 1ul in
  let ptr_payload: B.buffer type_payload_restrict = B.alloca !$"" 1ul in
  let ptr_payload_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_protocol_name_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_protocol_version_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_connect_flag: B.buffer U8.t = B.alloca 0uy 1ul in
  let ptr_keep_alive: B.buffer U8.t = B.alloca 0uy 2ul in
  let ptr_connect_topic_length: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_connect_property_id: B.buffer U8.t = B.alloca 0uy 1ul in

  let first_one_byte: U8.t = request.(0ul) in
  let message_type_bits: U8.t = slice_byte first_one_byte 0uy 4uy in
  let message_type: type_mqtt_control_packets_restrict = get_message_type message_type_bits in

  let variable_length: struct_variable_length = get_variable_byte request packet_size 1ul in
  let remaining_length: type_remaining_length = variable_length.variable_length_value in
  print_u32 remaining_length;
  print_string "\n";

  let inv h (i: nat) =
    B.live h ptr_is_break /\
    B.live h request /\
    B.live h ptr_variable_header_index /\
    B.live h ptr_for_topic_length /\
    B.live h ptr_topic_length /\
    B.live h ptr_topic_name_u8 /\
    B.live h ptr_topic_name /\
    B.live h ptr_topic_name_error_status /\
    B.live h ptr_topic_name_order_mark_check /\
    B.live h ptr_property_length /\
    B.live h ptr_is_searching_property_length /\
    B.live h ptr_payload /\
    B.live h ptr_payload_error_status /\
    B.live h ptr_protocol_name_error_status /\
    B.live h ptr_protocol_version_error_status /\
    B.live h ptr_connect_flag /\
    B.live h ptr_keep_alive /\
    B.live h ptr_connect_topic_length /\
    B.live h ptr_connect_property_id
    in
  let body (i: U32.t{ 2 <= U32.v i && U32.v i < U32.v packet_size  }): Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true))
  =
    let one_byte : U8.t = request.(i) in
        let is_break: bool = ptr_is_break.(0ul) in
      if (is_break) then
        ()
      else
        (
          let variable_header_index: U32.t = ptr_variable_header_index.(0ul) in
            if (U8.eq message_type define_mqtt_control_packet_PUBLISH) then
              (
                let topic_length: type_topic_length_restrict = ptr_topic_length.(0ul) in
                if (variable_header_index = 0ul) then
                  ptr_for_topic_length.(0ul) <- one_byte
                else if (variable_header_index = 1ul) then
                  (
                    let msb_u8: U8.t = ptr_for_topic_length.(0ul) in
                    let lsb_u8: U8.t = one_byte in
                    let msb_u32: U32.t = uint8_to_uint32 msb_u8  in
                    let lsb_u32: U32.t = uint8_to_uint32 lsb_u8 in
                    let _topic_length: U32.t =
                      U32.logor (U32.shift_left msb_u32 8ul) lsb_u32 in
                    if (U32.gt _topic_length 65535ul) then
                      (
                        ptr_topic_length.(0ul) <- max_u32;
                        ptr_is_break.(0ul) <- true
                      )
                    else
                      (
                        ptr_topic_length.(0ul) <- _topic_length
                      )
                  )
                else if (U32.gte variable_header_index 2ul) then
                  (
                    let is_searching_property_length: bool =
                     ptr_is_searching_property_length.(0ul) in
                    if (topic_length = max_u32) then
                      (
                        ptr_topic_length.(0ul) <- max_u32;
                        ptr_is_break.(0ul) <- true
                      )
                    else
                      (
                      if (U32.lte variable_header_index (U32.(topic_length +^ 1ul))) then
                        (
                          if (U8.eq one_byte 0x00uy || U8.eq one_byte 0x23uy || U8.eq one_byte 0x2buy) then
                            (
                              ptr_topic_name_error_status.(0ul) <- 2uy;
                              ptr_is_break.(0ul) <- true
                            )
                          else
                            (
                              ptr_topic_name_u8.(U32.sub variable_header_index 2ul) <- one_byte;
                              let topic_name_order_mark_check: U8.t = ptr_topic_name_order_mark_check.(0ul) in
                              if (U8.eq topic_name_order_mark_check 0uy && U8.eq one_byte 0xefuy) then
                                (
                                  ptr_topic_name_order_mark_check.(0ul) <- 1uy
                                )
                              else if (U8.eq topic_name_order_mark_check 1uy && U8.eq one_byte 0xbbuy) then
                                (
                                  ptr_topic_name_order_mark_check.(0ul) <- 2uy
                                )
                              else if (U8.eq topic_name_order_mark_check 2uy && U8.eq one_byte 0xbfuy && U32.gte variable_header_index 4ul) then
                                (
                                  ptr_topic_name_order_mark_check.(0ul) <- 3uy;
                                  ptr_topic_name_u8.(U32.sub variable_header_index 4ul) <- 0xfeuy;
                                  ptr_topic_name_u8.(U32.sub variable_header_index 3ul) <- 0xffuy;
                                  ptr_variable_header_index.(0ul) <- U32.sub variable_header_index 1ul
                                )
                              else
                                (
                                  ptr_topic_name_order_mark_check.(0ul) <- 0uy;
                                  if (variable_header_index = (U32.(topic_length +^ 1ul))) then
                                    (
                                      let topic_name: type_topic_name_restrict =
                                        (
                                          if (ptr_topic_name_u8.(65535ul) = 0uy) then
                                            topic_name_uint8_to_c_string ptr_topic_name_u8
                                          else
                                            (
                                              ptr_topic_name_error_status.(0ul) <- 1uy;
                                              !$""
                                            )
                                        ) in ptr_topic_name.(0ul) <- topic_name
                                    )
                                )
                             )

                        )
                      else if (U32.gt variable_header_index (U32.(topic_length +^ 1ul))
                        && U32.lte variable_header_index (U32.(topic_length +^ 5ul))
                        && is_searching_property_length
                        ) then
                        (

                          if (one_byte = 0uy) then
                            (
                              ptr_property_length.(0ul) <- uint8_to_uint32 one_byte;
                              ptr_is_searching_property_length.(0ul) <- false
                            )
                            // else (
                            //   // TODO: 3.3.2.3 PUBLISH Properties 
                            //   // https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901109
                            //   // print_not_implemented "PUBLISH Properties Parsing"
                            // )
                        )
                      else if (not is_searching_property_length) then
                        (
                          let payload_offset: type_payload_offset = i in
                          let ptr_payload_u8: B.buffer U8.t = B.offset request payload_offset in
                          let payload: type_payload_restrict =
                            (
                              let last_payload_index: U32.t =
                                U32.(packet_size -^ payload_offset) in
                              let last_payload_element: U8.t = ptr_payload_u8.(last_payload_index) in
                                if (last_payload_element <> 0uy) then
                                  (
                                    ptr_payload_error_status.(0ul) <- 1uy;
                                    !$""
                                  )
                                else
                                  payload_uint8_to_c_string ptr_payload_u8 min_packet_size max_packet_size packet_size
                            ) in
                          ptr_payload.(0ul) <- payload;
                          ptr_is_break.(0ul) <- true
                        )
                      else
                        (
                          ()
                        )
                      )
                  )
                else
                  (
                    ()
                  )
              )
            else if (U8.eq message_type define_mqtt_control_packet_CONNECT) then (
              (
                if (U32.lte variable_header_index 5ul) then
                  (
                    if (
                      (U32.eq variable_header_index 0ul && not (U8.eq one_byte 0x00uy)) ||
                      (U32.eq variable_header_index 1ul && not (U8.eq one_byte 0x04uy)) ||
                      (U32.eq variable_header_index 2ul && not (U8.eq one_byte 0x4Duy)) ||
                      (U32.eq variable_header_index 3ul && not (U8.eq one_byte 0x51uy)) ||
                      (U32.eq variable_header_index 4ul && not (U8.eq one_byte 0x54uy)) ||
                      (U32.eq variable_header_index 5ul && not (U8.eq one_byte 0x54uy))
                      ) then
                      (
                        ptr_protocol_name_error_status.(0ul) <- 1uy;
                        ptr_is_break.(0ul) <- true
                      )
                  )
                  else if (U32.eq variable_header_index 6ul && not (U8.eq one_byte 0x05uy)) then
                    (
                      ptr_protocol_version_error_status.(0ul) <- 1uy;
                      ptr_is_break.(0ul) <- true
                    )
                  else if (U32.eq variable_header_index 7ul) then
                    (
                      ptr_connect_flag.(0ul) <- one_byte
                    )
                  else if (U32.eq variable_header_index 8ul) then
                    (
                      ptr_keep_alive.(0ul) <- one_byte
                    )
                  else if (U32.eq variable_header_index 9ul) then
                    (
                      if (U8.lte one_byte 0x7Fuy) then
                        (
                          ptr_keep_alive.(1ul) <- one_byte
                        )
                      // else 
                      //   (
                      //     // TODO: keep aliveが127以上の場合は未実装.
                      //   )
                    )
                  else if (U32.eq variable_header_index 10ul) then
                    (
                      // TODO: topic length が一桁かつ, keep aliveが127以下の場合
                      ptr_connect_topic_length.(0ul) <- uint8_to_uint32 one_byte
                    )
                  else if (U32.eq variable_header_index 11ul) then
                    (
                      // TODO: topic length が一桁かつ, keep aliveが127以下の場合
                      ptr_connect_property_id.(0ul) <- one_byte
                    )
                  // else
                  //   (
                  //     print_string "x: ";
                  //     print_u8 one_byte;
                  //     print_string ", index: ";
                  //     print_u32 variable_header_index;
                  //     print_string "\n"
                  //   )
              )
            );
            if (U32.lte variable_header_index (U32.sub max_u32 1ul)) then
              ptr_variable_header_index.(0ul) <-
                U32.(variable_header_index +^ 1ul)

        )
      // else
      //   (
      //     ()
      //   )
  in
  let next_start_index: U32.t = variable_length.next_start_index in
  C.Loops.for next_start_index packet_size inv body;

  let topic_length: type_topic_length_restrict = ptr_topic_length.(0ul) in
  let topic_name: type_topic_name_restrict = ptr_topic_name.(0ul) in
  let topic_name_error_status: U8.t = ptr_topic_name_error_status.(0ul) in
  let is_searching_property_length: bool = ptr_is_searching_property_length.(0ul) in
  let property_length: type_property_length = ptr_property_length.(0ul) in
  let payload: type_payload_restrict = ptr_payload.(0ul) in
  let payload_error_status: U8.t = ptr_payload_error_status.(0ul) in
  let protocol_name_error_status: U8.t = ptr_protocol_name_error_status.(0ul) in
  let protocol_version_error_status: U8.t = ptr_protocol_version_error_status.(0ul) in
  let connect_flag: U8.t = ptr_connect_flag.(0ul) in
  let keep_alive_msb_u8: U8.t = ptr_keep_alive.(0ul) in
  let keep_alive_lsb_u8: U8.t = ptr_keep_alive.(1ul) in
  let connect_topic_length: U32.t = ptr_connect_topic_length.(0ul) in
  let connect_property_id: U8.t = ptr_connect_property_id.(0ul) in
  pop_frame ();
  let is_share_error: bool = (variable_length.have_error) || (U8.eq message_type max_u8) in

  if (is_share_error) then
    (

      let error_struct: struct_error_struct =
        (
          if (variable_length.have_error) then
            {
              code = define_error_remaining_length_invalid_code;
              message = define_error_remaining_length_invalid;
            }
          else // if (U8.eq message_type max_u8) then
            {
              code = define_error_message_type_invalid_code;
              message = define_error_message_type_invalid;
            }
        ) in error_struct_fixed_header error_struct
    )
  else
    (  
      if (U8.eq message_type define_mqtt_control_packet_PUBLISH) then
        (
          let dup_flag: type_dup_flags_restrict = get_dup_flag first_one_byte in
          let qos_flag: type_qos_flags_restrict = get_qos_flag first_one_byte in
          let retain_flag: type_retain_flags_restrict = get_retain_flag first_one_byte in
          let have_error: bool =
            (U8.eq dup_flag max_u8) ||
            (U8.eq qos_flag max_u8) ||
            (U8.eq retain_flag max_u8) ||
            (U8.eq topic_name_error_status 1uy) ||
            (U8.eq topic_name_error_status 2uy) ||
            (U32.eq topic_length max_u32) ||
            (is_searching_property_length) ||
            (U8.gt payload_error_status 0uy) in
          if (have_error) then
            (
              let error_struct: struct_error_struct =
                (
                  if (U8.eq dup_flag max_u8) then
                    {
                      code = define_error_dup_flag_invalid_code;
                      message = define_error_dup_flag_invalid;
                    }
                  else if (U8.eq qos_flag max_u8) then
                    {
                      code = define_error_qos_flag_invalid_code;
                      message = define_error_qos_flag_invalid;
                    }
                  else if (U8.eq retain_flag max_u8) then
                    {
                      code = define_error_retain_flag_invalid_code;
                      message = define_error_retain_flag_invalid;
                    }
                  else if (U32.eq topic_length max_u32) then
                    {
                      code = define_error_topic_length_invalid_code;
                      message = define_error_topic_length_invalid;
                    }
                  else if (U8.eq topic_name_error_status 1uy) then
                    {
                      code = define_error_topic_name_dont_zero_terminated_code;
                      message = define_error_topic_name_dont_zero_terminated;
                    }
                  else if (U8.eq topic_name_error_status 2uy) then
                    {
                      code = define_error_topic_name_have_inavlid_character_code;
                      message = define_error_topic_name_have_inavlid_character;
                    }
                  else // if (is_searching_property_length) then
                    {
                      code = define_error_property_length_invalid_code;
                      message = define_error_property_length_invalid;
                    }
                ) in error_struct_fixed_header error_struct
            )
          else
            (
              let ed_fixed_header_parts:
                struct_publish_parts = {
                  publish_fixed_header_first_one_byte = first_one_byte;
                  publish_remaining_length = remaining_length;
                  publish_topic_length = topic_length;
                  publish_topic_name = topic_name;
                  publish_property_length = property_length;
                  publish_payload = payload;
              } in
              assemble_publish_struct ed_fixed_header_parts
            )
        )
      else if (U8.eq message_type define_mqtt_control_packet_CONNECT) then
        (
            let connect_constant: struct_fixed_header_constant =
              get_struct_fixed_header_constant_except_publish message_type in
            let connect_flag: U8.t = connect_flag in
            let user_name_flag: U8.t = slice_byte connect_flag 0uy 1uy in
            let password_flag: U8.t = slice_byte connect_flag 1uy 2uy in
            let will_retain_flag: U8.t = slice_byte connect_flag 2uy 3uy in
            let will_qos_flag: U8.t = slice_byte connect_flag 3uy 5uy in
            let will_flag: U8.t = slice_byte connect_flag 5uy 6uy in
            let clean_start_flag: U8.t = slice_byte connect_flag 6uy 7uy in
            let resreved_flag: U8.t = slice_byte connect_flag 7uy 8uy in
            let connect_property_id: U8.t = connect_property_id in
            let keep_alive_msb_u32: U32.t = uint8_to_uint32 keep_alive_msb_u8  in
            let keep_alive_lsb_u32: U32.t = uint8_to_uint32 keep_alive_lsb_u8 in 
            let keep_alive: U32.t = U32.logor (U32.shift_left keep_alive_msb_u32 8ul)keep_alive_lsb_u32 in

            let have_error: bool =
              (protocol_name_error_status = 1uy) ||
              (protocol_version_error_status = 1uy) ||
              (not (U8.eq resreved_flag 0uy) ) in
            if (have_error) then
              (
                let error_struct: struct_error_struct =
                  (
                    if (protocol_name_error_status = 1uy) then
                      {
                        code = define_error_protocol_name_invalid_code;
                        message = define_error_protocol_name_invalid;
                      }
                    else if (protocol_version_error_status = 1uy) then
                      {
                        code = define_error_protocol_version_invalid_code;
                        message = define_error_protocol_version_invalid;
                      }
                    else // if (not (U8.eq resreved_flag 0uy) ) then
                      {
                        code = define_error_connect_flag_invalid_code;
                        message = define_error_connect_flag_invalid;
                      }
                  ) in error_struct_fixed_header error_struct
              )
            else
              (
                let ed_fixed_header_parts:
                  struct_connect_parts = {
                    connect_remaining_length = remaining_length;
                    connect_connect_constant = connect_constant;
                    connect_connect_flag = connect_flag;
                    connect_keep_alive = keep_alive;
                    connect_connect_topic_length = connect_topic_length;
                    connect_connect_property_id = connect_property_id;
                } in
                assemble_connect_struct ed_fixed_header_parts            
              )
        )
        else if (U8.eq message_type define_mqtt_control_packet_DISCONNECT) then
          (
            let flag: type_flag_restrict = get_flag message_type first_one_byte in
            let disconnect_constant: struct_fixed_header_constant =
              get_struct_fixed_header_constant_except_publish message_type in
            let have_error: bool =
              (is_valid_flag disconnect_constant flag = false) in
              if (have_error) then
                (
                  let error_struct: struct_error_struct =
                    {
                        code = define_error_flag_invalid_code;
                        message = define_error_flag_invalid;
                    }
                  in error_struct_fixed_header error_struct
                )
              else
                (
                  let ed_fixed_header_parts:
                  struct_disconnect_parts = {
                    disconnect_disconnect_constant = disconnect_constant;
                    disconnect_remaining_length = remaining_length;
                  } in
                  assemble_disconnect_struct ed_fixed_header_parts
                )
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
