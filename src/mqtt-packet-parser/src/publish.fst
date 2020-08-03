module Publish

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = LowStar.Buffer
module HS = FStar.HyperStack

open C.String
open LowStar.BufferOps
open FStar.HyperStack.ST
open FStar.Int.Cast
open LowStar.Printf

open Const
open Common
open FFI
open Debug_FFI

#set-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0"

val get_dup_flag: fixed_header_first_one_byte: U8.t -> type_dup_flags_restrict
let get_dup_flag fixed_header_first_one_byte =
  let dup_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 0uy 1uy in
  if (U8.gt dup_flag_bits 1uy) then
    max_u8
  else
    dup_flag_bits

val get_qos_flag: fixed_header_first_one_byte: U8.t -> type_qos_flags_restrict
let get_qos_flag fixed_header_first_one_byte =
    let qos_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 1uy 3uy in
    if (U8.gt qos_flag_bits 2uy) then
      max_u8
    else
      qos_flag_bits

val get_retain_flag: fixed_header_first_one_byte: U8.t -> type_retain_flags_restrict
let get_retain_flag fixed_header_first_one_byte =
    let retain_flag_bits: U8.t = slice_byte fixed_header_first_one_byte 3uy 4uy in
    if (U8.gt retain_flag_bits 1uy) then
      max_u8
    else
      retain_flag_bits

val struct_fixed_publish:
  flag: type_flag_restrict
  -> dup_flag:type_dup_flags_restrict
  -> qos_flag:type_qos_flags_restrict
  -> retain_flag:type_retain_flags_restrict
  -> struct_fixed_header_constant
let struct_fixed_publish flag dup_flag qos_flag retain_flag = {
  message_type_constant = define_mqtt_control_packet_PUBLISH;
  message_name_constant = define_mqtt_control_packet_PUBLISH_label;
  flags_constant = {
    flag = flag;
    dup_flag = dup_flag;
    qos_flag = qos_flag;
    retain_flag = retain_flag;
  };
}

val assemble_publish_struct: s: struct_publish_parts
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> true)
    (ensures fun h0 r h1 -> true)
let assemble_publish_struct s =
  // let dup_flag: type_dup_flags_restrict = get_dup_flag s.publish_fixed_header_first_one_byte in
  // let qos_flag: type_qos_flags_restrict = get_qos_flag s.publish_fixed_header_first_one_byte in
  // let retain_flag: type_retain_flags_restrict = get_retain_flag s.publish_fixed_header_first_one_byte in
  push_frame ();
  let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
  pop_frame ();
  let data: struct_fixed_header_constant =
    struct_fixed_publish 
      s.publish_flag s.publish_dup_flag s.publish_qos_flag s.publish_retain_flag in
    {
      message_type = data.message_type_constant;
      message_name = data.message_name_constant;
      flags = {
        flag = data.flags_constant.flag;
        dup_flag = data.flags_constant.dup_flag;
        qos_flag = data.flags_constant.qos_flag;
        retain_flag = data.flags_constant.retain_flag;
      };
      remaining_length = s.publish_remaining_length;
      connect = {
        protocol_name = !$"";
        protocol_version = max_u8;
        flags = {
          connect_flag = max_u8;
          user_name = max_u8;
          password = max_u8;
          will_retain = max_u8;
          will_qos = max_u8;
          will_flag = max_u8;
          clean_start = max_u8;
        };
        keep_alive = 0us;
        connect_id = 
          {
            utf8_string_length = 0us;
            utf8_string_value = empty_buffer;
            utf8_string_status_code = 1uy;
            utf8_next_start_index = 0ul;
          };
        will =
          {
            connect_will_property = property_struct_base;
            connect_will_topic_name = 
              {
                utf8_string_length = 0us;
                utf8_string_value = empty_buffer;
                utf8_string_status_code = 1uy;
                utf8_next_start_index = 0ul;
              };
            connect_will_payload = 
              {
                is_valid_binary_data = false;
                binary_length = 0us;
                binary_value = empty_buffer;
                binary_next_start_index = 0ul;
              };
            user_name_or_password_next_start_index = 0ul;
          };
        user_name =
          {
            utf8_string_length = 0us;
            utf8_string_value = empty_buffer;
            utf8_string_status_code = 1uy;
            utf8_next_start_index = 0ul;
          };
        password =
          {
            is_valid_binary_data = false;
            binary_length = 0us;
            binary_value = empty_buffer;
            binary_next_start_index = 0ul;
          };
      };
      publish = {
        topic_length = s.publish_topic_length;
        topic_name = s.publish_topic_name;
        packet_identifier = s.publish_packet_identifier;
        // property_length = s.publish_property_length;
        // property_id = s.publish_property_id;
        payload = s.publish_payload;
        // payload_length = s.publish_payload_length;
      };
      disconnect = {
        disconnect_reason = {
          disconnect_reason_code = max_u8;
          disconnect_reason_code_name = !$"";
        };
      };
      property = s.publish_property;
      error = {
        code = define_no_error_code;
        message = define_no_error;
      };
    }

// TODO: topic-name のエラー条件を追加する
// TODO: UTF-8 の 制約を追加する
val get_topic_name: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> topic_name_start_index: U32.t
  -> topic_length: U32.t
  -> Stack (topic_name: struct_topic_name)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v topic_name_start_index + U32.v topic_length <= U32.v max_u32)
    (ensures fun h0 r h1 -> true)
let get_topic_name packet_data packet_size topic_name_start_index topic_length =
  push_frame ();
  let ptr_counter: B.buffer U32.t = B.alloca 0ul 1ul in
  let ptr_topic_name_u8: B.buffer U8.t = B.alloca 0uy 65536ul in
  let ptr_topic_name: B.buffer type_topic_name_restrict = B.alloca !$"" 1ul in
  let ptr_topic_name_error_status: B.buffer U8.t = B.alloca 0uy 1ul in
  let inv (h: HS.mem) (i:nat) = B.live h packet_data /\
  B.live h ptr_counter /\
  B.live h ptr_topic_name_u8 /\
  B.live h ptr_topic_name /\
  B.live h ptr_topic_name_error_status in
  let last: U32.t = U32.add topic_length topic_name_start_index in
  let body (i: U32.t{U32.v topic_name_start_index <= U32.v i /\
              U32.v i < U32.v last}): Stack unit
    (requires (fun (h: HS.mem) -> inv h (U32.v i)))
    (ensures (fun _ _ _ -> true)) =
    (
      let one_byte: U8.t = 
        (
          if (U32.lt i packet_size) then
            (
              packet_data.(i)
            )
          else
            (
              ptr_topic_name_error_status.(0ul) <- 1uy;
              max_u8
            )
        ) in
      if (U8.eq one_byte 0x00uy || U8.eq one_byte 0x23uy || U8.eq one_byte 0x2buy) then
        (
          ptr_topic_name_error_status.(0ul) <- 2uy
        )
      else
        (
          // ptr_topic_name_u8.(U32.sub variable_header_index 2ul) <- one_byte;
          let counter: U32.t = ptr_counter.(0ul) in
            (
              if (U32.lt counter 65536ul) then 
                (
                  ptr_topic_name_u8.(counter) <- one_byte
                )
              else
                (
                  ptr_topic_name_error_status.(0ul) <- 1uy
                )
            );
          // 0xEF 0xBB 0xBF は 0xFE 0xFF 置換
          if (U32.eq counter (U32.(topic_length -^ 1ul))) then
            (
              let topic_name: type_topic_name_restrict =
                (
                  if (U8.eq ptr_topic_name_u8.(65535ul) 0uy) then
                    // let bom = replace_utf8_encoded ptr_topic_name_u8 65536ul in
                    // TODO: remaining length, ptr_topic_length も -1 対応させる?
                    // ptr_topic_length.(0ul) 
                    //   <- U32.sub ptr_topic_length.(0ul) bom.bom_count;
                    uint8_to_c_string ptr_topic_name_u8
                  else
                    (
                      ptr_topic_name_error_status.(0ul) <- 1uy;
                      !$""
                    )
                ) in ptr_topic_name.(0ul) <- topic_name
            )
          );
          let counter: U32.t = ptr_counter.(0ul) in
          if (U32.lt counter max_u32) then
            (
              ptr_counter.(0ul) <- U32.add counter 1ul
            )
          else
            (
              ptr_topic_name_error_status.(0ul) <- 1uy
            )
    )
  in
  (
  if (U32.lte topic_name_start_index last) then
    (
      C.Loops.for topic_name_start_index last inv body
    )
  else
    (
      ptr_topic_name_error_status.(0ul) <- 1uy
    )
  );

  let topic_name: type_topic_name_restrict = ptr_topic_name.(0ul) in
  let topic_name_error_status: U8.t = ptr_topic_name_error_status.(0ul) in
  pop_frame ();
  let topic_name: struct_topic_name = {
    topic_name_error_status = topic_name_error_status;
    topic_name = topic_name;
  } in topic_name

val publish_packet_parser: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> common_flag: type_flag_restrict
  -> next_start_index:U32.t
  -> Stack (publish_packet_seed: struct_publish_packet_seed)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v next_start_index < (B.length packet_data - 3))
    (ensures fun h0 r h1 -> true)
let publish_packet_parser packet_data packet_size common_flag next_start_index =
  push_frame();
  let dup_flag: type_dup_flags_restrict = get_dup_flag common_flag in
  let qos_flag: type_qos_flags_restrict = get_qos_flag common_flag in
  let retain_flag: type_retain_flags_restrict = get_retain_flag common_flag in

  // TODO: topic name のリファクタ
  let msb_u8: U8.t = packet_data.(next_start_index) in
  let lsb_u8: U8.t = packet_data.(U32.add next_start_index 1ul) in
  let msb_u32: U32.t = uint8_to_uint32 msb_u8  in
  let lsb_u32: U32.t = uint8_to_uint32 lsb_u8 in
  let topic_length: U32.t =
    U32.logor (U32.shift_left msb_u32 8ul) lsb_u32 in
  // U32.v topic_name_start_index + U32.v topic_length <= U32.v max_u32
  let topic_name_start_index: type_packet_data_index = U32.add next_start_index 2ul in
  let topic_name_struct: struct_topic_name = 
    (
      let temp: U64.t = U64.add (uint32_to_uint64 topic_name_start_index) (uint32_to_uint64 topic_length) in
      if (U64.lte temp (uint32_to_uint64 max_u32) &&
          U32.lte (U32.add topic_name_start_index topic_length) max_u32) then
        (
          get_topic_name packet_data packet_size topic_name_start_index topic_length
        )
      else
        (
          let topic_name: struct_topic_name = {
            topic_name_error_status = 1uy;
            topic_name = !$"";
          } in topic_name
        )
    ) in
  let topic_name_error_status: U8.t = topic_name_struct.topic_name_error_status in
  let packet_identifier_struct: struct_packet_identifier = 
    (
      let temp: U64.t = U64.add 
        (uint32_to_uint64 (U32.add next_start_index 3ul))
        (uint32_to_uint64 topic_length) in
      if (U64.lte temp (uint32_to_uint64 max_u32) && U8.gt qos_flag 0uy) then
        (
          let packet_identifier_value: U16.t = 
            get_two_byte_integer_u8_to_u16 
              packet_data.(
                U32.add 
                (U32.add next_start_index 2ul)
                 topic_length)
              packet_data.(U32.add (U32.add next_start_index 3ul) topic_length) in
            let packet_identifier_struct :struct_packet_identifier = 
              {
                packet_identifier_value = packet_identifier_value;
                property_start_to_offset = 2ul;
              } in packet_identifier_struct
        )
      else 
        (
          let packet_identifier_struct: struct_packet_identifier = 
            {
              packet_identifier_value = max_u16;
              property_start_to_offset = 0ul;
            } in packet_identifier_struct
        )
    ) in

  // TODO: propertyが存在しない場合の処理
  let temp: U64.t = U64.(
      (uint32_to_uint64 next_start_index) +^
      2UL +^
      (uint32_to_uint64 topic_length) +^
      (uint32_to_uint64 packet_identifier_struct.property_start_to_offset)
    ) in
  // TODO: エラー追加
  let property_start_index: type_packet_data_index = 
    (
      if (U64.lt temp (uint32_to_uint64 max_packet_size)) then
        (
          U32.(next_start_index +^ 2ul +^ topic_length +^ packet_identifier_struct.property_start_to_offset)
        )
      else
        (
          0ul
        )
    ) in
  let property_struct: struct_property = 
    parse_property packet_data packet_size property_start_index in
  let property_id = property_struct.property_id in
  let payload_start_index: type_packet_data_index = property_struct.payload_start_index in
  let paylaod_end_index: type_packet_data_index = U32.sub packet_size 1ul in
  let payload_struct: struct_payload = 
    get_payload packet_data packet_size payload_start_index paylaod_end_index in
  let payload_error_status = 
  if (payload_struct.is_valid_payload = false) then
    (
      1uy
    )
  else
    (
      0uy
    ) in
  pop_frame ();
  

  let publish_packet_seed: struct_publish_packet_seed = {
    publish_seed_dup_flag = dup_flag;
    publish_seed_qos_flag = qos_flag;
    publish_seed_retain_flag = retain_flag;
    publish_seed_topic_length = topic_length;
    publish_seed_topic_name = topic_name_struct.topic_name;
    publish_seed_topic_name_error_status = topic_name_error_status;
    publish_seed_packet_identifier = packet_identifier_struct.packet_identifier_value;
    publish_seed_is_searching_property_length = false;
    // publish_seed_property_length = 0ul;
    publish_seed_payload = payload_struct;
    // publish_seed_payload_length = payload_struct.payload_length;
    publish_seed_payload_error_status = payload_error_status;
    // publish_seed_property_id = property_id;
    publish_seed_property = property_struct;
  } in publish_packet_seed

val publish_packet_parse_result: (share_common_data: struct_share_common_data)
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> 
    logic_packet_data h0 share_common_data.common_packet_data share_common_data.common_packet_size /\
    U32.v share_common_data.common_next_start_index < (B.length share_common_data.common_packet_data - 3))
    (ensures fun h0 r h1 -> true)
let publish_packet_parse_result share_common_data =
  let publish_packet_seed: struct_publish_packet_seed = 
    publish_packet_parser 
      share_common_data.common_packet_data
      share_common_data.common_packet_size
      share_common_data.common_flag
      share_common_data.common_next_start_index in
  // TODO: エラーコードの見直し
  // Poroperty_error
  let have_error: bool =
    (U8.eq publish_packet_seed.publish_seed_dup_flag max_u8) ||
    (U8.eq publish_packet_seed.publish_seed_qos_flag max_u8) ||
    (U8.eq publish_packet_seed.publish_seed_retain_flag max_u8) ||
    (U32.eq publish_packet_seed.publish_seed_topic_length max_u32) ||
    (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 1uy) ||
    (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 2uy) ||
    (publish_packet_seed.publish_seed_is_searching_property_length) ||
    (U8.gt publish_packet_seed.publish_seed_payload_error_status 0uy) ||
    (U8.gt publish_packet_seed.publish_seed_property.property_type_struct.property_type_error.property_error_code 0uy) in
  if (have_error) then
    (
      let error_struct: struct_error_struct =
        (
          if (U8.eq publish_packet_seed.publish_seed_dup_flag max_u8) then
            {
              code = define_error_dup_flag_invalid_code;
              message = define_error_dup_flag_invalid;
            }
          else if (U8.eq publish_packet_seed.publish_seed_qos_flag max_u8) then
            {
              code = define_error_qos_flag_invalid_code;
              message = define_error_qos_flag_invalid;
            }
          else if (U8.eq publish_packet_seed.publish_seed_retain_flag max_u8) then
            {
              code = define_error_retain_flag_invalid_code;
              message = define_error_retain_flag_invalid;
            }
          else if (U32.eq publish_packet_seed.publish_seed_topic_length max_u32) then
            {
              code = define_error_topic_length_invalid_code;
              message = define_error_topic_length_invalid;
            }
          else if (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 1uy) then
            {
              code = define_error_topic_name_dont_zero_terminated_code;
              message = define_error_topic_name_dont_zero_terminated;
            }
          else if (U8.eq publish_packet_seed.publish_seed_topic_name_error_status 2uy) then
            {
              code = define_error_topic_name_have_inavlid_character_code;
              message = define_error_topic_name_have_inavlid_character;
            }
          else if (publish_packet_seed.publish_seed_is_searching_property_length) then
            {
              code = define_error_property_length_invalid_code;
              message = define_error_property_length_invalid;
            }
          else // (U8.gt publish_packet_seed.publish_seed_property.property_type_struct.struct_property_type.property_type_error.property_error_code 0uy) then
            {
              code = define_error_property_error_code;
              message = publish_packet_seed.publish_seed_property.property_type_struct.property_type_error.property_error_code_name;
            }

        ) in error_struct_fixed_header error_struct
    )
  else
    (
      let ed_fixed_header_parts:
        struct_publish_parts = {
          publish_flag = share_common_data.common_flag;
          publish_dup_flag = publish_packet_seed.publish_seed_dup_flag;
          publish_qos_flag = publish_packet_seed.publish_seed_qos_flag;
          publish_retain_flag = publish_packet_seed.publish_seed_retain_flag;
          publish_remaining_length = share_common_data.common_remaining_length;
          publish_topic_length = publish_packet_seed.publish_seed_topic_length;
          publish_topic_name = publish_packet_seed.publish_seed_topic_name;
          publish_packet_identifier = publish_packet_seed.publish_seed_packet_identifier;
          // publish_property_length = publish_packet_seed.publish_seed_property_length;
          publish_payload = publish_packet_seed.publish_seed_payload;
          // publish_payload_length = publish_packet_seed.publish_seed_payload_length;
          // publish_property_id = publish_packet_seed.publish_seed_property_id;
          publish_property = publish_packet_seed.publish_seed_property;
      } in
      assemble_publish_struct ed_fixed_header_parts
    )
