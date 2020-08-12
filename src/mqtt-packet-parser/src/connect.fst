module Connect

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer

open C.String
open LowStar.BufferOps
open FStar.HyperStack.ST
open FStar.Int.Cast
open LowStar.Printf

open Const
open Common
open Debug_FFI

#set-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0"

val assemble_connect_struct: s: struct_connect_parts
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> true)
    (ensures fun h0 r h1 -> true)
let assemble_connect_struct s =
  push_frame ();
  let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
  pop_frame ();
  let connect_constant: struct_fixed_header_constant = s.connect_connect_constant in
  {
    message_type = connect_constant.message_type_constant;
    message_name = connect_constant.message_name_constant;
    flags = {
      flag = connect_constant.flags_constant.flag;
      dup_flag = connect_constant.flags_constant.dup_flag;
      qos_flag = connect_constant.flags_constant.qos_flag;
      retain_flag = connect_constant.flags_constant.retain_flag;
    };
    remaining_length = s.connect_remaining_length;
    connect = s.connect_struct;
    publish = {
      topic_length = 0ul;
      topic_name = !$"";
      // property_length = 0ul;
      packet_identifier = max_u16;
      payload = {
        is_valid_payload = false;
        payload_value = empty_buffer;
        payload_length = 0ul;
      };
      // payload_length = 0ul;
      // property_id = max_u8;
    };
    disconnect = {
      disconnect_reason = {
        disconnect_reason_code = max_u8;
        disconnect_reason_code_name = !$"";
      };
    };
    property = s.connect_property;
    error = {
      code = define_no_error_code;
      message = define_no_error;
    };
  }

val is_valid_protocol_name: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index: type_packet_data_index
  -> Stack (protocoll_name_struct: struct_protocol_name)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v next_start_index < (B.length packet_data - 6))
    (ensures fun h0 r h1 -> true)
let is_valid_protocol_name packet_data packet_size next_start_index = 
  push_frame ();
  let first_byte: U8.t = packet_data.(U32.(next_start_index +^ 0ul)) in
  let second_byte: U8.t = packet_data.(U32.(next_start_index +^ 1ul)) in
  let third_byte: U8.t = packet_data.(U32.(next_start_index +^ 2ul)) in
  let fourth_byte: U8.t = packet_data.(U32.(next_start_index +^ 3ul)) in
  let fifth_byte: U8.t = packet_data.(U32.(next_start_index +^ 4ul)) in
  let sixth_byte: U8.t = packet_data.(U32.(next_start_index +^ 5ul)) in
  pop_frame ();
  if (
      (not (U8.eq first_byte 0x00uy)) ||
      (not (U8.eq second_byte 0x04uy)) ||
      (not (U8.eq third_byte 0x4Duy)) ||
      (not (U8.eq fourth_byte 0x51uy)) ||
      (not (U8.eq fifth_byte 0x54uy)) ||
      (not (U8.eq sixth_byte 0x54uy))
    ) then
    (
      let protocoll_name_struct: struct_protocol_name = {
        is_valid_protocol_name = false;
        protocol_version_start_index = 0ul;
      } in protocoll_name_struct
    )
  else 
    (
      let protocoll_name_struct: struct_protocol_name = {
        is_valid_protocol_name = true;
        protocol_version_start_index = U32.(next_start_index +^ 6ul);
      } in protocoll_name_struct 
    )

val is_valid_protocol_version: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index: type_packet_data_index
  -> Stack (protocoll_version_struct: struct_protocol_version)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v next_start_index < (B.length packet_data - 1))
    (ensures fun h0 r h1 -> true)
let is_valid_protocol_version packet_data packet_size next_start_index = 
  (
    let protocol_version: U8.t = packet_data.(next_start_index) in
    if (not (U8.eq protocol_version 0x05uy)) then
      (
        let protocol_version_struct: struct_protocol_version = {
          is_valid_protocol_version = false;
          connect_flag_start_index = 0ul;
        } in protocol_version_struct
      )
    else 
      (
        let protocol_version_struct: struct_protocol_version = {
          is_valid_protocol_version = true;
          connect_flag_start_index = U32.(next_start_index +^ 1ul);
        } in protocol_version_struct 
      )
  )

val get_connect_flag: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> next_start_index: type_packet_data_index
  -> Stack (connect_flag_struct: struct_connect_flag)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v next_start_index < (B.length packet_data - 1))
    (ensures fun h0 r h1 -> true)
let get_connect_flag packet_data packet_size next_start_index = 
  let connect_flag: U8.t = packet_data.(next_start_index) in
  let connect_flag_struct: struct_connect_flag = {
    connect_flag_value = connect_flag;
    keep_alive_start_index = U32.(next_start_index +^ 1ul);
  } in connect_flag_struct


val get_protocol_version_struct: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> protocol_version_start_index: type_packet_data_index
  -> Stack (protocol_version_struct: struct_protocol_version)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_protocol_version_struct packet_data packet_size protocol_version_start_index =
  (
    push_frame ();
    if (U32.lt protocol_version_start_index (U32.sub packet_size 1ul)) then
      (
        pop_frame ();
        is_valid_protocol_version 
          packet_data packet_size protocol_version_start_index 
      )
    else
      (
        let protocol_version_struct: struct_protocol_version = {
          is_valid_protocol_version = false;
          connect_flag_start_index = 0ul;
        } in 
        pop_frame ();
        protocol_version_struct
      ) 
  )


val get_connect_flag_struct: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> connect_flag_start_index: type_packet_data_index
  -> Stack (connect_flag_struct: struct_connect_flag)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_connect_flag_struct packet_data packet_size connect_flag_start_index =
  (
    push_frame ();
    if (U32.lt connect_flag_start_index (U32.sub packet_size 1ul)) then
      (
        pop_frame ();
        get_connect_flag packet_data packet_size connect_flag_start_index
      )
    else
      (
        let connect_flag: struct_connect_flag = {
          connect_flag_value = max_u8;
          keep_alive_start_index = 0ul;
        } in
        pop_frame ();
        connect_flag
      )
  )

val get_connect_property_index: keep_alive_start_index: type_packet_data_index
  -> packet_size: type_packet_size
  -> Stack (property_start_index: type_packet_data_index)
    (requires fun h0 -> true)
    (ensures fun h0 r h1 -> true)
let get_connect_property_index keep_alive_start_index packet_size = 
  (
    push_frame ();
    let temp_index: U32.t = U32.add keep_alive_start_index 2ul in
    pop_frame ();
    if (U32.lt temp_index packet_size) then
      (
        temp_index
      )
    else
      (
        0ul
      )
  )

val get_connect_id: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> payload_start_index: type_packet_data_index
  -> Stack (connect_id_struct: struct_utf8_string)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_connect_id packet_data packet_size payload_start_index =
  push_frame ();
  let connect_id: struct_utf8_string =
    (
      if (U32.lt payload_start_index (U32.sub packet_size 1ul) &&
          U32.lt (U32.add payload_start_index 2ul) max_packet_size) then
        (
          get_utf8_encoded_string packet_data packet_size payload_start_index
        ) 
      else
        (
          let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
          let error_struct: struct_utf8_string = {
              utf8_string_length = 0us;
              utf8_string_value = empty_buffer;
              utf8_string_status_code = 1uy;
              utf8_next_start_index = 0ul;
            } in error_struct
        )
    ) in
    pop_frame ();
    connect_id

#set-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --detail_errors"
val get_connect_will_struct: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> will_start_index: type_packet_data_index
  -> will_flag: U8.t
  -> Stack (connect_will_struct: struct_connect_will)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_connect_will_struct packet_data packet_size will_start_index will_flag =
  push_frame ();
  let connect_will_struct: struct_connect_will =
    (
      if (U8.eq will_flag 1uy &&
          U32.lt will_start_index (U32.sub packet_size 1ul)) then
        (
          // TODO: エラーチェック
          let will_property_start_index: type_packet_data_index =
            will_start_index in
          let property_struct: struct_property = 
            parse_property packet_data packet_size will_property_start_index in
          let will_topic_name_struct: struct_utf8_string = 
            (
              if (U32.lt property_struct.payload_start_index (U32.sub packet_size 1ul) &&   U32.lt (U32.add property_struct.payload_start_index 2ul) max_packet_size) then
                (
                  get_utf8_encoded_string 
                    packet_data packet_size property_struct.payload_start_index
                )
              else
                (
                  let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
                  let error_struct: struct_utf8_string = {
                    utf8_string_length = 0us;
                    utf8_string_value = empty_buffer;
                    utf8_string_status_code = 1uy;
                    utf8_next_start_index = 0ul;
                  } in error_struct  
                )
            ) in
          let will_payload_struct: struct_binary_data = 
            (
              if (U32.gte packet_size 3ul &&
                  U32.lt 
                    will_topic_name_struct.utf8_next_start_index
                    (U32.sub packet_size 3ul)
                  ) then
                (
                  get_binary 
                    packet_data packet_size will_topic_name_struct.utf8_next_start_index
                )
              else
                (
                  let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
                  let binary_data_struct: struct_binary_data = {
                    is_valid_binary_data = false;
                    binary_length = 0us;
                    binary_value = empty_buffer;
                    binary_next_start_index = 0ul;
                  } in binary_data_struct                
                )
            ) in
          let connect_will_struct: struct_connect_will = 
            {
              connect_will_property = property_struct;
              connect_will_topic_name = will_topic_name_struct;
              connect_will_payload = will_payload_struct;
              user_name_or_password_next_start_index = will_payload_struct.binary_next_start_index;
            } in connect_will_struct
        )
      else
        (
          let connect_will_struct: struct_connect_will =
            {
              connect_will_property = property_struct_base;
              connect_will_topic_name = 
                {
                  utf8_string_length = 0us;
                  utf8_string_value = B.alloca 0uy 1ul;
                  utf8_string_status_code = 1uy;
                  utf8_next_start_index = 0ul;
                };
              connect_will_payload = 
                {
                  is_valid_binary_data = false;
                  binary_length = 0us;
                  binary_value = B.alloca 0uy 1ul;
                  binary_next_start_index = 0ul;
                };
              user_name_or_password_next_start_index = 0ul;
            } in connect_will_struct
        )
    ) in
    pop_frame ();
    connect_will_struct
#reset-options

val get_keep_alive: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> keep_alive_start_index: type_packet_data_index
  -> Stack (keep_alive_struct: struct_keep_alive)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_keep_alive packet_data packet_size keep_alive_start_index =
  push_frame ();
  let ptr_is_valid_keep_alive: B.buffer bool = B.alloca false 1ul in
  let keep_alive: U16.t = 
    let msb_index: U32.t = keep_alive_start_index in
    let lsb_index: U32.t = U32.(keep_alive_start_index +^ 1ul) in
      (
        if (U32.lt msb_index packet_size && U32.lt lsb_index packet_size) then 
          (
            ptr_is_valid_keep_alive.(0ul) <- true;
            let a: U32.t = keep_alive_start_index in
            let b: U32.t = U32.(keep_alive_start_index +^ 1ul) in
            get_two_byte_integer_u8_to_u16 // ここエラー
              packet_data.(a)
              packet_data.(b)
          )
        else
          (
            0us
          )
      ) in
  let is_valid_keep_alive: bool = ptr_is_valid_keep_alive.(0ul) in
  let keep_alive_struct: struct_keep_alive = {
    keep_alive_value = keep_alive;
    is_valid_keep_alive = is_valid_keep_alive;
  } in
  pop_frame ();
  keep_alive_struct

val get_user_name_struct: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> user_name_start_index: type_packet_data_index
  -> user_name_flag: U8.t
  -> Stack (user_name_struct: struct_utf8_string)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_user_name_struct packet_data packet_size user_name_start_index user_name_flag =
  push_frame ();
  let user_name_struct: struct_utf8_string = 
    (
      if (user_name_flag = 1uy &&
          U32.lt 
            user_name_start_index
            (U32.sub packet_size 1ul) &&
          U32.lt 
            (U32.add user_name_start_index 2ul)
            max_packet_size) then
        (
          let user_name_struct: struct_utf8_string = //ここ
            get_utf8_encoded_string packet_data packet_size user_name_start_index
          in user_name_struct
        )
      else
        (
          let user_name_struct: struct_utf8_string = 
            {
              utf8_string_length = 0us;
              utf8_string_value = B.alloca 0uy 1ul;
              utf8_string_status_code = 1uy;
              utf8_next_start_index = 0ul;
            } in user_name_struct  
        )
    ) in
    pop_frame ();
    user_name_struct

val get_password_struct: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size
  -> password_start_index: type_packet_data_index
  -> password_flag: U8.t
  -> Stack (password_struct: struct_binary_data)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size)
    (ensures fun h0 r h1 -> true)
let get_password_struct packet_data packet_size password_start_index password_flag =
  push_frame ();
  let password_struct: struct_binary_data =
    (
      if (password_flag = 1uy &&
          U32.gte packet_size 3ul &&
          U32.lt 
            password_start_index
            (U32.sub packet_size 3ul)) then
        (
          let password_struct: struct_binary_data =
            get_binary packet_data packet_size password_start_index in
          password_struct 
        )
      else
        (
          let password_struct: struct_binary_data =
            {
              is_valid_binary_data = false;
              binary_length = 0us;
              binary_value = B.alloca 0uy 1ul;
              binary_next_start_index = 0ul;
            } 
            in password_struct  
        )
    ) in
    pop_frame ();
    password_struct

#set-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --detail_errors"
val connect_packet_parser: packet_data: (B.buffer U8.t) 
  -> packet_size: type_packet_size 
  -> next_start_index: type_packet_data_index
  -> Stack (connect_packet_seed: struct_connect_packet_seed)
    (requires fun h0 -> 
    logic_packet_data h0 packet_data packet_size /\
    U32.v next_start_index < (B.length packet_data - 6))
    (ensures fun h0 r h1 -> true)
let connect_packet_parser packet_data packet_size next_start_index =
  push_frame ();
  let protocol_name_struct: struct_protocol_name = 
    is_valid_protocol_name packet_data packet_size next_start_index in
  let protocol_version_struct: struct_protocol_version =
    get_protocol_version_struct packet_data packet_size protocol_name_struct.protocol_version_start_index in
  let connect_flag_struct: struct_connect_flag = 
    get_connect_flag_struct packet_data packet_size protocol_version_struct.connect_flag_start_index in
  let keep_alive_struct: struct_keep_alive = 
    get_keep_alive packet_data packet_size connect_flag_struct.keep_alive_start_index in
  // TODO: エラー追加
  let property_start_index: type_packet_data_index = 
    get_connect_property_index connect_flag_struct.keep_alive_start_index packet_size in
  let property_struct: struct_property = 
    (
      if (U32.lt property_start_index (U32.sub packet_size 1ul)) then
        (
          parse_property packet_data packet_size property_start_index 
        )
      else
        (
          let error_struct: struct_property = {
            property_id = max_u8;
            property_type_id = max_u8;
            property_type_struct = property_struct_type_base;
            payload_start_index = 0ul;
          } in error_struct
        )
    ) in
  let payload_start_index: U32.t = property_struct.payload_start_index in
  let connect_id: struct_utf8_string =
    get_connect_id packet_data packet_size payload_start_index in
  let connect_flag:U8.t = connect_flag_struct.connect_flag_value in
  let user_name_flag: U8.t = slice_byte connect_flag 0uy 1uy in
  let password_flag: U8.t = slice_byte connect_flag 1uy 2uy in
  let will_retain_flag: U8.t = slice_byte connect_flag 2uy 3uy in
  let will_qos_flag: U8.t = slice_byte connect_flag 3uy 5uy in
  let will_flag: U8.t = slice_byte connect_flag 5uy 6uy in
  let clean_start_flag: U8.t = slice_byte connect_flag 6uy 7uy in
  let resreved_flag: U8.t = slice_byte connect_flag 7uy 8uy in
  let ptr_is_valid_will_start_index: B.buffer bool = B.alloca false 1ul in
  let will_start_index: type_packet_data_index = 
    (
      let temp: U32.t = U32.(payload_start_index +^ 2ul +^ (uint16_to_uint32 connect_id.utf8_string_length)) in
      if (U32.lt temp max_packet_size) then
        (
          ptr_is_valid_will_start_index.(0ul) <- true;
          temp
        )
      else
        (
          0ul
        )
    ) in
  let is_valid_will_start_index: bool = ptr_is_valid_will_start_index.(0ul) in
  let connect_will_struct: struct_connect_will = 
    (
      if (is_valid_will_start_index) then
        (
          get_connect_will_struct packet_data packet_size will_start_index will_flag
        )
      else
        (
          let empty_buffer: B.buffer U8.t = B.alloca 0uy 1ul in
          let connect_will_struct: struct_connect_will =
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
            } in connect_will_struct          
        )
    ) in
  let user_name_struct: struct_utf8_string = 
    get_user_name_struct packet_data packet_size connect_will_struct.user_name_or_password_next_start_index user_name_flag in
  let password_struct: struct_binary_data =
    get_password_struct packet_data packet_size user_name_struct.utf8_next_start_index password_flag in
  pop_frame ();

  let connect_packet_seed: struct_connect_packet_seed = {
    connect_seed_is_valid_protocol_name = protocol_name_struct.is_valid_protocol_name;
    connect_seed_is_valid_protocol_version = protocol_version_struct.is_valid_protocol_version;
    connect_seed_connect_flag = connect_flag_struct.connect_flag_value;
    connect_seed_is_valid_keep_alive = keep_alive_struct.is_valid_keep_alive;
    connect_seed_keep_alive = keep_alive_struct.keep_alive_value;
    connect_seed_is_valid_property_length = true;
    connect_seed_property = property_struct;
    connect_seed_connect_id = connect_id;
    connect_seed_will_struct = connect_will_struct;
    connect_seed_user_name_struct = user_name_struct;
    connect_seed_password_struct = password_struct;
  } in connect_packet_seed
#reset-options


val connect_packet_parse_result: (share_common_data: struct_share_common_data)
  -> Stack (r: struct_fixed_header)
    (requires fun h0 -> 
    logic_packet_data h0 share_common_data.common_packet_data share_common_data.common_packet_size /\
    U32.v share_common_data.common_next_start_index < (B.length share_common_data.common_packet_data - 6))
    (ensures fun h0 r h1 -> true)
let connect_packet_parse_result share_common_data =
  let connect_packet_seed: struct_connect_packet_seed = 
  connect_packet_parser share_common_data.common_packet_data share_common_data.common_packet_size  share_common_data.common_next_start_index in
  let connect_constant: struct_fixed_header_constant =
    get_struct_fixed_header_constant_except_publish share_common_data.common_message_type in
  let connect_flag: U8.t = connect_packet_seed.connect_seed_connect_flag in
  let user_name_flag: U8.t = slice_byte connect_flag 0uy 1uy in
  let password_flag: U8.t = slice_byte connect_flag 1uy 2uy in
  let will_retain_flag: U8.t = slice_byte connect_flag 2uy 3uy in
  let will_qos_flag: U8.t = slice_byte connect_flag 3uy 5uy in
  let will_flag: U8.t = slice_byte connect_flag 5uy 6uy in
  let clean_start_flag: U8.t = slice_byte connect_flag 6uy 7uy in
  let resreved_flag: U8.t = slice_byte connect_flag 7uy 8uy in
  let keep_alive: U16.t = connect_packet_seed.connect_seed_keep_alive in

  // TODO: エラー処理
  let have_error: bool =
    (not connect_packet_seed.connect_seed_is_valid_protocol_name) ||
    (not connect_packet_seed.connect_seed_is_valid_protocol_version) ||
    (not (U8.eq resreved_flag 0uy)) ||
    (not connect_packet_seed.connect_seed_is_valid_keep_alive) ||
    (not connect_packet_seed.connect_seed_is_valid_property_length) ||
    (U8.gt connect_packet_seed.connect_seed_property.property_type_struct.property_type_error.property_error_code 0uy) ||
    (U8.gt connect_packet_seed.connect_seed_connect_id.utf8_string_status_code 0uy)
     in
  if (have_error) then
    (
      let error_struct: struct_error_struct =
        (
          if (not connect_packet_seed.connect_seed_is_valid_protocol_name) then
            {
              code = define_error_protocol_name_invalid_code;
              message = define_error_protocol_name_invalid;
            }
          else if (not connect_packet_seed.connect_seed_is_valid_protocol_version) then
            {
              code = define_error_protocol_version_invalid_code;
              message = define_error_protocol_version_invalid;
            }
          else if (not (U8.eq resreved_flag 0uy)) then
            {
              code = define_error_connect_flag_invalid_code;
              message = define_error_connect_flag_invalid;
            }
          else if (not connect_packet_seed.connect_seed_is_valid_keep_alive) then
            {
              code = define_error_connect_invalid_keep_alive_code;
              message = define_error_connect_keep_alive_invalid;
            }
          else if (not connect_packet_seed.connect_seed_is_valid_property_length) then
            {
              code = define_error_property_length_invalid_code;
              message = define_error_property_length_invalid;
            }
          else if (U8.gt connect_packet_seed.connect_seed_property.property_type_struct.property_type_error.property_error_code 0uy) then
            {
              code = define_error_property_error_code;
              message = connect_packet_seed.connect_seed_property.property_type_struct.property_type_error.property_error_code_name;
            }
          else // if (U8.gt connect_packet_seed.connect_id.utf8_string_status_code 0uy)
            {
              code = define_error_connect_id_invalid_code;
              message = define_error_connect_id_invalid;
            }
        ) in error_struct_fixed_header error_struct
    )
  else
    (
      let connect_struct :struct_connect = 
        {
          protocol_name = !$"MQTT";
          protocol_version = 5uy;
          flags = {
            connect_flag = connect_flag;
            user_name = user_name_flag;
            password = password_flag;
            will_retain = will_retain_flag;
            will_qos = will_qos_flag;
            will_flag = will_flag;
            clean_start = clean_start_flag;
          };
          keep_alive = keep_alive;
          connect_id = connect_packet_seed.connect_seed_connect_id;
          will = connect_packet_seed.connect_seed_will_struct;
          user_name = connect_packet_seed.connect_seed_user_name_struct;
          password = connect_packet_seed.connect_seed_password_struct;
        } in

      let ed_fixed_header_parts:
        struct_connect_parts = {
          connect_remaining_length = share_common_data.common_remaining_length;
          connect_connect_constant = connect_constant;
          connect_struct = connect_struct;
          connect_property = connect_packet_seed.connect_seed_property;
      } in
      assemble_connect_struct ed_fixed_header_parts            
    )